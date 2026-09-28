//! 启动时自动切换账号（WorkBuddy 桌面端 + VS Code CodeBuddy 插件）。
//!
//! 与 [`crate::modules::rotate`]（CodeBuddy CLI 自动轮换）的分工与差异：
//!
//! | 维度 | rotate.rs（CLI） | 本模块 |
//! | --- | --- | --- |
//! | 触发 | 启动后按间隔周期执行 | **仅启动后执行一次** |
//! | 作用端 | 只写 `~/.codebuddy-rotate/state.json` | WorkBuddy 认证文件 + VS Code 插件凭证 |
//! | 门控 | CLI 会话心跳新鲜则跳过 | **目标客户端进程在运行则跳过** |
//! | 选优 | 只按到期时间升序 | 多一条 `expiry_tolerance` 容差：到期相差 ≤ 容差视为「同时到期」，此时优先「即将到期积分更多」 |
//! | 冷却 | 进程内静态量（重启归零） | 持久化到 `auto_switch_state.json`（跨启动生效） |
//!
//! 两边**共用同一套口径常量**（改动需同步）：紧迫阈值 72 小时、到期差异阈值 24 小时、
//! 冷却 120 分钟；「即将到期」沿用 `credits.rs` 的 `EXPIRING_SOON_DAYS`（7 天窗口）。
//!
//! 上半部分是纯决策逻辑（可单测），下半部分是带副作用的一次性编排 `run_startup_switch_cycle`。

use std::sync::atomic::AtomicBool;

use serde_json::{json, Value};

use crate::modules::account;
use crate::modules::config::{
    add_auto_switch_log, auto_switch_last_switch_at, load_auto_switch_config,
    load_auto_switch_logs, load_auto_switch_state, now_ms, record_auto_switch,
    touch_auto_switch_run, try_consume_auto_switch_notify, RunFlagGuard,
};
use crate::modules::process::is_workbuddy_running;
use crate::modules::variant::WbVariant;
use crate::modules::{auth_file, credits, session, switch, vscode_ext, vscode_session};

/// 一天 / 一小时的毫秒数。
const DAY_MS: i64 = 24 * 3_600_000;
const HOUR_MS: i64 = 3_600_000;

/// 目标客户端正在运行时的固定跳过原因。
///
/// 日志与通知都认这一条，措辞改动只应发生在此处。
pub const CLIENT_RUNNING_REASON: &str = "客户端正在运行，跳过本次自动切换";

/// 单个账号的积分候选（从积分查询结果提取，不携带 token 明文）。
#[derive(Debug, Clone)]
pub struct Candidate {
    /// 账号库中的原始下标 —— 稳定 tie-break 的唯一依据。
    pub account_index: usize,
    pub account_id: String,
    pub display_name: String,
    pub variant: WbVariant,
    /// 剩余积分中最早到期时间（毫秒）；无剩余积分资源时为 None。
    pub soonest_expire_at: Option<i64>,
    /// 即将到期（7 天窗口内）的剩余积分，作为「同时到期」时的优先依据。
    pub expiring_soon_remaining: f64,
    pub total_remaining: f64,
    /// 查询成功、未过期、有剩余积分、token 可用且有到期时间 → 可被选为目标。
    pub valid: bool,
    /// 不可选的原因（`valid == false` 时给出，供日志解释）。
    pub invalid_reason: Option<String>,
}

/// 账号是否被标记为「需要重新登录」。
fn needs_relogin(account: &Value) -> bool {
    account.get("needs_relogin").and_then(Value::as_bool) == Some(true)
}

/// 从「账号 + 积分查询结果」提取候选。
///
/// 过滤比 `rotate.rs` 更严：本功能会**真的写认证文件**，选中失效账号会直接导致客户端登录失败，
/// 因此额外要求 `needs_relogin` 为假、`access_token` 非空、且有已知到期时间。
pub fn to_candidate(account: &Value, credit: &Value, account_index: usize) -> Candidate {
    let account_id = account
        .get("id")
        .and_then(Value::as_str)
        .unwrap_or("")
        .to_string();
    let display_name = account::account_display_name(account);
    let variant = account::variant_of(account);

    let ok = credit.get("ok").and_then(Value::as_bool) == Some(true);
    let expired = credit.get("expired").and_then(Value::as_bool) == Some(true);
    let total_remaining = credit
        .get("totalRemaining")
        .and_then(Value::as_f64)
        .unwrap_or(0.0);
    let expiring_soon_remaining = credit
        .get("expiringSoonRemaining")
        .and_then(Value::as_f64)
        .unwrap_or(0.0);
    let soonest_expire_at = credit.get("soonestExpireAt").and_then(Value::as_i64);

    let invalid_reason = if !ok {
        Some(
            credit
                .get("error")
                .and_then(Value::as_str)
                .unwrap_or("积分查询失败")
                .to_string(),
        )
    } else if expired {
        Some("积分已过期".to_string())
    } else if total_remaining <= 0.0 {
        Some("没有剩余积分".to_string())
    } else if needs_relogin(account) {
        Some("账号需要重新登录".to_string())
    } else if account::secret_value(account, "access_token").is_none() {
        Some("账号缺少 access_token".to_string())
    } else if soonest_expire_at.is_none() {
        Some("积分没有可用的到期时间".to_string())
    } else {
        None
    };

    Candidate {
        account_index,
        account_id,
        display_name,
        variant,
        soonest_expire_at,
        expiring_soon_remaining,
        total_remaining,
        valid: invalid_reason.is_none(),
        invalid_reason,
    }
}

/// 在候选中选出目标账号，返回其在 `candidates` 中的下标。
///
/// **为什么不用 `sort_by` 直接比较**：带容差的「到期时间相近即视为相同」不是严格弱序
/// （A≈B、B≈C 推不出 A≈C），直接排序结果不确定。改用两段式，天然良定义：
///
/// 1. 按 `(到期时间, 账号库下标)` **严格升序**排序 —— 基准到期时间 `best_ts` 唯一确定；
/// 2. 取满足 `到期时间 - best_ts <= tolerance_ms` 的**窗口**（闭区间）；
/// 3. 窗口内按 `(即将到期积分降序, 账号库下标升序)` 取最优。
///
/// 退化为「取最早到期」的两种情形：全部候选 `expiringSoonRemaining` 相等（含全为 0），
/// 或容差为 0 且无同到期账号。
pub fn pick_target(candidates: &[Candidate], tolerance_ms: i64) -> Option<usize> {
    let mut valid: Vec<usize> = candidates
        .iter()
        .enumerate()
        .filter(|(_, candidate)| candidate.valid && candidate.soonest_expire_at.is_some())
        .map(|(index, _)| index)
        .collect();
    if valid.is_empty() {
        return None;
    }

    valid.sort_by_key(|&index| {
        (
            candidates[index].soonest_expire_at.unwrap_or(i64::MAX),
            candidates[index].account_index,
        )
    });
    let best_ts = candidates[valid[0]].soonest_expire_at.unwrap_or(i64::MAX);

    valid
        .into_iter()
        .filter(|&index| {
            candidates[index].soonest_expire_at.unwrap_or(i64::MAX) - best_ts <= tolerance_ms
        })
        .min_by(|&left, &right| {
            // min_by 取「比较结果为 Less」者：即将到期积分多者更优，相等时账号库下标小者更优。
            candidates[right]
                .expiring_soon_remaining
                .total_cmp(&candidates[left].expiring_soon_remaining)
                .then(
                    candidates[left]
                        .account_index
                        .cmp(&candidates[right].account_index),
                )
        })
}

/// 决策阈值（从 `auto_switch_config.json` 读出，缺省值与 `rotate.rs` 保持一致）。
#[derive(Debug, Clone)]
pub struct Policy {
    /// 切换冷却：上次切换后多久内不再切。
    pub cooldown_ms: i64,
    /// 到期差异阈值：目标比当前早到期不足该值则不切（防抖动）。
    pub min_gap_ms: i64,
    /// 紧迫阈值：最紧迫的账号到期剩余超过该值则整体不切。
    pub min_urgency_ms: i64,
    /// 价值过滤：目标剩余积分低于该值则不切（0 表示关闭）。
    pub min_remaining: f64,
    /// 到期容差：相差不超过该值视为「同时到期」。
    pub tolerance_ms: i64,
}

impl Policy {
    /// 从配置对象构造；非数值或缺失一律回落默认值。
    pub fn from_config(cfg: &Value) -> Self {
        let read = |key: &str, default: f64| {
            cfg.get(key)
                .and_then(Value::as_f64)
                .filter(|value| value.is_finite() && *value >= 0.0)
                .unwrap_or(default)
        };
        Self {
            cooldown_ms: (read("cooldown_minutes", 120.0) * 60_000.0) as i64,
            min_gap_ms: (read("min_gap_hours", 24.0) * HOUR_MS as f64) as i64,
            min_urgency_ms: (read("min_urgency_hours", 72.0) * HOUR_MS as f64) as i64,
            min_remaining: read("min_remaining_credits", 0.0),
            tolerance_ms: (read("expiry_tolerance_minutes", 60.0) * 60_000.0) as i64,
        }
    }
}

/// 决策结果。
#[derive(Debug, PartialEq, Eq)]
pub enum Decision {
    /// 不切，附原因。
    Skip(String),
    /// 切到目标账号 id。
    Switch(String),
}

/// 决策（以当前系统时间为准）。
pub fn decide_startup_switch(
    candidates: &[Candidate],
    current_account_id: Option<&str>,
    last_switch_at_ms: Option<i64>,
    policy: &Policy,
    client_running: bool,
) -> Decision {
    decide_startup_switch_at(
        candidates,
        current_account_id,
        last_switch_at_ms,
        policy,
        client_running,
        now_ms(),
    )
}

/// 决策（时间由调用方注入，便于单测）。
///
/// 步骤顺序对齐 `rotate.rs::decide_target`：先判「该不该切」（紧迫度 → 是否已是目标 →
/// 冷却 → 门控 → 价值 → 防抖动），最后才给出目标。
pub fn decide_startup_switch_at(
    candidates: &[Candidate],
    current_account_id: Option<&str>,
    last_switch_at_ms: Option<i64>,
    policy: &Policy,
    client_running: bool,
    now: i64,
) -> Decision {
    let Some(target_index) = pick_target(candidates, policy.tolerance_ms) else {
        return Decision::Skip(
            "没有可用账号（查询失败/已过期/无剩余积分/需要重新登录）".to_string(),
        );
    };
    let target = &candidates[target_index];

    // 紧迫度：最紧迫的账号到期还早，整体无需切换。
    if let Some(target_ts) = target.soonest_expire_at {
        let remaining_ms = target_ts - now;
        if remaining_ms > policy.min_urgency_ms {
            return Decision::Skip(format!(
                "所有账号到期都还早（最紧迫的还剩 {} 天），无需切换",
                remaining_ms / DAY_MS
            ));
        }
    }
    // 已是目标账号。
    if current_account_id == Some(target.account_id.as_str()) {
        return Decision::Skip("当前账号已是最紧迫账号".to_string());
    }
    // 冷却期：注意用持久化的跨启动时间，而非进程内静态量。
    if let Some(last) = last_switch_at_ms {
        if last + policy.cooldown_ms > now {
            return Decision::Skip("处于切换冷却期".to_string());
        }
    }
    // 客户端门控：运行中一律不切，绝不关闭客户端、不打断进行中的会话。
    if client_running {
        return Decision::Skip(CLIENT_RUNNING_REASON.to_string());
    }
    // 价值过滤。
    if policy.min_remaining > 0.0 && target.total_remaining < policy.min_remaining {
        return Decision::Skip(format!(
            "目标账号剩余积分不足（{}，阈值 {}），不值得切换",
            target.total_remaining, policy.min_remaining
        ));
    }
    // 防抖动：目标比当前早到期，但差距不足阈值。
    if let Some(current) = candidates
        .iter()
        .find(|candidate| Some(candidate.account_id.as_str()) == current_account_id)
    {
        if let (Some(current_ts), Some(target_ts)) =
            (current.soonest_expire_at, target.soonest_expire_at)
        {
            if current_ts > 0
                && target_ts < current_ts
                && current_ts - target_ts < policy.min_gap_ms
            {
                return Decision::Skip(format!(
                    "目标到期仅早 {} 小时，未达切换阈值（{} 小时）",
                    (current_ts - target_ts) / HOUR_MS,
                    policy.min_gap_ms / HOUR_MS
                ));
            }
        }
    }
    Decision::Switch(target.account_id.clone())
}

// ---------------------------------------------------------------------------
// 一次性编排（带副作用；纯决策部分在上方）
// ---------------------------------------------------------------------------

static AUTO_SWITCH_RUNNING: AtomicBool = AtomicBool::new(false);

/// 通知标题（与 `rotate.rs` 同源，便于用户识别来源）。
const NOTIFY_TITLE: &str = "workbuddy-switch";

/// 客户端维度键：跨启动冷却按客户端（WorkBuddy 再按档位）独立计算。
fn workbuddy_state_key(variant: WbVariant) -> String {
    format!("workbuddy:{}", variant.as_str())
}

/// VS Code 插件无档位概念，单一维度。
const VSCODE_STATE_KEY: &str = "vscodeExt";

/// 由 uid 反查账号库里的账号 id（`find_account` 同时支持按 id 或 uid 查找）。
fn account_id_for_uid(uid: &str) -> Option<String> {
    account::find_account(uid).and_then(|acc| {
        acc.get("id")
            .and_then(Value::as_str)
            .map(|id| id.to_string())
    })
}

/// 单个客户端维度的执行结果。
#[derive(Debug, Clone)]
struct ClientOutcome {
    /// switched / skipped / error / inactive
    action: &'static str,
    reason: Option<String>,
    from: Option<String>,
    to: Option<String>,
    copy: Option<Value>,
    /// 仅 switched 时给出，用于写跨启动冷却。
    state_key: Option<String>,
}

impl ClientOutcome {
    fn skipped(reason: impl Into<String>) -> Self {
        Self {
            action: "skipped",
            reason: Some(reason.into()),
            from: None,
            to: None,
            copy: None,
            state_key: None,
        }
    }

    /// 「该端根本没启用」：没有登录态，不是失败也不是被跳过。
    fn inactive(reason: impl Into<String>) -> Self {
        Self {
            action: "inactive",
            reason: Some(reason.into()),
            from: None,
            to: None,
            copy: None,
            state_key: None,
        }
    }

    fn error(reason: impl Into<String>) -> Self {
        Self {
            action: "error",
            reason: Some(reason.into()),
            from: None,
            to: None,
            copy: None,
            state_key: None,
        }
    }

    fn switched(state_key: String, to: String, copy: Option<Value>) -> Self {
        Self {
            action: "switched",
            reason: None,
            from: None,
            to: Some(to),
            copy,
            state_key: Some(state_key),
        }
    }

    fn to_json(&self) -> Value {
        let mut value = json!({ "action": self.action });
        if let Some(reason) = &self.reason {
            value["reason"] = json!(reason);
        }
        if let Some(from) = &self.from {
            value["from"] = json!(from);
        }
        if let Some(to) = &self.to {
            value["to"] = json!(to);
        }
        if let Some(copy) = &self.copy {
            value["sessionCopy"] = copy.clone();
        }
        value
    }
}

/// WorkBuddy 分支：只在「已有登录态」的档位内选账号；目标档位的客户端在运行则跳过。
async fn run_workbuddy_branch(
    candidates: &[Candidate],
    policy: &Policy,
    state: &Value,
    now: i64,
    copy_sessions: bool,
) -> ClientOutcome {
    let active: Vec<WbVariant> = WbVariant::ALL
        .into_iter()
        .filter(|variant| auth_file::read_auth_file(*variant).is_some())
        .collect();
    if active.is_empty() {
        return ClientOutcome::inactive("未检测到已登录的 WorkBuddy 档位");
    }
    let scoped: Vec<Candidate> = candidates
        .iter()
        .filter(|candidate| active.contains(&candidate.variant))
        .cloned()
        .collect();

    // 先选一次目标只为确定档位：「当前账号」与「进程门控」都依赖它。
    // `pick_target` 是纯函数，两次调用结果必然一致。
    let Some(index) = pick_target(&scoped, policy.tolerance_ms) else {
        return ClientOutcome::skipped("没有可用账号（查询失败/已过期/无剩余积分/需要重新登录）");
    };
    let variant = scoped[index].variant;
    let state_key = workbuddy_state_key(variant);
    let current_uid = session::current_user_uid(variant);
    let current_id = current_uid.as_deref().and_then(account_id_for_uid);
    let last_switch = auto_switch_last_switch_at(state, &state_key);
    let running = is_workbuddy_running(variant);

    let mut outcome = match decide_startup_switch_at(
        &scoped,
        current_id.as_deref(),
        last_switch,
        policy,
        running,
        now,
    ) {
        Decision::Skip(reason) => ClientOutcome::skipped(reason),
        Decision::Switch(target_id) => {
            match switch_workbuddy_silently(
                &target_id,
                variant,
                current_uid.as_deref(),
                copy_sessions,
            )
            .await
            {
                Ok(copy) => ClientOutcome::switched(state_key, target_id, copy),
                Err(error) => ClientOutcome::error(error),
            }
        }
    };
    outcome.from = current_id;
    outcome
}

/// 静默写入 WorkBuddy 认证（可选带上当前账号的全部会话），**不关闭也不启动**客户端。
async fn switch_workbuddy_silently(
    target_id: &str,
    variant: WbVariant,
    source_uid: Option<&str>,
    copy_sessions: bool,
) -> Result<Option<Value>, String> {
    let copy_ids: Vec<String> = if copy_sessions {
        source_uid
            .map(|uid| {
                session::list_sessions_for_user(variant, uid)
                    .as_array()
                    .map(|sessions| {
                        sessions
                            .iter()
                            .filter_map(|item| item.get("id").and_then(Value::as_str))
                            .map(|id| id.to_string())
                            .collect()
                    })
                    .unwrap_or_default()
            })
            .unwrap_or_default()
    } else {
        Vec::new()
    };

    let account_id = target_id.to_string();
    let result = tokio::task::spawn_blocking(move || {
        switch::switch_account(
            None,
            &account_id,
            switch::SwitchMode::SilentWriteWithoutLaunch,
            false,
            &copy_ids,
            &[],
        )
    })
    .await
    .map_err(|error| error.to_string())?;

    result.map(|value| value.get("sessionCopy").cloned())
}

/// VS Code 插件分支：无档位概念，候选为全部有效账号；编辑器在运行则跳过。
async fn run_vscode_branch(
    candidates: &[Candidate],
    policy: &Policy,
    state: &Value,
    now: i64,
    copy_sessions: bool,
) -> ClientOutcome {
    let Some(source_uid) = vscode_ext::active_ext_uid() else {
        return ClientOutcome::inactive("未检测到 VS Code CodeBuddy 插件登录账号");
    };
    let current_id = account_id_for_uid(&source_uid);
    let last_switch = auto_switch_last_switch_at(state, VSCODE_STATE_KEY);
    let running = vscode_ext::is_vscode_running();

    let mut outcome = match decide_startup_switch_at(
        candidates,
        current_id.as_deref(),
        last_switch,
        policy,
        running,
        now,
    ) {
        Decision::Skip(reason) => ClientOutcome::skipped(reason),
        Decision::Switch(target_id) => {
            match switch_vscode_silently(&target_id, &source_uid, copy_sessions).await {
                Ok(copy) => ClientOutcome::switched(VSCODE_STATE_KEY.to_string(), target_id, copy),
                Err(error) => ClientOutcome::error(error),
            }
        }
    };
    outcome.from = current_id;
    outcome
}

/// 静默注入 VS Code 插件凭证（可选带上当前账号的全部会话），**不启动编辑器**。
async fn switch_vscode_silently(
    target_id: &str,
    source_uid: &str,
    copy_sessions: bool,
) -> Result<Option<Value>, String> {
    let items: Vec<vscode_session::CopyItem> = if copy_sessions {
        build_vscode_copy_items(source_uid)
    } else {
        Vec::new()
    };

    let account_id = target_id.to_string();
    let result = tokio::task::spawn_blocking(move || {
        vscode_session::switch_vscode_ext_with_copy(&account_id, false, &items, &[])
    })
    .await
    .map_err(|error| error.to_string())?;

    result.map(|value| value.get("sessionCopy").cloned())
}

/// 把当前账号的全部 VS Code 会话转成复制项。
///
/// 与前端切换弹窗口径一致：不做 `hasHistory` 过滤，只要求 `workspaceHash` 与 `id` 齐全。
fn build_vscode_copy_items(source_uid: &str) -> Vec<vscode_session::CopyItem> {
    vscode_session::list_vscode_sessions(source_uid)
        .get("sessions")
        .and_then(Value::as_array)
        .map(|sessions| {
            sessions
                .iter()
                .filter_map(|session| {
                    let workspace_hash = session.get("workspaceHash").and_then(Value::as_str)?;
                    let conversation_id = session.get("id").and_then(Value::as_str)?;
                    Some(vscode_session::CopyItem {
                        workspace_hash: workspace_hash.to_string(),
                        conversation_id: conversation_id.to_string(),
                    })
                })
                .collect()
        })
        .unwrap_or_default()
}

/// 启动自动切换的**一次性**编排（应用启动后只调用一次，不做周期循环）。
///
/// 返回结构化结果，供宿主写日志、投递通知与回传前端。整体不做重试：本次不满足条件
/// 就等下次启动，避免在用户开机瞬间反复读写客户端数据。
pub async fn run_startup_switch_cycle() -> Value {
    let Some(_guard) = RunFlagGuard::try_acquire(&AUTO_SWITCH_RUNNING) else {
        return json!({ "status": "skipped", "reason": "already_running" });
    };

    let cfg = load_auto_switch_config();
    if cfg.get("enabled").and_then(Value::as_bool) != Some(true) {
        return json!({ "status": "disabled" });
    }
    let policy = Policy::from_config(&cfg);
    let copy_sessions = cfg
        .get("copy_sessions")
        .and_then(Value::as_bool)
        .unwrap_or(true);
    let notify_on_skip = cfg
        .get("notify_on_skip")
        .and_then(Value::as_bool)
        .unwrap_or(true);
    let now = now_ms();

    // 串行查询全部账号积分：与 rotate.rs 同一策略，不为并发引入新依赖。
    let accounts = account::load_accounts();
    let mut candidates: Vec<Candidate> = Vec::with_capacity(accounts.len());
    for (index, account) in accounts.iter().enumerate() {
        let credit = credits::get_credit_expiry(account).await;
        candidates.push(to_candidate(account, &credit, index));
    }

    let state = load_auto_switch_state();
    let workbuddy = run_workbuddy_branch(&candidates, &policy, &state, now, copy_sessions).await;
    let vscode = run_vscode_branch(&candidates, &policy, &state, now, copy_sessions).await;
    let clients = [("workbuddy", &workbuddy), ("vscodeExt", &vscode)];

    // 跨启动冷却：按客户端维度分别记录；一个都没切就只刷新 lastRunAt。
    let switched_keys: Vec<&str> = clients
        .iter()
        .filter_map(|(_, outcome)| outcome.state_key.as_deref())
        .collect();
    if switched_keys.is_empty() {
        touch_auto_switch_run(now);
    } else {
        record_auto_switch(now, &switched_keys);
    }

    let any_error = clients.iter().any(|(_, outcome)| outcome.action == "error");
    let status = if any_error {
        "error"
    } else if switched_keys.is_empty() {
        "skipped"
    } else {
        "switched"
    };

    // 因客户端在运行而跳过 → 值得提示一次（受开关与每日预算约束）。
    let blocked_by_running = clients.iter().any(|(_, outcome)| {
        outcome.action == "skipped" && outcome.reason.as_deref() == Some(CLIENT_RUNNING_REASON)
    });
    let notify = (notify_on_skip && blocked_by_running && try_consume_auto_switch_notify(now))
        .then(|| {
            json!({
                "title": NOTIFY_TITLE,
                "body": "检测到客户端正在运行，本次启动的自动切换已跳过；关闭客户端后重启本应用即可生效",
            })
        });

    let detail: Vec<Value> = candidates
        .iter()
        .map(|candidate| {
            json!({
                "name": candidate.display_name,
                "variant": candidate.variant.as_str(),
                "remaining": candidate.total_remaining,
                "expiringSoonRemaining": candidate.expiring_soon_remaining,
                "soonestExpireAt": candidate.soonest_expire_at,
                "valid": candidate.valid,
                "invalidReason": candidate.invalid_reason,
            })
        })
        .collect();

    let clients_json = json!({
        "workbuddy": workbuddy.to_json(),
        "vscodeExt": vscode.to_json(),
    });
    let mut log = json!({
        "ts": now,
        "action": status,
        "clients": clients_json,
        "detail": detail,
    });
    if let Some(notify) = &notify {
        log["notify"] = notify.clone();
    }
    add_auto_switch_log(&log);

    let mut payload = json!({ "status": status, "clients": clients_json });
    if let Some(notify) = notify {
        payload["notify"] = notify;
    }
    payload
}

/// 启动自动切换状态：配置 + 运行态（上次运行/各端上次切换时间）+ 最近一条日志。
///
/// 供设置页展示，不触发任何 IO 写入。
pub fn auto_switch_status() -> Value {
    let logs = load_auto_switch_logs();
    json!({
        "config": load_auto_switch_config(),
        "state": load_auto_switch_state(),
        "lastLog": logs.last().cloned().unwrap_or(Value::Null),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    /// 基准时间：固定值，保证用例不依赖真实时钟。
    const NOW: i64 = 1_800_000_000_000;

    fn hours(count: i64) -> i64 {
        count * HOUR_MS
    }

    fn candidate_at(
        index: usize,
        id: &str,
        expire_offset_hours: i64,
        expiring_soon: f64,
    ) -> Candidate {
        Candidate {
            account_index: index,
            account_id: id.to_string(),
            display_name: id.to_string(),
            variant: WbVariant::Cn,
            soonest_expire_at: Some(NOW + hours(expire_offset_hours)),
            expiring_soon_remaining: expiring_soon,
            total_remaining: 1000.0,
            valid: true,
            invalid_reason: None,
        }
    }

    fn default_policy() -> Policy {
        Policy::from_config(&Value::Null)
    }

    #[test]
    fn tolerance_window_prefers_more_expiring_soon() {
        // A 到期早 30 分钟但即将到期积分为 0；B 晚 30 分钟但即将到期 500。
        // 两者相差在 1 小时容差内 → 选 B。
        let candidates = vec![
            candidate_at(0, "A", 10, 0.0),
            candidate_at(1, "B", 10, 500.0),
        ];
        assert_eq!(pick_target(&candidates, hours(1)), Some(1));
    }

    #[test]
    fn tolerance_boundary_exactly_one_hour() {
        let mut later = candidate_at(1, "B", 11, 500.0);
        // 恰好相差 1 小时 → 入窗，选积分多的 B。
        let candidates = vec![candidate_at(0, "A", 10, 0.0), later.clone()];
        assert_eq!(pick_target(&candidates, hours(1)), Some(1));

        // 多 1 毫秒 → 出窗，选到期更早的 A。
        later.soonest_expire_at = Some(NOW + hours(11) + 1);
        let candidates = vec![candidate_at(0, "A", 10, 0.0), later];
        assert_eq!(pick_target(&candidates, hours(1)), Some(0));
    }

    #[test]
    fn equal_expiry_and_equal_credits_falls_back_to_account_order() {
        let candidates = vec![
            candidate_at(7, "later-in-library", 10, 300.0),
            candidate_at(2, "earlier-in-library", 10, 300.0),
        ];
        // 两项完全等价 → 账号库下标小者优先（与输入顺序无关）。
        assert_eq!(pick_target(&candidates, hours(1)), Some(1));
    }

    #[test]
    fn pick_target_is_deterministic_on_unsorted_input() {
        let base = vec![
            candidate_at(0, "A", 30, 0.0),
            candidate_at(1, "B", 10, 500.0),
            candidate_at(2, "C", 10, 900.0),
            candidate_at(3, "D", 50, 100.0),
        ];
        let mut shuffled = base.clone();
        shuffled.reverse();
        let first = pick_target(&base, hours(1)).map(|i| base[i].account_id.clone());
        let second = pick_target(&shuffled, hours(1)).map(|i| shuffled[i].account_id.clone());
        assert_eq!(first, Some("C".to_string()));
        assert_eq!(first, second);
    }

    #[test]
    fn invalid_and_missing_expiry_candidates_are_excluded() {
        let mut broken = candidate_at(0, "broken", 5, 9999.0);
        broken.valid = false;
        broken.invalid_reason = Some("积分查询失败".to_string());
        let mut no_expiry = candidate_at(1, "no-expiry", 5, 9999.0);
        no_expiry.soonest_expire_at = None;

        let candidates = vec![broken, no_expiry, candidate_at(2, "ok", 40, 0.0)];
        // 前两个不可选（一个 invalid、一个无到期时间），只能落到第三个。
        assert_eq!(pick_target(&candidates, hours(1)), Some(2));
    }

    #[test]
    fn to_candidate_rejects_expired_relogin_and_empty_token() {
        let credit_ok = json!({
            "ok": true,
            "expired": false,
            "totalRemaining": 100.0,
            "expiringSoonRemaining": 10.0,
            "soonestExpireAt": NOW + hours(10),
        });
        let healthy = json!({ "id": "a", "uid": "u1", "access_token": "t" });
        assert!(to_candidate(&healthy, &credit_ok, 0).valid);

        let needs_relogin =
            json!({ "id": "b", "uid": "u2", "access_token": "t", "needs_relogin": true });
        let candidate = to_candidate(&needs_relogin, &credit_ok, 0);
        assert!(!candidate.valid);
        assert_eq!(
            candidate.invalid_reason.as_deref(),
            Some("账号需要重新登录")
        );

        let empty_token = json!({ "id": "c", "uid": "u3", "access_token": "   " });
        let candidate = to_candidate(&empty_token, &credit_ok, 0);
        assert!(!candidate.valid);
        assert_eq!(
            candidate.invalid_reason.as_deref(),
            Some("账号缺少 access_token")
        );

        // 加密信封形态的 token 视为「有值」（本机可由客户端自行解密）。
        let envelope = json!({ "id": "d", "uid": "u4", "access_token": { "$wbEncrypted": "x" } });
        assert!(to_candidate(&envelope, &credit_ok, 0).valid);

        let expired_credit = json!({ "ok": true, "expired": true, "totalRemaining": 10.0 });
        let candidate = to_candidate(&healthy, &expired_credit, 0);
        assert!(!candidate.valid);
        assert_eq!(candidate.invalid_reason.as_deref(), Some("积分已过期"));

        let failed_credit = json!({ "ok": false, "error": "登录状态已失效" });
        let candidate = to_candidate(&healthy, &failed_credit, 0);
        assert!(!candidate.valid);
        assert_eq!(candidate.invalid_reason.as_deref(), Some("登录状态已失效"));
    }

    #[test]
    fn urgency_threshold_skips_when_all_expiries_are_far_away() {
        let policy = default_policy();
        // 最紧迫的也还有 100 小时，超过 72 小时阈值。
        let candidates = vec![candidate_at(0, "A", 100, 500.0)];
        assert!(matches!(
            decide_startup_switch_at(&candidates, Some("B"), None, &policy, false, NOW),
            Decision::Skip(_)
        ));
        // 收紧到 10 小时则进入切换。
        assert_eq!(
            decide_startup_switch_at(
                &[candidate_at(0, "A", 10, 500.0)],
                Some("B"),
                None,
                &policy,
                false,
                NOW
            ),
            Decision::Switch("A".to_string())
        );
    }

    #[test]
    fn cooldown_blocks_within_window_and_allows_after() {
        let policy = default_policy();
        let candidates = vec![candidate_at(0, "A", 10, 500.0)];

        // 60 分钟前切过，冷却 120 分钟 → 仍在冷却期内。
        assert_eq!(
            decide_startup_switch_at(
                &candidates,
                Some("B"),
                Some(NOW - 60 * 60_000),
                &policy,
                false,
                NOW
            ),
            Decision::Skip("处于切换冷却期".to_string())
        );
        // 130 分钟前切过 → 冷却结束。
        assert_eq!(
            decide_startup_switch_at(
                &candidates,
                Some("B"),
                Some(NOW - 130 * 60_000),
                &policy,
                false,
                NOW
            ),
            Decision::Switch("A".to_string())
        );
    }

    #[test]
    fn first_run_without_state_has_no_cooldown() {
        let policy = default_policy();
        let candidates = vec![candidate_at(0, "A", 10, 500.0)];
        assert_eq!(
            decide_startup_switch_at(&candidates, Some("B"), None, &policy, false, NOW),
            Decision::Switch("A".to_string())
        );
    }

    #[test]
    fn current_account_short_circuits() {
        let policy = default_policy();
        let candidates = vec![candidate_at(0, "A", 10, 500.0)];
        assert_eq!(
            decide_startup_switch_at(&candidates, Some("A"), None, &policy, false, NOW),
            Decision::Skip("当前账号已是最紧迫账号".to_string())
        );
    }

    #[test]
    fn client_running_gate_reason_is_fixed() {
        let policy = default_policy();
        let candidates = vec![candidate_at(0, "A", 10, 500.0)];
        assert_eq!(
            decide_startup_switch_at(&candidates, Some("B"), None, &policy, true, NOW),
            Decision::Skip(CLIENT_RUNNING_REASON.to_string())
        );
    }

    #[test]
    fn min_gap_threshold_prevents_near_tie_switch() {
        let policy = default_policy();
        // 当前账号 36 小时后到期，目标 30 小时后到期：只早 6 小时 < 24 小时阈值 → 不切。
        let candidates = vec![
            candidate_at(0, "target", 30, 500.0),
            candidate_at(1, "current", 36, 0.0),
        ];
        assert!(matches!(
            decide_startup_switch_at(&candidates, Some("current"), None, &policy, false, NOW),
            Decision::Skip(reason) if reason.contains("未达切换阈值")
        ));
        // 目标早 48 小时 → 达到阈值。
        let candidates = vec![
            candidate_at(0, "target", 20, 500.0),
            candidate_at(1, "current", 68, 0.0),
        ];
        assert_eq!(
            decide_startup_switch_at(&candidates, Some("current"), None, &policy, false, NOW),
            Decision::Switch("target".to_string())
        );
    }

    #[test]
    fn min_remaining_value_filter_blocks_low_value_target() {
        let mut policy = default_policy();
        policy.min_remaining = 5000.0;
        let candidates = vec![candidate_at(0, "A", 10, 500.0)];
        assert!(matches!(
            decide_startup_switch_at(&candidates, Some("B"), None, &policy, false, NOW),
            Decision::Skip(reason) if reason.contains("剩余积分不足")
        ));
    }

    #[test]
    fn no_valid_candidates_skips_with_reason() {
        let policy = default_policy();
        let mut invalid = candidate_at(0, "A", 10, 500.0);
        invalid.valid = false;
        assert!(matches!(
            decide_startup_switch_at(&[invalid], Some("B"), None, &policy, false, NOW),
            Decision::Skip(reason) if reason.contains("没有可用账号")
        ));
    }

    #[test]
    fn policy_defaults_match_rotate_baseline() {
        let policy = Policy::from_config(&Value::Null);
        assert_eq!(policy.cooldown_ms, 120 * 60_000);
        assert_eq!(policy.min_gap_ms, 24 * HOUR_MS);
        assert_eq!(policy.min_urgency_ms, 72 * HOUR_MS);
        assert_eq!(policy.tolerance_ms, 60 * 60_000);
        assert_eq!(policy.min_remaining, 0.0);
    }

    #[test]
    fn policy_reads_overrides_from_config() {
        let policy = Policy::from_config(&json!({
            "cooldown_minutes": 30,
            "min_gap_hours": 48,
            "min_urgency_hours": 24,
            "min_remaining_credits": 250,
            "expiry_tolerance_minutes": 15,
        }));
        assert_eq!(policy.cooldown_ms, 30 * 60_000);
        assert_eq!(policy.min_gap_ms, 48 * HOUR_MS);
        assert_eq!(policy.min_urgency_ms, 24 * HOUR_MS);
        assert_eq!(policy.tolerance_ms, 15 * 60_000);
        assert_eq!(policy.min_remaining, 250.0);
    }
}
