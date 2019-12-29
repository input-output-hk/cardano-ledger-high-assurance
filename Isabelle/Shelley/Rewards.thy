section \<open> Rewards and the Epoch Boundary \<close>
theory Rewards
  imports UTxO Delegation Protocol_Parameters
begin

subsection \<open> Helper Functions and Accounting Fields \<close>

text \<open> Accounting Fields \<close>

type_synonym acnt = "coin \<times> coin"

subsection \<open> Pool Reaping Transition \<close>

text \<open> Pool Reap State \<close>

type_synonym pl_reap_state = "utxo_state \<times> acnt \<times> d_state \<times> p_state"

text \<open> Pool Reap Inference Rule \<close>

text \<open>
  NOTE:
  \<^item> \<open>reward_acnts'\<close> is undefined for now.
\<close>
inductive poolreap_sts :: "p_params \<Rightarrow> pl_reap_state \<Rightarrow> epoch \<Rightarrow> pl_reap_state \<Rightarrow> bool"
  (\<open>_ \<turnstile> _ \<rightarrow>\<^bsub>POOLREAP\<^esub>{_} _\<close> [51, 0, 51] 50)
  where
    pool_reap: "
      pp \<turnstile>
        (
          (utxo, deps, fees, ups),
          (treasury, reserves),
          rewards,
          pstate
        )
         \<rightarrow>\<^bsub>POOLREAP\<^esub>{e}
        (
          (utxo, deps - (unclaimed + refunded), fees, ups),
          (treasury + unclaimed, reserves),
          rewards \<union>\<^sub>+ refunds,
          pstate
        )"
      if "reward_acnts' = undefined"
      and "refunds = fmdom' rewards \<lhd> reward_acnts'"
      and "m_refunds = fmdom' rewards \<lhd>/ reward_acnts'"
      and "refunded = (\<Sum>k \<in> fmdom' refunds. refunds $$! k)"
      and "unclaimed = (\<Sum>k \<in> fmdom' m_refunds. m_refunds $$! k)"

end
