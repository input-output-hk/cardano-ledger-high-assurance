section \<open> Rewards and the Epoch Boundary \<close>

theory Rewards
  imports UTxO Delegation Protocol_Parameters Ledger
begin

subsection \<open> Helper Functions and Accounting Fields \<close>

text \<open> Accounting Fields \<close>

type_synonym acnt = "coin \<times> coin"

subsection \<open> Stake Distribution Calculation \<close>

text \<open> Blocks made by stake pools \<close>

type_synonym blocks_made = "(key_hash, nat) fmap"

text \<open> Stake \<close>

type_synonym stake = "(key_hash, coin) fmap"

subsection \<open> Snapshot Transition \<close>

text \<open> Snapshots environment \<close>

type_synonym snapshot_env = "
  p_params \<times> \<comment> \<open>protocol parameters\<close>
  d_state \<times> \<comment> \<open>delegation state\<close>
  p_state \<comment> \<open>pool state\<close>"

text \<open> Snapshots \<close>

type_synonym snapshots = "
  (stake \<times> (key_hash, key_hash) fmap) \<times> \<comment> \<open>newest stake\<close>
  (stake \<times> (key_hash, key_hash) fmap) \<times> \<comment> \<open>middle stake\<close>
  (stake \<times> (key_hash, key_hash) fmap) \<times> \<comment> \<open>oldest stake\<close>
  (key_hash, pool_param) fmap \<times> \<comment> \<open>pool parameters\<close>
  coin \<comment> \<open>fee snapshot\<close>"

text \<open> Snapshots states \<close>

type_synonym snapshot_state = "
  snapshots \<times> \<comment> \<open>snapshots\<close>
  utxo_state \<comment> \<open>utxo state\<close>"

text \<open> Snapshot Inference Rule \<close>

text \<open>
  NOTE:
  \<^item> \<open>stake\<close>, \<open>delegations\<close> and \<open>oblg\<close> are not defined since they are not related to the
    "preservation of value" property.
\<close>
inductive snap_sts :: "snapshot_env \<Rightarrow> snapshot_state \<Rightarrow> epoch \<Rightarrow> snapshot_state \<Rightarrow> bool"
  (\<open>_ \<turnstile> _ \<rightarrow>\<^bsub>SNAP\<^esub>{_} _\<close> [51, 0, 51] 50)
  where
    snapshot: "
      (pp, dstate, pstate) \<turnstile>
        (
          (pstake\<^sub>m\<^sub>a\<^sub>r\<^sub>k, pstake\<^sub>s\<^sub>e\<^sub>t, pstake\<^sub>g\<^sub>o, pools_ss, fee_ss),
          (utxo, deps, fees, up)
        )
        \<rightarrow>\<^bsub>SNAP\<^esub>{e}
        (
          ((stake, delegations), pstake\<^sub>m\<^sub>a\<^sub>r\<^sub>k, pstake\<^sub>s\<^sub>e\<^sub>t, pools_params, fees + decayed),
          (utxo, oblg, fees + decayed, up)
        )"
      if "stake = undefined"
      and "delegations = undefined"
      and "oblg = undefined"
      and "decayed = deps - oblg"

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
          (stk_creds, rewards, i\<^sub>r\<^sub>w\<^sub>d),
          pstate
        )
         \<rightarrow>\<^bsub>POOLREAP\<^esub>{e}
        (
          (utxo, deps - (unclaimed + refunded), fees, ups),
          (treasury + unclaimed, reserves),
          (stk_creds, rewards \<union>\<^sub>+ refunds, i\<^sub>r\<^sub>w\<^sub>d),
          pstate
        )"
      if "reward_acnts' = undefined"
      and "refunds = fmdom' rewards \<lhd> reward_acnts'"
      and "m_refunds = fmdom' rewards \<lhd>/ reward_acnts'"
      and "refunded = (\<Sum>k \<in> fmdom' refunds. refunds $$! k)"
      and "unclaimed = (\<Sum>k \<in> fmdom' m_refunds. m_refunds $$! k)"

subsection \<open> Complete Epoch Boundary Transition \<close>

text \<open> Epoch States \<close>

type_synonym epoch_state = "acnt \<times> snapshots \<times> l_state \<times> p_params"

subsection \<open> Reward Distribution Calculation \<close>

text \<open> Calculation to reward all stake pools \<close>

fun reward :: "p_params \<Rightarrow> blocks_made \<Rightarrow> coin \<Rightarrow> addr_rwd set \<Rightarrow> (key_hash, pool_param) fmap \<Rightarrow>
  stake \<Rightarrow> (key_hash, key_hash) fmap \<Rightarrow> (addr_rwd, coin) fmap" where
  "reward pp blocks R addrs\<^sub>r\<^sub>e\<^sub>w pool_params stake delegs = undefined" \<comment> \<open>NOTE: Undefined for now\<close>

subsection \<open> Reward Update Calculation \<close>

text \<open> Reward Update \<close>

type_synonym reward_update = "coin \<times> coin \<times> (addr_rwd, coin) fmap \<times> coin \<times> (credential, coin) fmap"

text \<open> Calculation to create a reward update \<close>

fun create_r_upd :: "blocks_made \<Rightarrow> epoch_state \<Rightarrow> reward_update" where
  "create_r_upd b
    (
      (_, reserves),
      (_, _, (stake, delegs), pools_ss, fee_ss),
      (_, ((stk_creds, rewards, i\<^sub>r\<^sub>w\<^sub>d), _)),
      pp
    ) =
    (
      let
        unregistered = fmdom' stk_creds \<lhd>/ i\<^sub>r\<^sub>w\<^sub>d;
        registered = i\<^sub>r\<^sub>w\<^sub>d --\<^sub>f unregistered;
        rewards\<^sub>m\<^sub>i\<^sub>r = (\<Sum> k \<in> fmdom' registered. registered $$! k);
        reserves' = reserves - rewards\<^sub>m\<^sub>i\<^sub>r;
        blocks_made = (\<Sum> k \<in> fmdom' b. b $$! k);
        \<eta> = real blocks_made / (real slots_per_epoch * active_slot_coeff pp);
        \<Delta>r\<^sub>l = \<lfloor>min 1 \<eta> * rho pp * reserves'\<rfloor>;
        reward_pot = fee_ss + \<Delta>r\<^sub>l;
        \<Delta>t\<^sub>1 = \<lfloor>tau pp * reward_pot\<rfloor>;
        \<Delta>r = \<Delta>r\<^sub>l + rewards\<^sub>m\<^sub>i\<^sub>r;
        R = reward_pot - \<Delta>t\<^sub>1;
        rs = reward pp b R (fmdom' rewards) pools_ss stake delegs;
        \<Delta>t\<^sub>2 = R - (\<Sum> k \<in> fmdom' rs. rs $$! k)
      in
        (\<Delta>t\<^sub>1 + \<Delta>t\<^sub>2, -\<Delta>r, rs, -fee_ss, registered)
    )"

text \<open> Applying a reward update \<close>

fun apply_r_upd :: "reward_update \<Rightarrow> epoch_state \<Rightarrow> epoch_state" where
  "apply_r_upd
    (\<Delta>t, \<Delta>r, rs, \<Delta>f, rew\<^sub>m\<^sub>i\<^sub>r)
    (
      (treasury, reserves),
      ss,
      (
        (utxo, deps, fees, up),
        ((stk_creds, rewards, i\<^sub>r\<^sub>w\<^sub>d), pstate)
      ),
      ppm
    ) =
    (
      let
        rew'\<^sub>m\<^sub>i\<^sub>r = fmdom' stk_creds \<lhd> rew\<^sub>m\<^sub>i\<^sub>r;
        unregistered = fmdom' stk_creds \<lhd>/ rew\<^sub>m\<^sub>i\<^sub>r;
        non_distributed = (\<Sum>k \<in> fmdom' unregistered. unregistered $$! k);
        update\<^sub>r\<^sub>w\<^sub>d = fmap_of_list [(addr_rwd hk, val). (hk, val) \<leftarrow> sorted_list_of_fmap rew'\<^sub>m\<^sub>i\<^sub>r]
      in
        (
          (treasury + \<Delta>t, reserves + \<Delta>r + non_distributed),
          ss,
          (
            (utxo, deps, fees + \<Delta>f, up),
            ((stk_creds, (rewards \<union>\<^sub>+ rs) \<union>\<^sub>+ update\<^sub>r\<^sub>w\<^sub>d, {$$}), pstate)
          ),
          ppm
        )
    )"

end
