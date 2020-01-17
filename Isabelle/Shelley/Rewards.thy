section \<open> Rewards and the Epoch Boundary \<close>

theory Rewards
  imports UTxO Delegation Protocol_Parameters Ledger
begin

subsection \<open> Helper Functions and Accounting Fields \<close>

text \<open> Total possible refunds \<close>

fun obligation :: "p_params \<Rightarrow> stake_creds \<Rightarrow> stake_pools \<Rightarrow> slot \<Rightarrow> coin" where
  "obligation pp stk_creds stpools cslot = undefined" \<comment> \<open>NOTE: Undefined for now\<close>

text \<open> Accounting Fields \<close>

type_synonym acnt = "
  coin \<times> \<comment> \<open>treasury pot\<close>
  coin \<comment> \<open>reserve pot\<close>"

subsection \<open> Stake Distribution Calculation \<close>

text \<open> Blocks made by stake pools \<close>

type_synonym blocks_made = "(key_hash, nat) fmap"

text \<open> Stake \<close>

type_synonym stake = "(key_hash, coin) fmap"

text \<open> Stake Distribution Function \<close>

fun stake_distr :: "utxo \<Rightarrow> d_state \<Rightarrow> p_state \<Rightarrow> stake" where
  "stake_distr utxo dstate pstate = undefined" \<comment> \<open>NOTE: Undefined for now\<close>

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
  \<^item> \<open>delegations\<close> is not defined since it is not related to the "preservation of value" property.
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
          ((stake, delegations), pstake\<^sub>m\<^sub>a\<^sub>r\<^sub>k, pstake\<^sub>s\<^sub>e\<^sub>t, pool_params, fees + decayed),
          (utxo, oblg, fees + decayed, up)
        )"
      if "(stk_creds, _, _) = dstate"
      and "(stpools, pool_params, _) = pstate"
      and "stake = stake_distr utxo dstate pstate"
      and "delegations = undefined"
      and "slot = first_slot e"
      and "oblg = obligation pp stk_creds stpools slot"
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

subsection \<open> Protocol Parameters Update Transition \<close>

text \<open> New Proto Param environment \<close>

type_synonym new_p_param_env = "
  p_params option \<times> \<comment> \<open>new protocol parameters\<close>
  d_state \<times> \<comment> \<open>delegation state\<close>
  p_state \<comment> \<open>pool state\<close>"

text \<open> New Proto Param States \<close>

type_synonym new_p_param_state = "
  utxo_state \<times> \<comment> \<open>utxo state\<close>
  acnt \<times> \<comment> \<open>accounting\<close>
  p_params \<comment> \<open>current protocol parameters\<close>"

text \<open> New Proto Param Inference Rules \<close>

abbreviation newpp_oblgs where
  "newpp_oblgs pp\<^sub>n\<^sub>e\<^sub>w pp dstate pstate e reserves \<equiv>
    (
      let
        stk_creds = fst dstate;
        stpools = fst pstate;
        slot = first_slot e;
        oblg\<^sub>c\<^sub>u\<^sub>r = obligation pp stk_creds stpools slot;
        oblg\<^sub>n\<^sub>e\<^sub>w = obligation pp\<^sub>n\<^sub>e\<^sub>w stk_creds stpools slot
      in
        (oblg\<^sub>c\<^sub>u\<^sub>r, oblg\<^sub>n\<^sub>e\<^sub>w)
    )"

abbreviation newpp_accepted where
  "newpp_accepted pp\<^sub>n\<^sub>e\<^sub>w pp dstate pstate e reserves \<equiv>
    (
      let
        (_, _, i\<^sub>r\<^sub>w\<^sub>d) = dstate;
        (oblg\<^sub>c\<^sub>u\<^sub>r, oblg\<^sub>n\<^sub>e\<^sub>w) = newpp_oblgs pp\<^sub>n\<^sub>e\<^sub>w pp dstate pstate e reserves;
        diff = oblg\<^sub>c\<^sub>u\<^sub>r - oblg\<^sub>n\<^sub>e\<^sub>w
      in
        reserves + diff \<ge> (\<Sum> c \<in> fmdom' i\<^sub>r\<^sub>w\<^sub>d. i\<^sub>r\<^sub>w\<^sub>d $$! c) \<and>
        max_tx_size pp\<^sub>n\<^sub>e\<^sub>w + max_header_size pp\<^sub>n\<^sub>e\<^sub>w < max_block_size pp\<^sub>n\<^sub>e\<^sub>w
    )"

text \<open>
  NOTE:
  \<^item> For the sake of simplicity and readability, an extra rule is added.
\<close>
inductive newpp_sts :: "new_p_param_env \<Rightarrow> new_p_param_state \<Rightarrow> epoch \<Rightarrow> new_p_param_state \<Rightarrow> bool"
  (\<open>_ \<turnstile> _ \<rightarrow>\<^bsub>NEWPP\<^esub>{_} _\<close> [51, 0, 51] 50)
  where
    new_proto_param_accept: "
      (opp\<^sub>n\<^sub>e\<^sub>w, dstate, pstate) \<turnstile> (utxo_st, acnt, pp) \<rightarrow>\<^bsub>NEWPP\<^esub>{e} (utxo_st', acnt', pp\<^sub>n\<^sub>e\<^sub>w)"
      if "opp\<^sub>n\<^sub>e\<^sub>w = Some pp\<^sub>n\<^sub>e\<^sub>w"
      and "(treasury, reserves) = acnt"
      and "newpp_accepted pp\<^sub>n\<^sub>e\<^sub>w pp dstate pstate e reserves"
      and "(oblg\<^sub>c\<^sub>u\<^sub>r, oblg\<^sub>n\<^sub>e\<^sub>w) = newpp_oblgs pp\<^sub>n\<^sub>e\<^sub>w pp dstate pstate e reserves"
      and "diff = oblg\<^sub>c\<^sub>u\<^sub>r - oblg\<^sub>n\<^sub>e\<^sub>w"
      and "(utxo, deps, fees, (pup, aup, favs, avs)) = utxo_st"
      and "deps = oblg\<^sub>c\<^sub>u\<^sub>r"
      and "utxo_st' = (utxo, oblg\<^sub>n\<^sub>e\<^sub>w, fees, ({$$}, aup, favs, avs))"
      and "acnt' = (treasury, reserves + diff)"
  | new_proto_param_denied_1: "
      (opp\<^sub>n\<^sub>e\<^sub>w, dstate, pstate) \<turnstile> (utxo_st, acnt, pp) \<rightarrow>\<^bsub>NEWPP\<^esub>{e} (utxo_st', acnt, pp)"
      if "opp\<^sub>n\<^sub>e\<^sub>w = Some pp\<^sub>n\<^sub>e\<^sub>w"
      and "(treasury, reserves) = acnt"
      and "\<not> newpp_accepted pp\<^sub>n\<^sub>e\<^sub>w pp dstate pstate e reserves"
      and "(utxo, deps, fees, (pup, aup, favs, avs)) = utxo_st"
      and "utxo_st' = (utxo, deps, fees, ({$$}, aup, favs, avs))"
  | new_proto_param_denied_2: "
      (opp\<^sub>n\<^sub>e\<^sub>w, dstate, pstate) \<turnstile> (utxo_st, acnt, pp) \<rightarrow>\<^bsub>NEWPP\<^esub>{e} (utxo_st', acnt, pp)"
      if "opp\<^sub>n\<^sub>e\<^sub>w = None"
      and "(utxo, deps, fees, (pup, aup, favs, avs)) = utxo_st"
      and "utxo_st' = (utxo, deps, fees, ({$$}, aup, favs, avs))"

subsection \<open> Complete Epoch Boundary Transition \<close>

text \<open> Epoch States \<close>

type_synonym epoch_state = "acnt \<times> snapshots \<times> l_state \<times> p_params"

text \<open> Epoch Inference Rule \<close>

inductive epoch_sts :: "epoch_state \<Rightarrow> epoch \<Rightarrow> epoch_state \<Rightarrow> bool"
  (\<open>\<turnstile> _ \<rightarrow>\<^bsub>EPOCH\<^esub>{_} _\<close> [0, 51] 50)
  where
    epoch: "\<turnstile> (acnt, ss, ls, pp) \<rightarrow>\<^bsub>EPOCH\<^esub>{e} (acnt'', ss', ls', pp')"
      if "(utxo_st, (dstate, pstate)) = ls"
      and "pp \<turnstile> (utxo_st, acnt, dstate, pstate) \<rightarrow>\<^bsub>POOLREAP\<^esub>{e} (utxo_st', acnt', dstate', pstate')"
      and "(pp, dstate', pstate') \<turnstile> (ss, utxo_st') \<rightarrow>\<^bsub>SNAP\<^esub>{e} (ss', utxo_st'')"
      and "(_, _, _, (pup, _, _, _)) = utxo_st''"
      and "pp\<^sub>n\<^sub>e\<^sub>w = voted_value\<^sub>P\<^sub>P\<^sub>a\<^sub>r\<^sub>a\<^sub>m\<^sub>s pup"
      and "(pp\<^sub>n\<^sub>e\<^sub>w, dstate', pstate') \<turnstile> (utxo_st'', acnt', pp) \<rightarrow>\<^bsub>NEWPP\<^esub>{e} (utxo_st''', acnt'', pp')"
      and "ls' = (utxo_st''', (dstate', pstate'))"

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
