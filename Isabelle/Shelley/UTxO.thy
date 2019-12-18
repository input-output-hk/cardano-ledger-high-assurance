section \<open> UTxO \<close>

theory UTxO
  imports Transaction Finite_Map_Extras Protocol_Parameters Cryptography Update
begin

subsection \<open> Deposits and Refunds \<close>

text \<open> Total deposits for transaction \<close>

abbreviation deposits :: "p_params \<Rightarrow> stake_pools \<Rightarrow> d_cert list \<Rightarrow> coin" where
  "deposits \<equiv> undefined" \<comment> \<open>NOTE: Abstract for now\<close>

text \<open> Key refunds for a transaction \<close>

abbreviation key_refunds :: "p_params \<Rightarrow> stake_creds \<Rightarrow> tx \<Rightarrow> coin" where
  "key_refunds \<equiv> undefined" \<comment> \<open>NOTE: Abstract for now\<close>

text \<open> Decayed deposit portions \<close>

abbreviation decayed_tx :: "p_params \<Rightarrow> stake_creds \<Rightarrow> tx \<Rightarrow> coin" where
  "decayed_tx \<equiv> undefined" \<comment> \<open>NOTE: Abstract for now\<close>

subsection \<open> UTxO transitions \<close>

text \<open> UTxO \<close>

type_synonym utxo = "(tx_in, tx_out) fmap"

text \<open> Tx outputs as UTxO \<close>

abbreviation outs :: "tx \<Rightarrow> utxo" where
  "outs tx \<equiv> fmap_of_list [((txid tx, ix), txout). (ix, txout) \<leftarrow> sorted_list_of_fmap (txouts tx)]"

lemma dom_outs_is_txid:
  assumes "(i, ix) \<in> fmdom' (outs tx)"
  shows "i = txid tx"
proof -
  from assms have "(i, ix) \<in> fset (fmdom (
    fmap_of_list [((txid tx, ix), txout). (ix, txout) \<leftarrow> sorted_list_of_fmap (txouts tx)]))"
    by (simp add: fmdom'_alt_def)
  then have "(i, ix) \<in> fset (fset_of_list (
    map fst [((txid tx, ix), txout). (ix, txout) \<leftarrow> sorted_list_of_fmap (txouts tx)]))"
    by simp
  then have "(i, ix) \<in> fset (fset_of_list
    [(txid tx, ix). (ix, txout) \<leftarrow> sorted_list_of_fmap (txouts tx)])"
    by auto
  then have "(i, ix) \<in> set [(txid tx, ix). (ix, txout) \<leftarrow> sorted_list_of_fmap (txouts tx)]"
    by (simp add: fset_of_list.rep_eq)
  then show "i = txid tx"
    by auto
qed

lemma txins_outs_exc:
  assumes "txid tx \<notin> {tid | tid ix. (tid, ix) \<in> fmdom' utxo}"
  shows "fmdom' (txins tx \<lhd>/ utxo) \<inter> fmdom' (outs tx) = {}"
proof -
  from assms have "txid tx \<notin> {tid | tid ix. (tid, ix) \<in> fmdom' (txins tx \<lhd>/ utxo)}"
    by simp
  then have "\<And>txin. txin \<in> fmdom' (txins tx \<lhd>/ utxo) \<Longrightarrow> fst txin \<noteq> txid tx"
    by (smt mem_Collect_eq prod.collapse)
  moreover have "\<And>txin. txin \<in> fmdom' (outs tx) \<Longrightarrow> fst txin = txid tx"
    using dom_outs_is_txid by (metis prod.collapse)
  ultimately show ?thesis
    by blast
qed

text \<open> UTxO balance \<close>

abbreviation ubalance :: "utxo \<Rightarrow> coin" where
  "ubalance utxo \<equiv> (\<Sum>txin \<in> fmdom' utxo. snd (utxo $$! txin))"

text \<open> Withdrawal balance \<close>

abbreviation wbalance :: "wdrl \<Rightarrow> coin" where
  "wbalance ws \<equiv> (\<Sum>addr \<in> fmdom' ws. ws $$! addr)"

text \<open> Value consumed \<close>

abbreviation consumed :: "p_params \<Rightarrow> utxo \<Rightarrow> stake_creds \<Rightarrow> tx \<Rightarrow> coin" where
  "consumed pp utxo stk_creds tx \<equiv>
    ubalance (txins tx \<lhd> utxo) + wbalance (txwdrls tx) + key_refunds pp stk_creds tx"

text \<open> Value produced \<close>

abbreviation produced :: "p_params \<Rightarrow> stake_pools \<Rightarrow> tx \<Rightarrow> coin" where
  "produced pp stpools tx \<equiv> ubalance (outs tx) + txfee tx + deposits pp stpools (txcerts tx)"

subsubsection \<open> UTxO transition-system types \<close>

text \<open> UTxO environment \<close>

type_synonym utxo_env = "slot \<times> p_params \<times> stake_creds \<times> stake_pools \<times> (key_hash_g, key_hash) fmap"

text \<open> UTxO states \<close>

type_synonym utxo_state = "utxo \<times> coin \<times> coin \<times> update_state"

text \<open> UTxO inference rules \<close>

text \<open>
  NOTE:
  \<^item> The assumption that the Tx ID must not appear in utxo needs to be made explicit here (see
    first precondition).
\<close>
inductive utxo_sts :: "utxo_env \<Rightarrow> utxo_state \<Rightarrow> tx \<Rightarrow> utxo_state \<Rightarrow> bool"
  (\<open>_ \<turnstile> _ \<rightarrow>\<^bsub>UTXO\<^esub>{_} _\<close> [51, 0, 51] 50)
  where
    utxo_inductive: "
      (slot, pp, stk_creds, stpools, gen_delegs)
        \<turnstile> (utxo, deps, fees, ups)
          \<rightarrow>\<^bsub>UTXO\<^esub>{tx}
          (
            (txins tx \<lhd>/ utxo) ++\<^sub>f outs tx,
            deps + deposit_change,
            fees + txfee tx + decayed,
            ups'
          )"
      if "txid tx \<notin> {tid | tid ix. (tid, ix) \<in> fmdom' utxo}"
      and "txins tx \<noteq> {}"
      and "txins tx \<subseteq> fmdom' utxo"
      and "consumed pp utxo stk_creds tx = produced pp stpools tx"
      and "\<forall>(_, c) \<in> fmran' (txouts tx). c \<ge> 0"
      and "refunded = key_refunds pp stk_creds tx"
      and "decayed = decayed_tx pp stk_creds tx"
      and "deposit_change = deposits pp stpools (txcerts tx) - (refunded + decayed)"
      and "(slot, pp, gen_delegs) \<turnstile> ups \<rightarrow>\<^bsub>UP\<^esub>{txup tx} ups'"

end
