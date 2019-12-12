section \<open> UTxO \<close>

theory UTxO
  imports Transaction Finite_Map_Extras Protocol_Parameters Cryptography
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

(* NOTE: `ups'` is not defined for now since it involves another transition system. *)
inductive utxo_sts :: "utxo_env \<Rightarrow> utxo_state \<Rightarrow> tx \<Rightarrow> utxo_state \<Rightarrow> bool"
  (\<open>_ \<turnstile> _ \<rightarrow>\<^bsub>UTXO\<^esub>{_} _\<close> [51, 0, 51] 50)
  where
    utxo_inductive: "
      \<lbrakk>
        \<Gamma> = (slot, pp, stk_creds, stpools, gen_delegs);
        s = (utxo, deps, fees, ups);
        txins tx \<noteq> {};
        txins tx \<subseteq> fmdom' utxo;
        consumed pp utxo stk_creds tx = produced pp stpools tx;
        \<forall>(_, c) \<in> fmran' (txouts tx). c \<ge> 0;
        refunded = key_refunds pp stk_creds tx;
        decayed = decayed_tx pp stk_creds tx;
        deposit_change = deposits pp stpools (txcerts tx) - (refunded + decayed);
        ups' = ups; \<comment> \<open>FIXME: Complete later\<close>
        finite (fmdom' utxo)
      \<rbrakk>
      \<Longrightarrow>
      \<Gamma> \<turnstile> s \<rightarrow>\<^bsub>UTXO\<^esub>{tx} (
        (txins tx \<lhd>/ utxo) ++\<^sub>f outs tx, deps + deposit_change, fees + txfee tx + decayed, ups')"

subsection \<open> Properties \<close>

subsubsection \<open> Preservation of Value \<close>

text \<open> Lovelace Value \<close>

abbreviation val_coin :: "coin \<Rightarrow> coin" where
  "val_coin c \<equiv> c"

abbreviation val_map :: "('a, coin) fmap \<Rightarrow> coin" where
  "val_map m \<equiv> (\<Sum>k \<in> fmdom' m. m $$! k)"

fun val_utxo_state :: "utxo_state \<Rightarrow> coin" where
  "val_utxo_state (utxo, deps, fees, ups) = ubalance utxo + deps + fees"

lemma val_map_split:
  assumes "s \<subseteq> fmdom' m"
  shows "val_map m = val_map (s \<lhd>/ m) + val_map (s \<lhd> m)"
  oops

lemma val_map_union:
  assumes "fmdom' m\<^sub>1 \<inter> fmdom' m\<^sub>2 = {}"
  shows "val_map (m\<^sub>1 ++\<^sub>f m\<^sub>2) = val_map m\<^sub>1 + val_map m\<^sub>2"
  oops

lemma utxo_value_preservation:
  assumes "\<Gamma> \<turnstile> s \<rightarrow>\<^bsub>UTXO\<^esub>{t} s'"
  shows "val_utxo_state s + wbalance (txwdrls t) = val_utxo_state s'"
  oops

end
