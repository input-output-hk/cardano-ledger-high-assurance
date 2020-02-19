section \<open> Ledger State Transition \<close>

theory Ledger
  imports UTxO Delegation
begin

subsubsection \<open>Ledger transition-system types\<close>

text \<open> Ledger environment \<close>

type_synonym l_env = "
  slot \<times> \<comment> \<open>current slot\<close>
  ix \<times> \<comment> \<open>transaction index\<close>
  p_params \<times> \<comment> \<open>protocol parameters\<close>
  coin \<comment> \<open>total reserves\<close>"

text \<open> Ledger state \<close>

type_synonym l_state = "utxo_state \<times> d_p_state"

text \<open> Ledger inference rule \<close>

text \<open>
  NOTE:
  \<^item> \<open>stkCreds\<close>, \<open>stpools\<close> and \<open>genDelegs\<close> are not included for now.
\<close>
inductive ledger_sts :: "l_env \<Rightarrow> l_state \<Rightarrow> tx \<Rightarrow> l_state \<Rightarrow> bool"
  (\<open>_ \<turnstile> _ \<rightarrow>\<^bsub>LEDGER\<^esub>{_} _\<close> [51, 0, 51] 50)
  where
    ledger: "
      (slot, tx_ix, pp, reserves) \<turnstile> (utxo_st, dpstate) \<rightarrow>\<^bsub>LEDGER\<^esub>{tx} (utxo_st', dpstate')"
      if "(slot, tx) \<turnstile> dpstate \<rightarrow>\<^bsub>DELEGS\<^esub>{txcerts tx} dpstate'"
      and "(slot, pp, undefined, undefined, undefined) \<turnstile> utxo_st \<rightarrow>\<^bsub>UTXOW\<^esub>{tx} utxo_st'"

text \<open> Ledger sequence rules \<close>

text \<open>
  NOTE:
  \<^item> No state updates are performed in \<open>seq_ledger_base\<close> since all updates in the spec are not
    related to the "preservation of value" property.
\<close>
inductive ledgers_sts :: "(slot \<times> p_params \<times> coin) \<Rightarrow> l_state \<Rightarrow> tx list \<Rightarrow> l_state \<Rightarrow> bool"
  (\<open>_ \<turnstile> _ \<rightarrow>\<^bsub>LEDGERS\<^esub>{_} _\<close> [51, 0, 51] 50)
  where
    seq_ledger_base: "
      (slot, pp, reserves) \<turnstile> ls \<rightarrow>\<^bsub>LEDGERS\<^esub>{[]} ls'"
      if "((utxo, deps, fees, us), (ds, ps)) = ls"
      and "us' = us"
      and "ds' = ds"
      and "ls' = ((utxo, deps, fees, us'), (ds', ps))"
  | seq_ledger_ind: "
      (slot, pp, reserves) \<turnstile> ls \<rightarrow>\<^bsub>LEDGERS\<^esub>{\<Gamma> @ [c]} ls''"
      if "(slot, pp, reserves) \<turnstile> ls \<rightarrow>\<^bsub>LEDGERS\<^esub>{\<Gamma>} ls'"
      and "(slot, length \<Gamma> - 1, pp, reserves) \<turnstile> ls' \<rightarrow>\<^bsub>LEDGER\<^esub>{c} ls''"

end
