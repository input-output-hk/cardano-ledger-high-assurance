section \<open> Ledger State Transition \<close>

theory Ledger
  imports UTxO Delegation
begin

text \<open> Ledger state \<close>

type_synonym l_state = "utxo_state \<times> d_p_state"

end
