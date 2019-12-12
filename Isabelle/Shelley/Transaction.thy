section \<open> Transactions \<close>

theory Transaction
  imports Basic_Types Address Finite_Map_Extras Delegation Update
begin

text \<open> Genesis key hash \<close>

typedecl key_hash_g

text \<open> Transaction ID \<close>

typedecl tx_id

text \<open> Transaction input \<close>

type_synonym tx_in = "tx_id \<times> ix"

text \<open> Transaction output \<close>

type_synonym tx_out = "addr \<times> coin"

text \<open> Reward withdrawal \<close>

type_synonym wdrl = "(addr_rwd, coin) fmap"

text \<open> Update proposal \<close>

typedecl update \<comment> \<open>NOTE: Abstract for now\<close>

text \<open> Transaction body \<close>

type_synonym tx_body = "tx_in set \<times> (ix, tx_out) fmap \<times> d_cert list \<times> coin \<times> slot \<times> wdrl \<times> update"

text \<open> Transaction witness \<close>

typedecl tx_witness \<comment> \<open>NOTE: Abstract for now\<close>

text \<open> Transaction \<close>

type_synonym tx = "tx_body \<times> tx_witness"

text \<open> Accessor functions \<close>

\<comment> \<open>Transaction inputs\<close>

fun txins :: "tx \<Rightarrow> tx_in set" where
  "txins ((txis, _, _, _, _, _, _), _) = txis"

\<comment> \<open>Transaction outputs\<close>

fun txouts :: "tx \<Rightarrow> (ix, tx_out) fmap" where
  "txouts ((_, txos, _, _, _, _, _), _) = txos"

\<comment> \<open>Delegation certificates\<close>

fun txcerts :: "tx \<Rightarrow> d_cert list" where
  "txcerts ((_, _, dcs, _, _, _, _), _) = dcs"

\<comment> \<open>Transaction fee\<close>

fun txfee :: "tx \<Rightarrow> coin" where
  "txfee ((_, _, _, c, _, _, _), _) = c"

\<comment> \<open>Withdrawals\<close>

fun txwdrls :: "tx \<Rightarrow> wdrl" where
  "txwdrls ((_, _, _, _, _, wds, _), _) = wds"

text \<open> Abstract functions \<close>

consts txid :: "tx \<Rightarrow> tx_id"

end
