section \<open> Protocol Parameters \<close>

theory Protocol_Parameters
  imports "HOL.Complex" Finite_Map_Extras Basic_Types
begin

text \<open> Protocol parameter name \<close>

typedecl ppm \<comment> \<open>NOTE: Abstract for now\<close>

text \<open> Duration difference between slots \<close>

type_synonym duration = nat

text \<open> Protocol parameter value \<close>

typedecl pvalue \<comment> \<open>NOTE: Abstract for now\<close>

text \<open> Protocol parameter map \<close>

type_synonym p_params = "(ppm, pvalue) fmap"

text \<open> Accessor Functions \<close>

consts max_block_size :: "p_params \<Rightarrow> nat" \<comment> \<open>max block body size\<close>

consts max_tx_size :: "p_params \<Rightarrow> nat" \<comment> \<open>max transaction size\<close>

consts max_header_size :: "p_params \<Rightarrow> nat" \<comment> \<open>max block header size\<close>

consts tau :: "p_params \<Rightarrow> real" \<comment> \<open>[0, 1]\<close>

consts rho :: "p_params \<Rightarrow> real" \<comment> \<open>[0, 1]\<close>

consts active_slot_coeff :: "p_params \<Rightarrow> real" \<comment> \<open>[0, 1]\<close>

text \<open> Global Constants \<close>

consts slots_per_epoch :: nat \<comment> \<open>slots per epoch\<close>

consts start_rewards :: duration \<comment> \<open>duration to start reward calculations\<close>

text \<open> Helper Functions \<close>

fun epoch :: "slot \<Rightarrow> epoch" where
  "epoch s = undefined" \<comment> \<open>NOTE: Undefined for now\<close>

fun first_slot :: "epoch \<Rightarrow> slot" where
  "first_slot e = undefined" \<comment> \<open>NOTE: Undefined for now\<close>

end
