section \<open> Protocol Parameters \<close>

theory Protocol_Parameters
  imports "HOL.Complex" Finite_Map_Extras
begin

text \<open> Protocol parameter name \<close>

typedecl ppm \<comment> \<open>NOTE: Abstract for now\<close>

text \<open> Protocol parameter value \<close>

typedecl pvalue \<comment> \<open>NOTE: Abstract for now\<close>

text \<open> Protocol parameter map \<close>

type_synonym p_params = "(ppm, pvalue) fmap"

text \<open> Accessor Functions \<close>

consts tau :: "p_params \<Rightarrow> real" \<comment> \<open>[0, 1]\<close>

consts rho :: "p_params \<Rightarrow> real" \<comment> \<open>[0, 1]\<close>

consts active_slot_coeff :: "p_params \<Rightarrow> real" \<comment> \<open>[0, 1]\<close>

text \<open> Global Constants \<close>

consts slots_per_epoch :: nat

end
