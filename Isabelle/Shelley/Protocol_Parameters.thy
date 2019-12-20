section \<open> Protocol Parameters \<close>

theory Protocol_Parameters
  imports Finite_Map_Extras
begin

text \<open> Protocol parameter name \<close>

typedecl ppm \<comment> \<open>NOTE: Abstract for now\<close>

text \<open> Protocol parameter value \<close>

typedecl pvalue \<comment> \<open>NOTE: Abstract for now\<close>

text \<open> Protocol parameter map \<close>

type_synonym p_params = "(ppm, pvalue) fmap"

end
