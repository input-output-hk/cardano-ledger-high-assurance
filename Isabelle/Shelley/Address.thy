section \<open> Addresses \<close>

theory Address
  imports Main
begin

text \<open> Credential \<close>

typedecl credential \<comment> \<open>NOTE: Abstract for now\<close>

text \<open> Output address \<close>

typedecl addr \<comment> \<open>NOTE: Abstract for now\<close>

text \<open> Reward account \<close>

typedecl addr_rwd \<comment> \<open>NOTE: Abstract for now\<close>

text \<open> Construct a reward account \<close>

consts addr_rwd :: "credential \<Rightarrow> addr_rwd" \<comment> \<open>NOTE: Abstract for now\<close>

end
