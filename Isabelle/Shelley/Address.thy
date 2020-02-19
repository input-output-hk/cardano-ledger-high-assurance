section \<open> Addresses \<close>

theory Address
  imports Main
begin

text \<open> Credential \<close>

typedecl credential \<comment> \<open>NOTE: Abstract for now\<close>
axiomatization where credential_linorder: "OFCLASS(credential, linorder_class)"
instance credential :: linorder by (rule credential_linorder)

text \<open> Output address \<close>

typedecl addr \<comment> \<open>NOTE: Abstract for now\<close>

text \<open> Reward account \<close>

typedecl addr_rwd \<comment> \<open>NOTE: Abstract for now\<close>
axiomatization where addr_rwd_linorder: "OFCLASS(addr_rwd, linorder_class)"
instance addr_rwd :: linorder by (rule addr_rwd_linorder)

text \<open> Construct a reward account \<close>

consts addr_rwd :: "credential \<Rightarrow> addr_rwd" \<comment> \<open>NOTE: Abstract for now\<close>

end
