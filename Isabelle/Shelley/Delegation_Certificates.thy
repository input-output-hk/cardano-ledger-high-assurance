section \<open> Delegation certificates \<close>

theory Delegation_Certificates
  imports Address Basic_Types Finite_Map_Extras
begin

subsection \<open> Delegation Definitions \<close>

text \<open> Delegation certificate \<close>

datatype d_cert = DCert_RegKey | DCert_DeregKey \<comment> \<open>NOTE: Incomplete for now\<close>

text \<open> Registered stake credential \<close>

type_synonym stake_creds = "(credential, slot) fmap"

text \<open> Registered stake pools \<close>

typedecl stake_pools \<comment> \<open>NOTE: Abstract for now\<close>

text \<open> Stake pools parameters \<close>

typedecl pool_param \<comment> \<open>NOTE: Abstract for now\<close>

text \<open> Certificate witness \<close>

consts cwitness :: "d_cert \<Rightarrow> credential" \<comment> \<open>NOTE: Abstract for now\<close>

text \<open> Registered credential \<close>

consts reg_cred :: "d_cert \<Rightarrow> credential" \<comment> \<open>NOTE: Abstract for now\<close>

end
