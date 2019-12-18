section \<open> Update Proposal Mechanism \<close>

theory Update
  imports Basic_Types Protocol_Parameters Cryptography Finite_Map_Extras
begin

text \<open> Protocol parameter update \<close>

typedecl pp_update \<comment> \<open>NOTE: Abstract for now\<close>

text \<open> Application update \<close>

typedecl av_update \<comment> \<open>NOTE: Abstract for now\<close>

text \<open> Update proposal \<close>

typedecl update \<comment> \<open>NOTE: Abstract for now\<close>

text \<open> Update environment \<close>

type_synonym update_env = "slot \<times> p_params \<times> (key_hash_g, key_hash) fmap"

text \<open> Update states \<close>

type_synonym update_state = "pp_update \<times> av_update \<times> (slot, applications) fmap \<times> applications"

text \<open> Update inference rules \<close>

inductive update_sts :: "update_env \<Rightarrow> update_state \<Rightarrow> update \<Rightarrow> update_state \<Rightarrow> bool"
  (\<open>_ \<turnstile> _ \<rightarrow>\<^bsub>UP\<^esub>{_} _\<close> [51, 0, 51] 50)
  where
    update: "
      \<Gamma> \<turnstile> s \<rightarrow>\<^bsub>UP\<^esub>{up} s'"
      if "s' = s" \<comment> \<open>TODO: Continue later\<close>

end
