section \<open> Update Proposal Mechanism \<close>

theory Update
  imports Basic_Types Protocol_Parameters Cryptography Finite_Map_Extras
begin

subsection \<open> Protocol Parameter Update Proposals \<close>

text \<open> Protocol parameter update \<close>

type_synonym pp_update = "(key_hash_g, p_params) fmap"

text \<open> Epoch Helper Functions \<close>

fun voted_value\<^sub>P\<^sub>P\<^sub>a\<^sub>r\<^sub>a\<^sub>m\<^sub>s :: "(key_hash_g, p_params) fmap \<Rightarrow> p_params option" where
  "voted_value\<^sub>P\<^sub>P\<^sub>a\<^sub>r\<^sub>a\<^sub>m\<^sub>s vs = undefined" \<comment> \<open>NOTE: Undefined for now\<close>

subsection \<open> Application Version Update Proposals \<close>

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
