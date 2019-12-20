section \<open> Delegation \<close>

theory Delegation
  imports Finite_Map_Extras Basic_Types Address
begin

subsection \<open> Delegation Definitions \<close>

text \<open> Delegation certificate \<close>

datatype d_cert = DCert_RegKey | DCert_DeregKey \<comment> \<open>NOTE: Incomplete for now\<close>

text \<open> Registered stake credential \<close>

typedecl stake_creds \<comment> \<open>NOTE: Abstract for now\<close>

text \<open> Registered stake pools \<close>

typedecl stake_pools \<comment> \<open>NOTE: Abstract for now\<close>

text \<open> Certificate witness \<close>

consts cwitness :: "d_cert \<Rightarrow> credential" \<comment> \<open>NOTE: Abstract for now\<close>

text \<open> Registered credential \<close>

consts reg_cred :: "d_cert \<Rightarrow> credential" \<comment> \<open>NOTE: Abstract for now\<close>

subsection \<open> Delegation Transitions \<close>

text \<open> Delegation States \<close>

type_synonym d_state = "(addr_rwd, coin) fmap" \<comment> \<open>NOTE: Only rewards for now\<close>

text \<open> Delegation Environment \<close>

type_synonym d_env = slot \<comment> \<open>NOTE: Only slot for now\<close>

subsection \<open> Delegation Rules \<close>

text \<open> Delegation Inference Rules \<close>

text \<open> NOTE:
  Although \<open>addr_rwd hk \<notin> dom rewards \<Longleftrightarrow> hk \<notin> dom stkCreds\<close> is a property of the system,
  it cannot be proven in \<open>DELEG\<close> alone (but possibly in \<open>DELEGS\<close>). So I had either to add an extra
  precondition \<open>addr_rwd hk \<notin> dom rewards\<close> or use \<open>\<union>\<^sub>\<leftarrow>\<close> instead of \<open>++\<^sub>f\<close> in rule \<open>deleg_reg\<close> since
  Lemma 15.6 is a property of \<open>DELEG\<close>.
 \<close>

inductive deleg_sts :: "d_env \<Rightarrow> d_state \<Rightarrow> d_cert \<Rightarrow> d_state \<Rightarrow> bool"
  (\<open>_ \<turnstile> _ \<rightarrow>\<^bsub>DELEG\<^esub>{_} _\<close> [51, 0, 51] 50)
  where
    deleg_reg: "
      \<Gamma> \<turnstile> rewards \<rightarrow>\<^bsub>DELEG\<^esub>{c} rewards \<union>\<^sub>\<leftarrow> {addr_rwd hk $$:= 0}"
      if "c = DCert_RegKey"
      and "hk = reg_cred c"
  | deleg_dereg: "
      \<Gamma> \<turnstile> rewards \<rightarrow>\<^bsub>DELEG\<^esub>{c} {addr_rwd hk} \<lhd>/ rewards"
      if "c = DCert_DeregKey"
      and "hk = cwitness c"
      and "rewards $$ (addr_rwd hk) = Some 0"

end
