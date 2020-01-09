section \<open> Delegation \<close>

theory Delegation
  imports Finite_Map_Extras Basic_Types Address Delegation_Certificates Transaction
begin

subsection \<open> Delegation Transitions \<close>

text \<open> Delegation States \<close>

\<comment> \<open>NOTE: Only \<open>stkCreds\<close>, \<open>rewards\<close> and \<open>i\<^sub>r\<^sub>w\<^sub>d\<close> for now\<close>
type_synonym d_state = "
  stake_creds \<times> \<comment> \<open>registered stake delegators\<close>
  (addr_rwd, coin) fmap \<times> \<comment> \<open>rewards\<close>
  (credential, coin) fmap \<comment> \<open>instantaneous rewards\<close>"

typedecl p_state \<comment> \<open>NOTE: Abstract for now\<close>

text \<open> Delegation Environment \<close>

type_synonym d_env = slot \<comment> \<open>NOTE: Only slot for now\<close>

subsection \<open> Delegation Rules \<close>

text \<open> Delegation Inference Rules \<close>

text \<open>
  NOTE:
  \<^item> Only the \<open>deleg_reg\<close> and \<open>deleg_dereg\<close> rules are included for now.
  \<^item> Although \<open>addr_rwd hk \<notin> dom rewards \<Longleftrightarrow> hk \<notin> dom stkCreds\<close> is a property of the system,
  it cannot be proven in \<open>DELEG\<close> alone (but possibly in \<open>DELEGS\<close>). So I had either to add an extra
  precondition \<open>addr_rwd hk \<notin> dom rewards\<close> or use \<open>\<union>\<^sub>\<leftarrow>\<close> instead of \<open>++\<^sub>f\<close> in rule \<open>deleg_reg\<close> since
  Lemma 15.6 is a property of \<open>DELEG\<close>.
 \<close>
inductive deleg_sts :: "d_env \<Rightarrow> d_state \<Rightarrow> d_cert \<Rightarrow> d_state \<Rightarrow> bool"
  (\<open>_ \<turnstile> _ \<rightarrow>\<^bsub>DELEG\<^esub>{_} _\<close> [51, 0, 51] 50)
  where
    deleg_reg: "
      slot \<turnstile>
        (stk_creds, rewards, i\<^sub>r\<^sub>w\<^sub>d)
          \<rightarrow>\<^bsub>DELEG\<^esub>{c}
        (stk_creds ++\<^sub>f {hk $$:= slot}, rewards \<union>\<^sub>\<leftarrow> {addr_rwd hk $$:= 0}, i\<^sub>r\<^sub>w\<^sub>d)"
      if "c = DCert_RegKey"
      and "hk = reg_cred c"
      and "hk \<notin> fmdom' stk_creds"
  | deleg_dereg: "
      slot \<turnstile>
        (stk_creds, rewards, i\<^sub>r\<^sub>w\<^sub>d)
          \<rightarrow>\<^bsub>DELEG\<^esub>{c}
        ({hk} \<lhd>/ stk_creds, {addr_rwd hk} \<lhd>/ rewards, i\<^sub>r\<^sub>w\<^sub>d)"
      if "c = DCert_DeregKey"
      and "hk = cwitness c"
      and "rewards $$ (addr_rwd hk) = Some 0"
      and "hk \<in> fmdom' stk_creds"

subsection \<open> Delegation and Pool Combined Rules \<close>

text \<open> Delegation and Pool Combined Environment \<close>

type_synonym d_p_env = slot \<comment> \<open>NOTE: Only slot for now\<close>

text \<open> Delegation and Pool Combined State \<close>

type_synonym d_p_state = "d_state \<times> p_state"

text \<open> Delegation and Pool Combined Transition Rules \<close>

text \<open>
  NOTE:
  \<^item> Only the \<open>delpl_deleg\<close> rule is included for now.
\<close>
inductive delpl_sts :: "d_p_env \<Rightarrow> d_p_state \<Rightarrow> d_cert \<Rightarrow> d_p_state \<Rightarrow> bool"
  (\<open>_ \<turnstile> _ \<rightarrow>\<^bsub>DELPL\<^esub>{_} _\<close> [51, 0, 51] 50)
  where
    delpl_deleg: "
      slot \<turnstile> (dstate, pstate) \<rightarrow>\<^bsub>DELPL\<^esub>{c} (dstate', pstate)"
      if "slot \<turnstile> dstate \<rightarrow>\<^bsub>DELEG\<^esub>{c} dstate'"

text \<open> Certificate Sequence Environment \<close>

type_synonym d_p_s_env = "slot \<times> tx"

text \<open> Delegation sequence rules \<close>

text \<open>
  NOTE:
  \<^item> The first and second preconditions in the \<open>seq_delg_ind\<close> rule are not included for now.
\<close>
inductive delegs_sts :: "d_p_s_env \<Rightarrow> d_p_state \<Rightarrow> d_cert list \<Rightarrow> d_p_state \<Rightarrow> bool"
  (\<open>_ \<turnstile> _ \<rightarrow>\<^bsub>DELEGS\<^esub>{_} _\<close> [51, 0, 51] 50)
  where
    seq_delg_base: "
      (slot, tx) \<turnstile>
        ((stk_creds, rewards, i\<^sub>r\<^sub>w\<^sub>d), pstate) \<rightarrow>\<^bsub>DELEGS\<^esub>{[]} ((stk_creds, rewards', i\<^sub>r\<^sub>w\<^sub>d), pstate)"
      if "wdrls = txwdrls tx"
      and "wdrls \<subseteq>\<^sub>f rewards"
      and "rewards' = rewards \<union>\<^sub>\<rightarrow> fmmap (\<lambda>_. 0) wdrls"
    | seq_delg_ind: "
      (slot, tx) \<turnstile> dpstate \<rightarrow>\<^bsub>DELEGS\<^esub>{\<Gamma> @ [c]} dpstate''"
      if "(slot, tx) \<turnstile> dpstate \<rightarrow>\<^bsub>DELEGS\<^esub>{\<Gamma>} dpstate'"
      and "slot \<turnstile> dpstate' \<rightarrow>\<^bsub>DELPL\<^esub>{c} dpstate''"

end
