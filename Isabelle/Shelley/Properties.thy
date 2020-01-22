section \<open> Properties \<close>

theory Properties
  imports UTxO Delegation Rewards Ledger Chain
begin

subsection \<open> Preservation of Value \<close>

text \<open> Lovelace Value \<close>

fun val_coin :: "coin \<Rightarrow> coin" where
  "val_coin c = c"

abbreviation val_map :: "('a, coin) fmap \<Rightarrow> coin" where
  "val_map m \<equiv> (\<Sum>k \<in> fmdom' m. m $$! k)"

abbreviation val_utxo :: "utxo \<Rightarrow> coin" where
  "val_utxo utxo \<equiv> ubalance utxo"

fun val_utxo_state :: "utxo_state \<Rightarrow> coin" where
  "val_utxo_state (utxo, deps, fees, _) = val_utxo utxo + val_coin deps + val_coin fees"

lemma val_map_add:
  assumes "m $$ k = None"
  shows "val_map m(k $$:= c) = val_map m + c"
proof -
  let ?m' = "m(k $$:= c)"
  have "val_map ?m' = (\<Sum>k\<^sub>i \<in> fmdom' m \<union> {k}. ?m' $$! k\<^sub>i)"
    by simp
  also from assms have "\<dots> = (\<Sum>k\<^sub>i \<in> fmdom' m. ?m' $$! k\<^sub>i) + (?m' $$! k)"
    by (simp add: fmdom'_notI)
  also have "\<dots> = (\<Sum>k\<^sub>i \<in> fmdom' m. ?m' $$! k\<^sub>i) + c"
    by simp
  also from assms have "\<dots> = (\<Sum>k\<^sub>i \<in> fmdom' m. m $$! k\<^sub>i) + c"
    by (metis (no_types, lifting) fmdom'_notI fmupd_lookup sum.cong)
  finally show ?thesis
    by simp
qed

\<comment> \<open>NOTE: Lemma 15.4 in the spec.\<close>
lemma val_map_union:
  assumes "fmdom' m\<^sub>1 \<inter> fmdom' m\<^sub>2 = {}"
  shows "val_map (m\<^sub>1 ++\<^sub>f m\<^sub>2) = val_map m\<^sub>1 + val_map m\<^sub>2"
  using assms
proof (induction m\<^sub>2 arbitrary: m\<^sub>1)
  case fmempty
  then show ?case
    by simp
next
  case (fmupd k c m\<^sub>2)
  have "val_map (m\<^sub>1 ++\<^sub>f m\<^sub>2(k $$:= c)) = val_map ((m\<^sub>1 ++\<^sub>f m\<^sub>2)(k $$:= c))"
    by simp
  also have "\<dots> = val_map (m\<^sub>1 ++\<^sub>f m\<^sub>2) + c"
  proof -
    have "fmdom' (m\<^sub>1 ++\<^sub>f m\<^sub>2) = fmdom' m\<^sub>1 \<union> fmdom' m\<^sub>2"
      by simp
    moreover from fmupd.prems have "m\<^sub>1 $$ k = None"
      by auto
    ultimately have "(m\<^sub>1 ++\<^sub>f m\<^sub>2) $$ k = None"
      using fmupd.hyps by simp
    then show ?thesis
      using val_map_add by metis
  qed
  also from fmupd.prems and fmupd.IH have "\<dots> = val_map m\<^sub>1 + val_map m\<^sub>2 + c"
    by simp
  also have "\<dots> = val_map m\<^sub>1 + val_map (m\<^sub>2(k $$:= c))"
  proof -
    from fmupd.hyps have "val_map m\<^sub>2(k $$:= c) = val_map m\<^sub>2 + c"
      using val_map_add by simp
    then show ?thesis
      by simp
  qed
  finally show ?case .
qed

\<comment> \<open>NOTE: Lemma 15.3 in the spec.\<close>
lemma val_map_split:
  shows "val_map m = val_map (s \<lhd>/ m) + val_map (s \<lhd> m)"
proof -
  have *: "fmdom' (s \<lhd>/ m) \<inter> fmdom' (s \<lhd> m) = {}"
    by auto
  then have "m = s \<lhd>/ m ++\<^sub>f s \<lhd> m"
    using fmap_partition by simp
  with * show ?thesis
    using val_map_union by metis
qed

lemma val_utxo_val_map:
  shows "val_utxo utxo = val_map (fmmap snd utxo)"
proof -
  have "fmdom' (fmmap snd utxo) = fmdom' utxo"
    by simp
  moreover have "\<And>k. k \<in> fmdom' utxo \<Longrightarrow> (fmmap snd utxo) $$! k = snd (utxo $$! k)"
    using fmlookup_dom'_iff by force
  ultimately show ?thesis
    by auto
qed

text \<open>
  NOTE:
  \<^item> Lemma 15.5 in the spec.
  \<^item> The proof in the document applies lemmas 15.3 and 15.4 on \<open>utxo\<close>'s,
    however this is incorrect since the range of \<open>utxo\<close> is not \<open>coin\<close> but
    \<open>(addr, coin)\<close>.
  \<^item> The proof in the document applies lemma 15.4 without proving its
    precondition, which is not trivial to formalize.
\<close>
lemma utxo_value_preservation:
  assumes "e \<turnstile> s \<rightarrow>\<^bsub>UTXO\<^esub>{tx} s'"
  shows "val_utxo_state s + wbalance (txwdrls tx) = val_utxo_state s'"
proof -
  from assms show ?thesis
  proof cases
    case (utxo_inductive utxo pp stk_creds stpools refunded decayed deposit_change slot
      gen_delegs ups ups' deps fees)
    from \<open>s' =
      (txins tx \<lhd>/ utxo ++\<^sub>f outs tx, deps + deposit_change, fees + txfee tx + decayed, ups')\<close>
    have "val_utxo_state s' =
      val_utxo_state (
        (txins tx \<lhd>/ utxo) ++\<^sub>f outs tx,
        deps + deposit_change,
        fees + txfee tx + decayed,
        ups')"
      by blast
    also have "\<dots> =
      ubalance ((txins tx \<lhd>/ utxo) ++\<^sub>f outs tx)
      + (deps + deposit_change)
      + (fees + txfee tx + decayed)"
      by simp
    also have "\<dots> =
      ubalance (txins tx \<lhd>/ utxo) + ubalance (outs tx)
      + (deps + deposit_change)
      + (fees + txfee tx + decayed)"
    proof -
      have "ubalance ((txins tx \<lhd>/ utxo) ++\<^sub>f outs tx) =
        val_map (fmmap snd ((txins tx \<lhd>/ utxo) ++\<^sub>f outs tx))"
        by (fact val_utxo_val_map)
      also have "\<dots> = val_map (fmmap snd (txins tx \<lhd>/ utxo) ++\<^sub>f fmmap snd (outs tx))"
        by simp
      also have "\<dots> = val_map (fmmap snd (txins tx \<lhd>/ utxo)) + val_map (fmmap snd (outs tx))"
      proof -
        from \<open>txid tx \<notin> {tid | tid ix. (tid, ix) \<in> fmdom' utxo}\<close>
        have "fmdom' (txins tx \<lhd>/ utxo) \<inter> fmdom' (outs tx) = {}"
          using txins_outs_exc by blast
        then have "fmdom' (fmmap snd (txins tx \<lhd>/ utxo)) \<inter> fmdom' (fmmap snd (outs tx)) = {}"
          by simp
        then show ?thesis
          using val_map_union by blast
      qed
      also have "\<dots> = ubalance (txins tx \<lhd>/ utxo) + ubalance (outs tx)"
        using val_utxo_val_map by presburger
      finally show ?thesis
        by linarith
    qed
    also from \<open>deposit_change = deposits pp stpools (txcerts tx) - (refunded + decayed)\<close>
    have "\<dots> =
      ubalance (txins tx \<lhd>/ utxo) + ubalance (outs tx)
      + (deps + deposits pp stpools (txcerts tx) - (refunded + decayed))
      + (fees + txfee tx + decayed)"
      by simp
    also have "\<dots> =
      ubalance (txins tx \<lhd>/ utxo) + ubalance (outs tx)
      + deps + deposits pp stpools (txcerts tx) - refunded
      + fees + txfee tx"
      by simp
    also from \<open>refunded = decayed_tx pp stk_creds tx\<close> have "\<dots> =
      ubalance (txins tx \<lhd>/ utxo) + ubalance (outs tx)
      + deps + deposits pp stpools (txcerts tx) - key_refunds pp stk_creds tx
      + fees + txfee tx"
      by simp
    also from \<open>consumed pp utxo stk_creds tx = produced pp stpools tx\<close> have "\<dots> =
      ubalance (txins tx \<lhd>/ utxo) + ubalance (txins tx \<lhd> utxo)
      + wbalance (txwdrls tx) + key_refunds pp stk_creds tx
      + deps - key_refunds pp stk_creds tx + fees"
      by simp
    also have "\<dots> =
      ubalance (txins tx \<lhd>/ utxo) + ubalance (txins tx \<lhd> utxo)
      + wbalance (txwdrls tx) + deps + fees"
      by simp
    also have "\<dots> = ubalance utxo + wbalance (txwdrls tx) + deps + fees"
    proof -
      have "ubalance (txins tx \<lhd>/ utxo) + ubalance (txins tx \<lhd> utxo) =
        val_map (fmmap snd (txins tx \<lhd>/ utxo)) + val_map (fmmap snd (txins tx \<lhd> utxo))"
        using val_utxo_val_map by presburger
      also have "\<dots> =
        val_map (txins tx \<lhd>/ (fmmap snd utxo)) + val_map (txins tx \<lhd> (fmmap snd utxo))"
        by simp
      also from \<open>txins tx \<subseteq> fmdom' utxo\<close> have "\<dots> = val_map (fmmap snd utxo)"
        using val_map_split by (metis fmdom'_map)
      finally show ?thesis
        using val_utxo_val_map by simp
    qed
    finally show ?thesis
      using \<open>s = (utxo, deps, fees, ups)\<close> by simp
  qed
qed

fun val_deleg_state :: "d_state \<Rightarrow> coin" where
  "val_deleg_state (_, rewards, _) = val_map rewards"

lemma val_map_dom_exc_singleton:
  assumes "m $$ k = Some v"
  shows "val_map ({k} \<lhd>/ m) = val_map m - v"
proof -
  from assms have *: "val_map ({k} \<lhd> m) = val_map {k $$:= v}"
    using dom_res_singleton by metis
  have "val_map ({k} \<lhd>/ m) = val_map ({k} \<lhd> m) + val_map ({k} \<lhd>/ m) - val_map ({k} \<lhd> m)"
    by simp
  also have "\<dots> = val_map ({k} \<lhd>/ m) + val_map ({k} \<lhd> m) - val_map ({k} \<lhd> m)"
    by simp
  also have "\<dots> = val_map m - val_map ({k} \<lhd> m)"
    using val_map_split by metis
  also from * and assms have "\<dots> = val_map m - val_map {k $$:= v}"
    by linarith
  finally show ?thesis
    by simp
qed

\<comment> \<open>NOTE: Lemma 15.6 in the spec.\<close>
lemma deleg_value_preservation:
  assumes "e \<turnstile> s \<rightarrow>\<^bsub>DELEG\<^esub>{c} s'"
  shows "val_deleg_state s = val_deleg_state s'"
proof -
  from assms show ?thesis
  proof cases
    case (deleg_reg hk stk_creds rewards i\<^sub>r\<^sub>w\<^sub>d)
    from \<open>s' = (stk_creds ++\<^sub>f {hk $$:= e}, rewards \<union>\<^sub>\<leftarrow> {addr_rwd hk $$:= 0}, i\<^sub>r\<^sub>w\<^sub>d)\<close>
    have *: "val_deleg_state s' =
      val_deleg_state (stk_creds ++\<^sub>f {hk $$:= e}, rewards \<union>\<^sub>\<leftarrow> {addr_rwd hk $$:= 0}, i\<^sub>r\<^sub>w\<^sub>d)"
      by simp
    then show ?thesis
    proof (cases "addr_rwd hk \<in> fmdom' rewards")
      case True
      then have "rewards \<union>\<^sub>\<leftarrow> {addr_rwd hk $$:= 0} = rewards"
        by simp
      with \<open>s = (stk_creds, rewards, i\<^sub>r\<^sub>w\<^sub>d)\<close>
      have "val_deleg_state (stk_creds ++\<^sub>f {hk $$:= e}, rewards \<union>\<^sub>\<leftarrow> {addr_rwd hk $$:= 0}, i\<^sub>r\<^sub>w\<^sub>d) =
        val_deleg_state s"
        by simp
      with * show ?thesis
        by simp
    next
      case False
      then have **: "rewards \<union>\<^sub>\<leftarrow> {addr_rwd hk $$:= 0} = rewards ++\<^sub>f {addr_rwd hk $$:= 0}"
        by simp
      with False have "fmdom' rewards \<inter> fmdom' {addr_rwd hk $$:= 0} = {}"
        by simp
      then have "val_map (rewards ++\<^sub>f {addr_rwd hk $$:= 0}) =
        val_map rewards + val_map {addr_rwd hk $$:= 0}"
        using val_map_union by blast
      also have "\<dots> = val_map rewards + 0"
        by simp
      finally have "
        val_deleg_state (stk_creds ++\<^sub>f {hk $$:= e}, rewards ++\<^sub>f {addr_rwd hk $$:= 0}, i\<^sub>r\<^sub>w\<^sub>d) =
        val_deleg_state s"
        using \<open>s = (stk_creds, rewards, i\<^sub>r\<^sub>w\<^sub>d)\<close> by auto
      with * and ** show ?thesis
        by presburger
    qed
  next
    case (deleg_dereg hk rewards stk_creds i\<^sub>r\<^sub>w\<^sub>d)
    then have "val_deleg_state s' = val_map ({addr_rwd hk} \<lhd>/ rewards)"
      by simp
    also from \<open>rewards $$ (addr_rwd hk) = Some 0\<close> have "\<dots> = val_map rewards - 0"
      using val_map_dom_exc_singleton by fast
    finally show ?thesis
      using \<open>s = (stk_creds, rewards, i\<^sub>r\<^sub>w\<^sub>d)\<close> by simp
  qed
qed

fun val_delegs_state :: "d_p_state \<Rightarrow> coin" where
  "val_delegs_state (dstate, _) = val_deleg_state dstate"

lemma val_map_minus:
  assumes "m\<^sub>2 \<subseteq>\<^sub>f m\<^sub>1"
  shows "val_map (m\<^sub>1 --\<^sub>f m\<^sub>2) = val_map m\<^sub>1 - val_map m\<^sub>2"
  using assms
proof (induction m\<^sub>2 arbitrary: m\<^sub>1)
  case fmempty
  then show ?case
    by simp
next
  case (fmupd k v m\<^sub>2)
  have "val_map (m\<^sub>1 --\<^sub>f m\<^sub>2(k $$:= v)) = val_map ({k} \<lhd>/ (m\<^sub>1 --\<^sub>f m\<^sub>2))"
    by simp
  also have "\<dots> = val_map ({k} \<lhd>/ m\<^sub>1) - val_map m\<^sub>2"
  proof -
    from fmupd.prems and fmupd.hyps have "m\<^sub>2 \<subseteq>\<^sub>f {k} \<lhd>/ m\<^sub>1"
      using fmdiff_fmupd
      by (metis fmdom'_empty fmdom'_fmupd fmdrop_set_single fmfilter_alt_defs(2) fmsubset_drop_mono)
    with fmupd.IH have "val_map ({k} \<lhd>/ m\<^sub>1) - val_map m\<^sub>2 = val_map (fmdom' m\<^sub>2 \<lhd>/ ({k} \<lhd>/ m\<^sub>1))"
      by presburger
    then show ?thesis
      by (metis fmfilter_comm)
  qed
  also have "\<dots> = (val_map m\<^sub>1 - v) - val_map m\<^sub>2"
  proof -
    from fmupd.prems have "m\<^sub>1 $$ k = Some v"
      by (fastforce simp add: fmsubset_alt_def)
    with fmupd.prems show ?thesis
      using val_map_dom_exc_singleton by fastforce
  qed
  also have "\<dots> = val_map m\<^sub>1 - val_map (m\<^sub>2(k $$:= v))"
  proof -
    have "\<dots> = val_map m\<^sub>1 - (val_map m\<^sub>2 + v)"
      by simp
    with fmupd.hyps show ?thesis
      using val_map_add by metis
  qed
  finally show ?case .
qed

lemma fmran_fmmap_const: (* TODO: Find nicer proofs for SMT calls. *)
  assumes "m \<noteq> {$$}"
  shows "fmran (fmmap (\<lambda>_. v) m) = {|v|}"
  using assms
proof (induction m)
  case fmempty
  then show ?case by simp
next
  case (fmupd k' v' m)
  then show ?case
  proof (cases "m \<noteq> {$$}")
    case True
    have "fmmap (\<lambda>_. v) m(k' $$:= v') = fmmap (\<lambda>_. v) m ++\<^sub>f {k' $$:= v}"
      by (smt dom_res_singleton dom_res_singleton fmadd_empty(1) fmadd_empty(1,2) fmfilter_fmmap
          fmlookup_map fmmap_add fmupd_alt_def fmupd_lookup option.simps(9))
    then have "fmran (fmmap (\<lambda>_. v) m(k' $$:= v')) = fmran (fmmap (\<lambda>_. v) m ++\<^sub>f {k' $$:= v})"
      by simp
    also have "\<dots> = fmran (fmmap (\<lambda>_. v) m) |\<union>| fmran {k' $$:= v}"
    proof -
      from \<open>m $$ k' = None\<close> have "fmdom (fmmap (\<lambda>_. v) m) |\<inter>| fmdom {k' $$:= v} = {||}"
        by (simp add: fmdom_notI)
      with \<open>m $$ k' = None\<close> show ?thesis
        by (smt finter_absorb finter_commute finter_funion_distrib2 fmadd_restrict_right_dom
            fmap_singleton_comm fmdom_add fmdom_map fmdom_notD fmdom_notI fmimage_dom fmimage_union
            fmran_restrict_fset)
    qed
    also from True and fmupd.IH have "\<dots> = {|v|} |\<union>| fmran {k' $$:= v}"
      by simp
    finally show ?thesis
      by (simp add: fmran_singleton)
  next
    case False
    then have "fmmap (\<lambda>_. v) m(k' $$:= v') = {k' $$:= v}"
      by (smt dom_res_singleton dom_res_singleton fmadd_empty(1,2) fmfilter_fmmap fmlookup_map
          fmmap_add fmupd_alt_def fmupd_lookup option.simps(9))
    then show ?thesis
      by (simp add: fmran_singleton)
  qed
qed

lemma val_map_subset_zeroing:
  assumes "m\<^sub>2 \<subseteq>\<^sub>f m\<^sub>1"
  shows "val_map (m\<^sub>1 \<union>\<^sub>\<rightarrow> fmmap (\<lambda>_. 0::coin) m\<^sub>2) = val_map (m\<^sub>1 --\<^sub>f m\<^sub>2)"
  using assms
proof (cases "m\<^sub>2 = {$$}")
  case True
  then show ?thesis
    by auto
next
  case False
  let ?m = "fmmap (\<lambda>_. 0::coin) m\<^sub>2"
  have "fmdom' (fmdom' ?m \<lhd>/ m\<^sub>1) \<inter> fmdom' ?m = {}"
    by auto
  then have "val_map (m\<^sub>1 \<union>\<^sub>\<rightarrow> ?m) = val_map (fmdom' ?m \<lhd>/ m\<^sub>1) + val_map ?m"
    using val_map_union by blast
  also have "\<dots> = val_map (fmdom' ?m \<lhd>/ m\<^sub>1)"
  proof -
    from False have "fmran ?m = {|0::coin|}"
      using fmran_fmmap_const by simp
    then show ?thesis
      by (smt fmdom'_map fmlookup_dom'_iff fmlookup_map option.map(2) option.sel
          sum.not_neutral_contains_not_neutral)
  qed
  also have *: "\<dots> = val_map m\<^sub>1 - val_map (fmdom' ?m \<lhd> m\<^sub>1)"
    using val_map_split by (metis add.commute add_diff_cancel_left')
  finally show ?thesis
    using \<open>m\<^sub>2 \<subseteq>\<^sub>f m\<^sub>1\<close> and * and val_map_minus by force
qed

\<comment> \<open>NOTE: Lemma 15.7 in the spec.\<close>
lemma delegs_value_preservation:
  assumes "(slot, tx) \<turnstile> s \<rightarrow>\<^bsub>DELEGS\<^esub>{\<Gamma>} s'"
  shows "val_delegs_state s = val_delegs_state s' + wbalance (txwdrls tx)"
  using assms
proof (induction \<Gamma> arbitrary: s' rule: rev_induct)
  case Nil
  from \<open>(slot, tx) \<turnstile> s \<rightarrow>\<^bsub>DELEGS\<^esub>{[]} s'\<close> show ?case
  proof cases
    case (seq_delg_base wdrls rewards rewards' stk_creds i\<^sub>r\<^sub>w\<^sub>d pstate)
    from \<open>s = ((stk_creds, rewards, i\<^sub>r\<^sub>w\<^sub>d), pstate)\<close> have "val_delegs_state s = val_map rewards"
      by simp
    also have "\<dots> = val_map wdrls + val_map (rewards --\<^sub>f wdrls)"
    proof -
      from \<open>wdrls \<subseteq>\<^sub>f rewards\<close> have "rewards = wdrls ++\<^sub>f (rewards --\<^sub>f wdrls)"
        by (simp add: fmdiff_partition)
      moreover have "fmdom' wdrls \<inter> fmdom' (rewards --\<^sub>f wdrls) = {}"
        by auto
      ultimately show ?thesis
        using val_map_union by metis
    qed
    also from \<open>wdrls = txwdrls tx\<close> have "\<dots> = val_map (rewards --\<^sub>f wdrls) + wbalance (txwdrls tx)"
      by auto
    also from \<open>wdrls \<subseteq>\<^sub>f rewards\<close> have "\<dots> =
      val_map (rewards \<union>\<^sub>\<rightarrow> fmmap (\<lambda>_. 0) wdrls) + wbalance (txwdrls tx)"
      using val_map_subset_zeroing by fastforce
    also from \<open>rewards' = rewards \<union>\<^sub>\<rightarrow> fmmap (\<lambda>_. 0) wdrls\<close> have "\<dots> =
      val_map rewards' + wbalance (txwdrls tx)"
      by simp
    finally show ?thesis
      using \<open>s' = ((stk_creds, rewards', i\<^sub>r\<^sub>w\<^sub>d), pstate)\<close> by simp
  next
    case (seq_delg_ind \<Gamma> dpstate' c)
    then show ?thesis
      by simp
  qed
next
  case (snoc c \<Gamma>)
  from \<open>(slot, tx) \<turnstile> s \<rightarrow>\<^bsub>DELEGS\<^esub>{\<Gamma> @ [c]} s'\<close> obtain s''
    where "(slot, tx) \<turnstile> s \<rightarrow>\<^bsub>DELEGS\<^esub>{\<Gamma>} s''" and "slot \<turnstile> s'' \<rightarrow>\<^bsub>DELPL\<^esub>{c} s'"
    using delegs_sts.simps by blast
  from \<open>(slot, tx) \<turnstile> s \<rightarrow>\<^bsub>DELEGS\<^esub>{\<Gamma>} s''\<close> and snoc.IH have "val_delegs_state s
    = val_delegs_state s'' + val_map (txwdrls tx)"
    by simp
  moreover from \<open>slot \<turnstile> s'' \<rightarrow>\<^bsub>DELPL\<^esub>{c} s'\<close> have "slot \<turnstile> fst s'' \<rightarrow>\<^bsub>DELEG\<^esub>{c} fst s'"
    by (auto simp add: delpl_sts.simps)
  then have "val_deleg_state (fst s'') = val_deleg_state (fst s')"
    using deleg_value_preservation by simp
  moreover have "val_delegs_state s'' = val_deleg_state (fst s'')"
    by (metis val_delegs_state.elims eq_fst_iff)
  ultimately show ?case
    by (metis fst_conv val_delegs_state.elims)
qed

fun val_acnt :: "acnt \<Rightarrow> coin" where
  "val_acnt (treasury, reserves) = val_coin treasury + val_coin reserves"

fun val_poolreap_state :: "pl_reap_state \<Rightarrow> coin" where
  "val_poolreap_state (utxo_st, acnt, dstate, _) =
    val_utxo_state utxo_st + val_acnt acnt + val_deleg_state dstate"

lemma val_map_fmmap_keys:
  assumes "fmdom' m\<^sub>2 \<subseteq> fmdom' m\<^sub>1"
  shows "val_map (fmmap_keys (\<lambda>k v. v + m\<^sub>1 $$! k) m\<^sub>2) = val_map (fmdom' m\<^sub>2 \<lhd> m\<^sub>1) + val_map m\<^sub>2"
  using assms
proof (induction m\<^sub>2)
  case fmempty
  then show ?case
    by auto
next
  case (fmupd k' v' m\<^sub>2)
  have "val_map (fmmap_keys (\<lambda>k v. v + m\<^sub>1 $$! k) m\<^sub>2(k' $$:= v')) =
    val_map (fmmap_keys (\<lambda>k v. v + m\<^sub>1 $$! k) m\<^sub>2 ++\<^sub>f {k' $$:= v' + m\<^sub>1 $$! k'})"
  proof -
    have "fmmap_keys (\<lambda>k v. v + m\<^sub>1 $$! k) m\<^sub>2(k' $$:= v') =
      fmmap_keys (\<lambda>k v. v + m\<^sub>1 $$! k) m\<^sub>2 ++\<^sub>f {k' $$:= v' + m\<^sub>1 $$! k'}"
      by transfer' (auto simp add: fmap_ext)
    then show ?thesis
      by simp
  qed
  also have "\<dots> =
    val_map (fmmap_keys (\<lambda>k v. v + m\<^sub>1 $$! k) m\<^sub>2) + val_map {k' $$:= v' + m\<^sub>1 $$! k'}"
  proof -
    from \<open>m\<^sub>2 $$ k' = None\<close>
    have "fmdom' (fmmap_keys (\<lambda>k v. v + m\<^sub>1 $$! k) m\<^sub>2) \<inter> fmdom' {k' $$:= v' + m\<^sub>1 $$! k'} = {}"
      by (simp add: fmdom'_notI)
    then show ?thesis
      using val_map_union by blast
  qed
  also have "\<dots> = 	val_map (fmmap_keys (\<lambda>k v. v + m\<^sub>1 $$! k) m\<^sub>2) + (v' + m\<^sub>1 $$! k')"
    by simp
  also from \<open>fmdom' m\<^sub>2(k' $$:= v') \<subseteq> fmdom' m\<^sub>1\<close> and fmupd.IH have "\<dots> =
    val_map (fmdom' m\<^sub>2 \<lhd> m\<^sub>1) + val_map m\<^sub>2 + (v' + m\<^sub>1 $$! k')"
    by simp
  also have "\<dots> = (val_map (fmdom' m\<^sub>2 \<lhd> m\<^sub>1) + m\<^sub>1 $$! k') + (val_map m\<^sub>2 + v')"
    by simp
  also have "\<dots> = val_map (fmdom' m\<^sub>2(k' $$:= v') \<lhd> m\<^sub>1) + val_map m\<^sub>2(k' $$:= v')"
  proof -
    have "val_map (fmdom' m\<^sub>2 \<lhd> m\<^sub>1) + m\<^sub>1 $$! k' = val_map (fmdom' m\<^sub>2(k' $$:= v') \<lhd> m\<^sub>1)"
    proof -
      from \<open>m\<^sub>2 $$ k' = None\<close>
      have "val_map (fmdom' m\<^sub>2(k' $$:= v') \<lhd> m\<^sub>1) = val_map ((fmdom' m\<^sub>2 \<union> {k'}) \<lhd> m\<^sub>1)"
        by simp
      also have "\<dots> = val_map ((fmdom' m\<^sub>2 \<lhd> m\<^sub>1) ++\<^sub>f ({k'} \<lhd> m\<^sub>1))"
        using dom_res_union_distr by metis
      also have "\<dots> = val_map (fmdom' m\<^sub>2 \<lhd> m\<^sub>1) + val_map ({k'} \<lhd> m\<^sub>1)"
      proof -
        from \<open>fmdom' m\<^sub>2(k' $$:= v') \<subseteq> fmdom' m\<^sub>1\<close> have "fmdom' (fmdom' m\<^sub>2 \<lhd> m\<^sub>1) = fmdom' m\<^sub>2"
          by (auto simp add: fmfilter_alt_defs(4))
        moreover from \<open>fmdom' m\<^sub>2(k' $$:= v') \<subseteq> fmdom' m\<^sub>1\<close> have "fmdom' ({k'} \<lhd> m\<^sub>1) = {k'}"
          by (auto simp add: equalityI)
        ultimately have "fmdom' (fmdom' m\<^sub>2 \<lhd> m\<^sub>1) \<inter> fmdom' ({k'} \<lhd> m\<^sub>1) = {}"
          using \<open>m\<^sub>2 $$ k' = None\<close> by (simp add: fmdom'_notI)
        then show ?thesis
          using val_map_union by blast
      qed
      also have "\<dots> = val_map (fmdom' m\<^sub>2 \<lhd> m\<^sub>1) + m\<^sub>1 $$! k'"
      proof -
        from \<open>fmdom' m\<^sub>2(k' $$:= v') \<subseteq> fmdom' m\<^sub>1\<close> have "k' \<in> fmdom' m\<^sub>1"
          by simp
        then have "fmdom' ({k'} \<lhd> m\<^sub>1) = {k'}"
          by (auto simp add: equalityI)
        then show ?thesis
          by simp
      qed
      finally show ?thesis
        by simp
    qed
    moreover from \<open>m\<^sub>2 $$ k' = None\<close> have "val_map m\<^sub>2(k' $$:= v') = val_map m\<^sub>2 + v'"
      using val_map_add by metis
    ultimately show ?thesis
      by linarith
  qed
  finally show ?case .
qed

lemma val_map_inter_plus:
  assumes "fmdom' m\<^sub>2 \<subseteq> fmdom' m\<^sub>1"
  shows "val_map (m\<^sub>1 \<inter>\<^sub>+ m\<^sub>2) = val_map (fmdom' m\<^sub>2 \<lhd> m\<^sub>1) + val_map m\<^sub>2"
proof -
  from \<open>fmdom' m\<^sub>2 \<subseteq> fmdom' m\<^sub>1\<close> have "m\<^sub>1 \<inter>\<^sub>+ m\<^sub>2 = fmmap_keys (\<lambda>k v. v + m\<^sub>1 $$! k) m\<^sub>2"
    by (metis Un_iff fmdom'I fmfilter_true subset_Un_eq)
  then have "val_map (m\<^sub>1 \<inter>\<^sub>+ m\<^sub>2) = val_map (fmmap_keys (\<lambda>k v. v + m\<^sub>1 $$! k) m\<^sub>2)"
    by simp
  also from \<open>fmdom' m\<^sub>2 \<subseteq> fmdom' m\<^sub>1\<close> have "\<dots> = val_map (fmdom' m\<^sub>2 \<lhd> m\<^sub>1) + val_map m\<^sub>2"
    using val_map_fmmap_keys by blast
  finally show ?thesis .
qed

lemma val_map_sym_diff:
  assumes "fmdom' m\<^sub>2 \<subseteq> fmdom' m\<^sub>1"
  shows "val_map (m\<^sub>1 \<Delta>\<^sub>f m\<^sub>2) = val_map m\<^sub>1 - val_map (fmdom' m\<^sub>2 \<lhd> m\<^sub>1)"
proof -
  from \<open>fmdom' m\<^sub>2 \<subseteq> fmdom' m\<^sub>1\<close> have "m\<^sub>1 \<Delta>\<^sub>f m\<^sub>2 = m\<^sub>1 --\<^sub>f m\<^sub>2"
    by (metis Un_iff fmadd_empty(2) fmdom'I fmfilter_false subset_Un_eq)
  then have "val_map (m\<^sub>1 \<Delta>\<^sub>f m\<^sub>2) = val_map (m\<^sub>1 --\<^sub>f m\<^sub>2)"
    by simp
  also from \<open>fmdom' m\<^sub>2 \<subseteq> fmdom' m\<^sub>1\<close> have "\<dots> = val_map m\<^sub>1 - val_map (fmdom' m\<^sub>2 \<lhd> m\<^sub>1)"
    using val_map_split by (metis add_diff_cancel_right')
  finally show ?thesis .
qed

\<comment> \<open>NOTE: Lemma 15.8 in the spec.\<close>
lemma poolreap_value_preservation:
  assumes "e \<turnstile> s \<rightarrow>\<^bsub>POOLREAP\<^esub>{\<epsilon>} s'"
  shows "val_poolreap_state s = val_poolreap_state s'"
proof -
  from assms show ?thesis
  proof cases
    case (pool_reap reward_acnts' refunds rewards m_refunds refunded unclaimed utxo deps fees ups
      treasury reserves stk_creds i\<^sub>r\<^sub>w\<^sub>d pstate)
    from pool_reap(2) have "val_poolreap_state s' =
      val_utxo_state (utxo, deps - (unclaimed + refunded), fees, ups)
      + val_acnt (treasury + unclaimed, reserves)
      + val_deleg_state (stk_creds, rewards \<union>\<^sub>+ refunds, i\<^sub>r\<^sub>w\<^sub>d)"
      by simp
    also have "\<dots> =
      (val_utxo utxo + deps - (unclaimed + refunded) + fees)
      + (treasury + unclaimed + reserves)
      + val_map (rewards \<union>\<^sub>+ refunds)"
      by simp
    also have "\<dots> =
      val_utxo utxo + fees + reserves + deps - (unclaimed + refunded) + treasury + unclaimed
      + val_map (rewards \<union>\<^sub>+ refunds)"
      by simp
    also have "\<dots> = val_utxo utxo + fees + reserves + deps - refunded + treasury
      + val_map (rewards \<union>\<^sub>+ refunds)"
      by simp
    also have "\<dots> = val_utxo utxo + fees + reserves + deps - refunded + treasury
      + val_map rewards + val_map refunds"
    proof -
      have "val_map (rewards \<union>\<^sub>+ refunds) = val_map rewards + val_map refunds"
      proof -
        have "val_map (rewards \<union>\<^sub>+ refunds) =
          val_map (rewards \<Delta>\<^sub>f refunds) + val_map (rewards \<inter>\<^sub>+ refunds)"
        proof -
          from \<open>refunds = fmdom' rewards \<lhd> reward_acnts'\<close>
          have "fmdom' (rewards \<Delta>\<^sub>f refunds) \<inter> fmdom' (rewards \<inter>\<^sub>+ refunds) = {}"
            by (smt Int_emptyI fmadd_empty(2) fmdom'_filter fmdom'_notI fmfilter_false
                fmlookup_restrict_set fmrestrict_set_dom fmrestrict_set_fmmap_keys member_filter
                option.distinct(1)) (* TODO: Find a nicer proof. *)
          then show ?thesis
            using val_map_union by blast
        qed
        also have "\<dots> = val_map rewards - val_map (fmdom' refunds \<lhd> rewards) +
          val_map (fmdom' refunds \<lhd> rewards) + val_map refunds"
        proof -
          from \<open>refunds = fmdom' rewards \<lhd> reward_acnts'\<close> have "fmdom' refunds \<subseteq> fmdom' rewards"
            by auto
          then show ?thesis
            using val_map_sym_diff and val_map_inter_plus by fastforce
        qed
        finally show ?thesis
          by simp
      qed
      then show ?thesis
        by linarith
    qed
    finally show ?thesis
      using \<open>s = ((utxo, deps, fees, ups), (treasury, reserves), (stk_creds, rewards, i\<^sub>r\<^sub>w\<^sub>d), pstate)\<close>
        and \<open>refunded = val_map refunds\<close> by simp
  qed
qed

fun val_ledger_state :: "l_state \<Rightarrow> coin" where
  "val_ledger_state (utxo_st, dpstate) = val_utxo_state utxo_st + val_delegs_state dpstate"

fun val_epoch_state :: "epoch_state \<Rightarrow> coin" where
  "val_epoch_state (acnt, _, ls, _) = val_acnt acnt + val_ledger_state ls"

lemma val_map_union_plus: (* TODO: Find nicer proofs for SMT calls. *)
  shows "val_map (m\<^sub>1 \<union>\<^sub>+ m\<^sub>2) = val_map m\<^sub>1 + val_map m\<^sub>2"
proof (induction m\<^sub>1)
  case fmempty
  have "fmdom' m\<^sub>2 \<lhd>/ {$$} = {$$}"
    by simp
  moreover have "fmdom' {$$} \<lhd>/ m\<^sub>2 = m\<^sub>2"
    by simp
  moreover have "{$$} \<inter>\<^sub>+ m\<^sub>2 = {$$}"
    by (simp add: fmap_ext)
  moreover have "val_map {$$} = 0"
    by simp
  ultimately show ?case
    by simp
next
  case (fmupd k v m\<^sub>1)
  then show ?case
  proof (cases "m\<^sub>2 $$ k = None")
    case True
    from fmupd.hyps and True have "val_map (m\<^sub>1(k $$:= v) \<union>\<^sub>+ m\<^sub>2) = val_map ((m\<^sub>1 \<union>\<^sub>+ m\<^sub>2) ++\<^sub>f {k $$:= v})"
      using union_plus_addition_notin by metis
    also have "\<dots> = val_map (m\<^sub>1 \<union>\<^sub>+ m\<^sub>2) + val_map {k $$:= v}"
    proof -
      from fmupd.hyps and True have "fmdom' (m\<^sub>1 \<union>\<^sub>+ m\<^sub>2) \<inter> fmdom' {k $$:= v} = {}"
        by (simp add: fmdom'_notI)
      then show ?thesis
        using val_map_union by fast
    qed
    also from fmupd.IH have "\<dots> = val_map m\<^sub>1 + val_map m\<^sub>2 + val_map {k $$:= v}"
      by simp
    finally show ?thesis
      using val_map_add and fmupd.hyps by (smt fmdom'_empty fmempty_lookup sum.cong sum.empty)
  next
    case False
    from False obtain v' where *: "m\<^sub>2 $$ k = Some v'"
      by auto
    from False have "val_map (m\<^sub>1(k $$:= v) \<union>\<^sub>+ m\<^sub>2) =
      val_map (fmdom' m\<^sub>2 \<lhd>/ m\<^sub>1 ++\<^sub>f fmdom' m\<^sub>1(k $$:= v) \<lhd>/ m\<^sub>2 ++\<^sub>f (m\<^sub>1(k $$:= v) \<inter>\<^sub>+ m\<^sub>2))"
      by auto
    also from fmupd.hyps and * have "\<dots> =
      val_map (fmdom' m\<^sub>2 \<lhd>/ m\<^sub>1 ++\<^sub>f (fmdom' m\<^sub>1 \<lhd>/ m\<^sub>2 --\<^sub>f {k $$:= v'}) ++\<^sub>f (m\<^sub>1(k $$:= v) \<inter>\<^sub>+ m\<^sub>2))"
      by simp
    also have "\<dots> =
      val_map (fmdom' m\<^sub>2 \<lhd>/ m\<^sub>1 ++\<^sub>f (fmdom' m\<^sub>1 \<lhd>/ m\<^sub>2 --\<^sub>f {k $$:= v'}) ++\<^sub>f (m\<^sub>1 \<inter>\<^sub>+ m\<^sub>2)
        ++\<^sub>f {k $$:= v' + v})"
    proof -
      from \<open>m\<^sub>1 $$ k = None\<close> and * have "m\<^sub>1(k $$:= v) \<inter>\<^sub>+ m\<^sub>2 = (m\<^sub>1 \<inter>\<^sub>+ m\<^sub>2) ++\<^sub>f {k $$:= v' + v}"
        using inter_plus_addition_in by simp
      then show ?thesis
        by auto
    qed
    also have "\<dots> = val_map ((fmdom' m\<^sub>2 \<lhd>/ m\<^sub>1 ++\<^sub>f fmdom' m\<^sub>1 \<lhd>/ m\<^sub>2) --\<^sub>f {k $$:= v'} ++\<^sub>f (m\<^sub>1 \<inter>\<^sub>+ m\<^sub>2)
      ++\<^sub>f {k $$:= v' + v})"
    proof -
      from False have "fmdom' m\<^sub>2 \<lhd>/ m\<^sub>1 ++\<^sub>f (fmdom' m\<^sub>1 \<lhd>/ m\<^sub>2 --\<^sub>f {k $$:= v'}) =
        (fmdom' m\<^sub>2 \<lhd>/ m\<^sub>1 ++\<^sub>f fmdom' m\<^sub>1 \<lhd>/ m\<^sub>2) --\<^sub>f {k $$:= v'}"
        by (smt fmdom'_empty fmdom'_fmupd fmdom'_notD fmfilter_add_distrib fmfilter_true
            fmlookup_filter option.distinct(1) singletonD)
      then show ?thesis
        by auto
    qed
    also have "\<dots> = val_map ((fmdom' m\<^sub>2 \<lhd>/ m\<^sub>1 ++\<^sub>f fmdom' m\<^sub>1 \<lhd>/ m\<^sub>2 ++\<^sub>f (m\<^sub>1 \<inter>\<^sub>+ m\<^sub>2)) --\<^sub>f {k $$:= v'}
      ++\<^sub>f {k $$:= v' + v})"
    proof -
      from fmupd.hyps have "(fmdom' m\<^sub>2 \<lhd>/ m\<^sub>1 ++\<^sub>f fmdom' m\<^sub>1 \<lhd>/ m\<^sub>2) --\<^sub>f {k $$:= v'} ++\<^sub>f (m\<^sub>1 \<inter>\<^sub>+ m\<^sub>2) =
        (fmdom' m\<^sub>2 \<lhd>/ m\<^sub>1 ++\<^sub>f fmdom' m\<^sub>1 \<lhd>/ m\<^sub>2) ++\<^sub>f (m\<^sub>1 \<inter>\<^sub>+ m\<^sub>2) --\<^sub>f {k $$:= v'}"
        by (smt fmdom'_empty fmdom'_fmupd fmdom'_notI fmfilter_add_distrib fmfilter_fmmap_keys
            fmfilter_true fmlookup_filter option.distinct(1) singletonD)
      then show ?thesis
        by auto
    qed
    also have "\<dots> = val_map ((m\<^sub>1 \<union>\<^sub>+ m\<^sub>2) --\<^sub>f {k $$:= v'}) + val_map {k $$:= v' + v}"
    proof -
      have "fmdom' ((m\<^sub>1 \<union>\<^sub>+ m\<^sub>2) --\<^sub>f {k $$:= v'}) \<inter> fmdom' {k $$:= v' + v} = {}"
        by (simp add: fmdom'_notI)
      then show ?thesis
        using val_map_union by fast
    qed
    also have "\<dots> = val_map (m\<^sub>1 \<union>\<^sub>+ m\<^sub>2) - val_map {k $$:= v'} + val_map {k $$:= v' + v}"
    proof -
      from * and fmupd.hyps have "{k $$:= v'} \<subseteq>\<^sub>f fmdom' m\<^sub>1 \<lhd>/ m\<^sub>2"
        by (simp add: fmdom'_notI fmpred_upd fmsubset_alt_def)
      moreover have "(m\<^sub>1 \<inter>\<^sub>+ m\<^sub>2) $$ k = None"
        by (simp add: fmdom'_notI fmupd.hyps)
      ultimately have "{k $$:= v'} \<subseteq>\<^sub>f m\<^sub>1 \<union>\<^sub>+ m\<^sub>2"
        using * and fmdiff_partition
        by (smt Un_iff domIff dom_fmlookup fmdom'_add fmdom'_empty fmdom'_fmupd fmlookup_add
            fmlookup_filter fmpred_empty fmpred_upd fmsubset_alt_def singletonI)
      then show ?thesis
        using val_map_minus by metis
    qed
    also have "\<dots> = val_map (m\<^sub>1 \<union>\<^sub>+ m\<^sub>2) - v' + v' + v"
      by simp
    also from fmupd.IH have "\<dots> = val_map m\<^sub>1 + val_map m\<^sub>2 + v"
      by simp
    finally show ?thesis
      using \<open>m\<^sub>1 $$ k = None\<close> and val_map_add by (smt sum.cong)
  qed
qed

lemma val_map_fmap_of_list:
  fixes m :: "('a::linorder, coin) fmap" and f :: "'a::linorder \<Rightarrow> 'b::linorder"
  assumes "inj f"
  and "mono f"
  shows "val_map (fmap_of_list [(f k, v). (k, v) \<leftarrow> sorted_list_of_fmap m]) = val_map m"
  using assms
proof (induction m)
  case fmempty
  then show ?case
    unfolding sorted_list_of_fmap_def and sorted_list_of_fset_def by simp
next
  case (fmupd k v m)
  let ?g = "\<lambda>(k, v). (f k, v)"
  from \<open>m $$ k = None\<close> and assms(1,2)
  have "val_map (fmap_of_list (map ?g (sorted_list_of_fmap m(k $$:= v)))) =
    val_map ((fmap_of_list (map ?g (sorted_list_of_fmap m)))(f k $$:= v))"
    by (simp add: fmap_of_list_sorted_list_of_fmap)
  also have "\<dots> = val_map (fmap_of_list (map ?g (sorted_list_of_fmap m))) + v"
  proof -
    have "(fmap_of_list (map ?g (sorted_list_of_fmap m))) $$ (f k) = None"
    proof -
      from \<open>m $$ k = None\<close> have "k \<notin> set (map fst (sorted_list_of_fmap m))"
        by (metis domIff dom_map_of_conv_image_fst map_of_sorted_list set_map)
      with assms(1) have "f k \<notin> set (map fst (map ?g (sorted_list_of_fmap m)))"
        using map_inj_pair_non_membership by simp
      then show ?thesis
        by (metis fmlookup_of_list map_of_eq_None_iff set_map)
    qed
    then show ?thesis
      using val_map_add by force
  qed
  also from assms(1,2) and fmupd.IH have "\<dots> = val_map m + v"
    by simp
  finally show ?case
    by (metis fmupd.hyps val_map_add)
qed

\<comment> \<open>NOTE: Lemma 15.9 in the spec.\<close>
\<comment> \<open>NOTE: We require \<open>addr_rwd\<close> to be monotonic, which is a minor (though sensible) deviation from
the spec.\<close>
lemma reward_update_value_preservation:
  assumes "inj addr_rwd"
  and "mono addr_rwd"
  shows "val_epoch_state s = val_epoch_state (apply_r_upd (create_r_upd b s) s)"
proof -
  obtain treasury reserves ss utxo deps fees up stk_creds rewards i\<^sub>r\<^sub>w\<^sub>d pstate ppm
    where f1: "s =
      (
        (treasury, reserves),
        ss,
        ((utxo, deps, fees, up), ((stk_creds, rewards, i\<^sub>r\<^sub>w\<^sub>d), pstate)),
        ppm
      )"
    by (metis old.prod.exhaust val_deleg_state.cases)
  moreover obtain \<Delta>t \<Delta>r rs \<Delta>f rew\<^sub>m\<^sub>i\<^sub>r where f2: "create_r_upd b s = (\<Delta>t, \<Delta>r, rs, \<Delta>f, rew\<^sub>m\<^sub>i\<^sub>r)"
    using prod_cases5 by blast
  ultimately obtain non_distributed and rew'\<^sub>m\<^sub>i\<^sub>r and update\<^sub>r\<^sub>w\<^sub>d and unregistered
    where f3: "apply_r_upd (\<Delta>t, \<Delta>r, rs, \<Delta>f, rew\<^sub>m\<^sub>i\<^sub>r) s =
      (
        (treasury + \<Delta>t, reserves + \<Delta>r + non_distributed),
        ss,
        ((utxo, deps, fees + \<Delta>f, up), ((stk_creds, (rewards \<union>\<^sub>+ rs) \<union>\<^sub>+ update\<^sub>r\<^sub>w\<^sub>d, {$$}), pstate)),
        ppm
      )"
      and f4: "non_distributed =
        (\<Sum>k \<in> fmdom' (fmdom' stk_creds \<lhd>/ rew\<^sub>m\<^sub>i\<^sub>r). (fmdom' stk_creds \<lhd>/ rew\<^sub>m\<^sub>i\<^sub>r) $$! k)"
      and f5: "rew'\<^sub>m\<^sub>i\<^sub>r = fmdom' stk_creds \<lhd> rew\<^sub>m\<^sub>i\<^sub>r"
      and f6: "update\<^sub>r\<^sub>w\<^sub>d = fmap_of_list [(addr_rwd hk, val). (hk, val) \<leftarrow> sorted_list_of_fmap rew'\<^sub>m\<^sub>i\<^sub>r]"
      and f7: "unregistered = fmdom' stk_creds \<lhd>/ rew\<^sub>m\<^sub>i\<^sub>r"
    by (metis apply_r_upd.simps)
  then have "val_epoch_state (apply_r_upd (create_r_upd b s) s) =
    treasury + reserves + val_utxo utxo + deps + fees + val_map rewards + \<Delta>t + \<Delta>r + non_distributed
    + \<Delta>f + val_map rs + val_map update\<^sub>r\<^sub>w\<^sub>d"
  proof -
    from f2 and f3 have "val_epoch_state (apply_r_upd (create_r_upd b s) s) =
      val_acnt (treasury + \<Delta>t, reserves + \<Delta>r + non_distributed)
      + val_ledger_state (
        (utxo, deps, fees + \<Delta>f, up), ((stk_creds, (rewards \<union>\<^sub>+ rs) \<union>\<^sub>+ update\<^sub>r\<^sub>w\<^sub>d, {$$}), pstate))"
      by simp
    then have "val_epoch_state (apply_r_upd (create_r_upd b s) s) =
      (treasury + \<Delta>t) + (reserves + \<Delta>r + non_distributed) + val_utxo utxo + deps + (fees + \<Delta>f)
      + val_map ((rewards \<union>\<^sub>+ rs) \<union>\<^sub>+ update\<^sub>r\<^sub>w\<^sub>d)"
      by auto
    moreover have "val_map ((rewards \<union>\<^sub>+ rs) \<union>\<^sub>+ update\<^sub>r\<^sub>w\<^sub>d) =
      val_map rewards + val_map rs + val_map update\<^sub>r\<^sub>w\<^sub>d"
      using val_map_union_plus by metis
    ultimately show ?thesis
      by linarith
  qed
  moreover have "\<Delta>t + \<Delta>r + non_distributed + \<Delta>f + val_map rs + val_map update\<^sub>r\<^sub>w\<^sub>d = 0"
  proof (cases ss)
    case (fields pstake\<^sub>m\<^sub>a\<^sub>r\<^sub>k pstake\<^sub>s\<^sub>e\<^sub>t pstake\<^sub>g\<^sub>o pools_ss fee_ss)
    from f1 and fields have "s =
      (
        (treasury, reserves),
        (pstake\<^sub>m\<^sub>a\<^sub>r\<^sub>k, pstake\<^sub>s\<^sub>e\<^sub>t, pstake\<^sub>g\<^sub>o, pools_ss, fee_ss),
        ((utxo, deps, fees, up), (stk_creds, rewards, i\<^sub>r\<^sub>w\<^sub>d), pstate),
        ppm
      )"
      by simp
    then obtain \<Delta>t\<^sub>1 \<Delta>t\<^sub>2 \<Delta>r' \<Delta>r\<^sub>l rs' rewards\<^sub>m\<^sub>i\<^sub>r registered unregistered' reward_pot R
      where "create_r_upd b s = (\<Delta>t\<^sub>1 + \<Delta>t\<^sub>2, -\<Delta>r', rs', -fee_ss, registered)"
      and "unregistered' = fmdom' stk_creds \<lhd>/ i\<^sub>r\<^sub>w\<^sub>d"
      and "registered = i\<^sub>r\<^sub>w\<^sub>d --\<^sub>f unregistered'"
      and "rewards\<^sub>m\<^sub>i\<^sub>r = (\<Sum> k \<in> fmdom' registered. registered $$! k)"
      and "reward_pot = fee_ss + \<Delta>r\<^sub>l"
      and "R = reward_pot - \<Delta>t\<^sub>1"
      and "\<Delta>t\<^sub>2 = R - (\<Sum> k \<in> fmdom' rs'. rs' $$! k)"
      and "\<Delta>r' = \<Delta>r\<^sub>l + rewards\<^sub>m\<^sub>i\<^sub>r"
      by (metis create_r_upd.simps prod.exhaust_sel that)
    with f1 and f2 and fields have "rs' = rs" and "\<Delta>r' = -\<Delta>r" and "\<Delta>t = \<Delta>t\<^sub>1 + \<Delta>t\<^sub>2"
      and "\<Delta>f = -fee_ss" and "registered = rew\<^sub>m\<^sub>i\<^sub>r"
      by auto
    with \<open>R = reward_pot - \<Delta>t\<^sub>1\<close> and \<open>\<Delta>t\<^sub>2 = R - val_map rs'\<close> and \<open>reward_pot = fee_ss + \<Delta>r\<^sub>l\<close>
    have "\<Delta>t\<^sub>1 + \<Delta>t\<^sub>2 - \<Delta>r\<^sub>l + val_map rs - fee_ss = 0"
      by simp
    from \<open>\<Delta>t = \<Delta>t\<^sub>1 + \<Delta>t\<^sub>2\<close> have "\<Delta>t + \<Delta>r + non_distributed + \<Delta>f + val_map rs + val_map update\<^sub>r\<^sub>w\<^sub>d =
      \<Delta>t\<^sub>1 + \<Delta>t\<^sub>2 + \<Delta>r + non_distributed + \<Delta>f + val_map rs + val_map update\<^sub>r\<^sub>w\<^sub>d"
      by simp
    also from \<open>\<Delta>r' = \<Delta>r\<^sub>l + rewards\<^sub>m\<^sub>i\<^sub>r\<close> and \<open>\<Delta>r' = -\<Delta>r\<close> and \<open>rewards\<^sub>m\<^sub>i\<^sub>r = val_map registered\<close>
    have "\<dots> = \<Delta>t\<^sub>1 + \<Delta>t\<^sub>2 - \<Delta>r\<^sub>l - val_map registered + non_distributed + \<Delta>f + val_map rs
      + val_map update\<^sub>r\<^sub>w\<^sub>d"
      by simp
    also from \<open>\<Delta>f = -fee_ss\<close> have "\<dots> = \<Delta>t\<^sub>1 + \<Delta>t\<^sub>2 - \<Delta>r\<^sub>l + val_map rs - fee_ss - val_map registered
      + non_distributed + val_map update\<^sub>r\<^sub>w\<^sub>d"
      by simp
    also from \<open>\<Delta>t\<^sub>1 + \<Delta>t\<^sub>2 - \<Delta>r\<^sub>l + val_map rs - fee_ss = 0\<close> have "\<dots> =
      - val_map registered + non_distributed + val_map update\<^sub>r\<^sub>w\<^sub>d"
      by simp
    also have "\<dots> = 0"
    proof -
      have "val_map registered = val_map update\<^sub>r\<^sub>w\<^sub>d + non_distributed"
      proof -
        from f6 and assms(1,2) have "val_map rew'\<^sub>m\<^sub>i\<^sub>r = val_map update\<^sub>r\<^sub>w\<^sub>d"
          by (simp add: val_map_fmap_of_list)
        moreover from f4 and f7 have "val_map unregistered = non_distributed"
          by simp
        ultimately have *: "val_map rew'\<^sub>m\<^sub>i\<^sub>r + val_map unregistered =
          val_map update\<^sub>r\<^sub>w\<^sub>d + non_distributed"
          by simp
        from \<open>registered = rew\<^sub>m\<^sub>i\<^sub>r\<close> have "val_map registered = val_map rew\<^sub>m\<^sub>i\<^sub>r"
          by simp
        also from f5 and f7 have "\<dots> = val_map rew'\<^sub>m\<^sub>i\<^sub>r + val_map unregistered"
          using val_map_split by (metis add.commute)
        finally show ?thesis
          using * by simp
      qed
      then show ?thesis
        by simp
  qed
    finally show ?thesis .
  qed
  moreover have "val_epoch_state s =
    treasury + reserves + val_utxo utxo + deps + fees + val_map rewards"
    using f1 by simp
  ultimately show ?thesis
    by simp
qed

fun val_utxow_state :: "utxo_state \<Rightarrow> coin" where
  "val_utxow_state s = val_utxo_state s"

lemma utxow_value_preservation:
  assumes "e \<turnstile> s \<rightarrow>\<^bsub>UTXOW\<^esub>{tx} s'"
  shows "val_utxow_state s + wbalance (txwdrls tx) = val_utxow_state s'"
proof -
  from assms show ?thesis
  proof cases
    case utxo_wit
    from \<open>e \<turnstile> s \<rightarrow>\<^bsub>UTXO\<^esub>{tx} s'\<close> have "val_utxo_state s + wbalance (txwdrls tx) = val_utxo_state s'"
      using utxo_value_preservation by simp
    then have "val_utxow_state s' = val_utxow_state s + wbalance (txwdrls tx)"
      using val_utxow_state.simps by simp
    then show ?thesis ..
  qed
qed

lemma ledger_value_preservation:
  assumes "e \<turnstile> s \<rightarrow>\<^bsub>LEDGER\<^esub>{tx} s'"
  shows "val_ledger_state s = val_ledger_state s'"
proof -
  from assms show ?thesis
  proof cases
    case (ledger slot dpstate dpstate' pp utxo_st utxo_st' tx_ix reserves)
    from \<open>(slot, pp, undefined, undefined, undefined) \<turnstile> utxo_st \<rightarrow>\<^bsub>UTXOW\<^esub>{tx} utxo_st'\<close>
    have "val_utxo_state utxo_st' = val_utxo_state utxo_st + wbalance (txwdrls tx)"
      using utxow_value_preservation by simp
    moreover from \<open>(slot, tx) \<turnstile> dpstate \<rightarrow>\<^bsub>DELEGS\<^esub>{txcerts tx} dpstate'\<close>
    have "val_delegs_state dpstate = val_delegs_state dpstate' + wbalance (txwdrls tx)"
      using delegs_value_preservation by simp
    ultimately show ?thesis using val_ledger_state.simps
      by (simp add: \<open>s = (utxo_st, dpstate)\<close> \<open>s' = (utxo_st', dpstate')\<close>) 
  qed
qed

fun val_ledgers_state :: "l_state \<Rightarrow> coin" where
  "val_ledgers_state ls = val_ledger_state ls"

lemma ledgers_value_preservation:
  assumes "e \<turnstile> s \<rightarrow>\<^bsub>LEDGERS\<^esub>{\<Gamma>} s'"
  shows "val_ledgers_state s = val_ledgers_state s'"
  using assms
proof (induction \<Gamma> arbitrary: s' rule: rev_induct)
  case Nil
  from \<open>e \<turnstile> s \<rightarrow>\<^bsub>LEDGERS\<^esub>{[]} s'\<close> show ?case
    by cases simp_all
next
  case (snoc c \<Gamma>)
  from \<open>e \<turnstile> s \<rightarrow>\<^bsub>LEDGERS\<^esub>{\<Gamma> @ [c]} s'\<close> show ?case
  proof cases
    case seq_ledger_base
    then show ?thesis
      by simp
  next
    case (seq_ledger_ind slot pp reserves \<Gamma>' s'' c')
    from \<open>(slot, pp, reserves) \<turnstile> s \<rightarrow>\<^bsub>LEDGERS\<^esub>{\<Gamma>'} s''\<close> and snoc.IH and \<open>e = (slot, pp, reserves)\<close>
      and \<open>\<Gamma> @ [c] = \<Gamma>' @ [c']\<close> have "val_ledgers_state s = val_ledgers_state s''"
      by simp
    moreover from \<open>(slot, length \<Gamma>' - 1, pp, reserves) \<turnstile> s'' \<rightarrow>\<^bsub>LEDGER\<^esub>{c'} s'\<close>
    have "val_ledger_state s'' = val_ledger_state s'"
      using ledger_value_preservation by simp
    ultimately show ?thesis
      by simp
  qed
qed

fun val_snap_state :: "snapshot_state \<Rightarrow> coin" where
  "val_snap_state (_, utxo_st) = val_utxo_state utxo_st"

lemma snap_value_preservation:
  assumes "e \<turnstile> s \<rightarrow>\<^bsub>SNAP\<^esub>{\<epsilon>} s'"
  shows "val_snap_state s = val_snap_state s'"
proof -
  from assms show ?thesis
  proof cases
    case (snapshot stk_creds _ _ dstate stpools pool_params _ pstate stake utxo delegations slot
        oblg pp decayed deps pstake\<^sub>m\<^sub>a\<^sub>r\<^sub>k pstake\<^sub>s\<^sub>e\<^sub>t pstake\<^sub>g\<^sub>o pools_ss fee_ss fees up)
    from \<open>s' =
      (
        ((stake, delegations), pstake\<^sub>m\<^sub>a\<^sub>r\<^sub>k, pstake\<^sub>s\<^sub>e\<^sub>t, pool_params, fees + decayed),
        (utxo, oblg, fees + decayed, up)
      )\<close> have "val_snap_state s' = val_utxo_state (utxo, oblg, fees + decayed, up)"
      by simp
    also have "\<dots> = val_utxo utxo + oblg + (fees + decayed)"
      by simp
    also from \<open>decayed = deps - oblg\<close> have "\<dots> = val_utxo utxo + deps + fees"
      by simp
    also have "\<dots> = val_utxo_state (utxo, deps, fees, up)"
      by simp
    also from \<open>s = ((pstake\<^sub>m\<^sub>a\<^sub>r\<^sub>k, pstake\<^sub>s\<^sub>e\<^sub>t, pstake\<^sub>g\<^sub>o, pools_ss, fee_ss), (utxo, deps, fees, up))\<close>
    have "\<dots> = val_snap_state s"
      by simp
    finally show ?thesis ..
  qed
qed

fun val_newpp_state :: "new_p_param_state \<Rightarrow> coin" where
  "val_newpp_state (utxo_st, acnt, _) = val_utxo_state utxo_st + val_acnt acnt"

lemma newpp_value_preservation:
  assumes "e \<turnstile> s \<rightarrow>\<^bsub>NEWPP\<^esub>{\<epsilon>} s'"
  shows "val_newpp_state s = val_newpp_state s'"
proof -
  from assms show ?thesis
  proof cases
    case (new_proto_param_accept _ pp\<^sub>n\<^sub>e\<^sub>w treasury reserves acnt pp _ _ oblg\<^sub>c\<^sub>u\<^sub>r oblg\<^sub>n\<^sub>e\<^sub>w diff utxo deps
        fees pup aup favs avs utxo_st utxo_st' acnt')
    from \<open>s' = (utxo_st', acnt', pp\<^sub>n\<^sub>e\<^sub>w)\<close> and \<open>acnt' = (treasury, reserves + diff)\<close>
    have "val_newpp_state s' =
      val_utxo_state utxo_st' + val_coin treasury + val_coin (reserves + diff)"
      by simp
    also from \<open>utxo_st' = (utxo, oblg\<^sub>n\<^sub>e\<^sub>w, fees, {$$}, aup, favs, avs)\<close> have "\<dots> =
      val_utxo utxo + oblg\<^sub>n\<^sub>e\<^sub>w + fees + val_coin treasury + val_coin (reserves + diff)"
      by simp
    also from \<open>diff = oblg\<^sub>c\<^sub>u\<^sub>r - oblg\<^sub>n\<^sub>e\<^sub>w\<close> have "\<dots> =
      val_utxo utxo + oblg\<^sub>c\<^sub>u\<^sub>r - diff + fees + val_coin treasury + val_coin (reserves + diff)"
      by simp
    also have "\<dots> = val_utxo utxo + oblg\<^sub>c\<^sub>u\<^sub>r + fees + treasury + reserves"
      by simp
    also from \<open>deps = oblg\<^sub>c\<^sub>u\<^sub>r\<close> have "\<dots> = val_utxo utxo + deps + fees + treasury + reserves"
      by simp
    also from \<open>(utxo, deps, fees, pup, aup, favs, avs) = utxo_st\<close> have "\<dots> =
      val_utxo_state utxo_st + treasury + reserves"
      by auto
    also from \<open>(treasury, reserves) = acnt\<close> and \<open>s = (utxo_st, acnt, pp)\<close> have "\<dots> =
      val_newpp_state s"
      by auto
    finally show ?thesis ..
  next
    case (new_proto_param_denied_1 _ _ treasury reserves acnt pp _ _ utxo oblg fees pup aup favs avs
        utxo_st utxo_st')
    from \<open>s' = (utxo_st', acnt, pp)\<close> and \<open>(treasury, reserves) = acnt\<close>
    have "val_newpp_state s' = val_utxo_state utxo_st' + val_coin treasury + val_coin reserves"
      by auto
    also from \<open>utxo_st' = (utxo, oblg, fees, {$$}, aup, favs, avs)\<close> have "\<dots> =
      val_utxo utxo + oblg + fees + val_coin treasury + val_coin reserves"
      by simp
    also from \<open>(utxo, oblg, fees, pup, aup, favs, avs) = utxo_st\<close> have "\<dots> =
      val_utxo_state utxo_st + treasury + reserves"
      by auto
    also from \<open>(treasury, reserves) = acnt\<close> and \<open>s = (utxo_st, acnt, pp)\<close> have "\<dots> =
      val_newpp_state s"
      by auto
    finally show ?thesis ..
  next
    case (new_proto_param_denied_2 _ utxo oblg fees pup aup favs avs utxo_st utxo_st' _ _ acnt pp)
    from \<open>s' = (utxo_st', acnt, pp)\<close> have "val_newpp_state s' =
      val_utxo_state utxo_st' + val_acnt acnt"
      by simp
    also from \<open>utxo_st' = (utxo, oblg, fees, {$$}, aup, favs, avs)\<close> have "\<dots> =
      val_utxo utxo + val_coin oblg + val_coin fees + val_acnt acnt"
      by simp
    also from \<open>(utxo, oblg, fees, pup, aup, favs, avs) = utxo_st\<close> and \<open>s = (utxo_st, acnt, pp)\<close>
    have "\<dots> = val_newpp_state s"
      by auto
    finally show ?thesis ..
  qed
qed

lemma epoch_value_preservation:
  assumes "\<turnstile> s \<rightarrow>\<^bsub>EPOCH\<^esub>{\<epsilon>} s'"
  shows "val_epoch_state s = val_epoch_state s'"
proof -
  from assms show ?thesis
  proof cases
    case (epoch utxo_st dstate pstate ls pp ss ss' utxo_st' acnt utxo_st'' acnt' dstate' pstate'
        _ _ _ pup _ _ _ pp\<^sub>n\<^sub>e\<^sub>w utxo_st''' acnt'' pp' ls')
    from \<open>(pp\<^sub>n\<^sub>e\<^sub>w, dstate', pstate') \<turnstile> (utxo_st'', acnt', pp) \<rightarrow>\<^bsub>NEWPP\<^esub>{\<epsilon>} (utxo_st''', acnt'', pp')\<close>
    have "val_newpp_state (utxo_st'', acnt', pp) = val_newpp_state (utxo_st''', acnt'', pp')"
      using newpp_value_preservation by fast
    then have f1: "val_utxo_state utxo_st'' + val_acnt acnt' =
      val_utxo_state utxo_st''' + val_acnt acnt''"
      by simp
    moreover
    from \<open>pp \<turnstile> (utxo_st', acnt, dstate, pstate) \<rightarrow>\<^bsub>POOLREAP\<^esub>{\<epsilon>} (utxo_st'', acnt', dstate', pstate')\<close>
    have "val_poolreap_state (utxo_st', acnt, dstate, pstate)
      = val_poolreap_state (utxo_st'', acnt', dstate', pstate')"
      using poolreap_value_preservation by presburger
    then have f3: "val_utxo_state utxo_st' + val_acnt acnt + val_deleg_state dstate =
      val_utxo_state utxo_st'' + val_acnt acnt' + val_deleg_state dstate'"
      by simp
    moreover from \<open>(pp, dstate, pstate) \<turnstile> (ss, utxo_st) \<rightarrow>\<^bsub>SNAP\<^esub>{\<epsilon>} (ss', utxo_st')\<close>
    have "val_snap_state (ss, utxo_st) = val_snap_state (ss', utxo_st')"
      using snap_value_preservation by presburger
    then have f2: "val_utxo_state utxo_st = val_utxo_state utxo_st'"
      by simp
    moreover have f4: "val_epoch_state s' =
      val_acnt acnt'' + val_utxo_state utxo_st''' + val_deleg_state dstate'"
    proof -
      from \<open>s' = (acnt'', ss', ls', pp')\<close> have "val_epoch_state s' =
      val_acnt acnt'' + val_ledger_state ls'"
        by simp
      also from \<open>ls' = (utxo_st''', (dstate', pstate'))\<close> have "\<dots> =
      val_acnt acnt'' + val_utxo_state utxo_st''' + val_delegs_state (dstate', pstate')"
        by simp
      finally show ?thesis
        by simp
    qed
    ultimately show ?thesis
    proof -
      from f4 have "val_epoch_state s' =
        (val_acnt acnt'' + val_utxo_state utxo_st''') + val_deleg_state dstate'"
        by simp
      also from f1 have "\<dots> = (val_acnt acnt' + val_utxo_state utxo_st'') + val_deleg_state dstate'"
        by simp
      also from f3 have "\<dots> = val_acnt acnt + val_utxo_state utxo_st' + val_deleg_state dstate"
        by simp
      also from f2 have "\<dots> = val_utxo_state utxo_st + val_acnt acnt + val_deleg_state dstate"
        by simp
      also from \<open>(utxo_st, (dstate, pstate)) = ls\<close> have "\<dots> = val_acnt acnt + val_ledger_state ls"
        by auto
      finally show ?thesis using \<open>s = (acnt, ss, ls, pp)\<close>
        by simp
    qed
  qed
qed

fun val_new_epoch_state :: "new_epoch_state \<Rightarrow> coin" where
  "val_new_epoch_state (_, _, _, es, _, _, _) = val_epoch_state es"

lemma newepoch_value_preservation:
  assumes "e \<turnstile> s \<rightarrow>\<^bsub>NEWEPOCH\<^esub>{\<epsilon>} s'"
  and "inj addr_rwd"
  and "mono addr_rwd"
  shows "val_new_epoch_state s = val_new_epoch_state s'"
proof -
  from assms show ?thesis
  proof cases
    case (new_epoch e\<^sub>l ru ru' b\<^sub>p\<^sub>r\<^sub>e\<^sub>v es es' pd' osched' b\<^sub>c\<^sub>u\<^sub>r pd osched)
    have "val_epoch_state es' = val_epoch_state es"
    proof -
      from \<open>inj addr_rwd\<close> and \<open>mono addr_rwd\<close> and \<open>ru' = create_r_upd b\<^sub>p\<^sub>r\<^sub>e\<^sub>v es\<close> have "
        val_epoch_state (apply_r_upd ru' es) = val_epoch_state es"
        using reward_update_value_preservation by presburger
      with \<open>\<turnstile> apply_r_upd ru' es \<rightarrow>\<^bsub>EPOCH\<^esub>{\<epsilon>} es'\<close> show ?thesis
        using epoch_value_preservation by simp
    qed
    with \<open>s = (e\<^sub>l, b\<^sub>p\<^sub>r\<^sub>e\<^sub>v, b\<^sub>c\<^sub>u\<^sub>r, es, ru, pd, osched)\<close> and
      \<open>s' = (\<epsilon>, b\<^sub>c\<^sub>u\<^sub>r, {$$}, es', None, pd', osched')\<close> show ?thesis
      by simp
  next
    case not_new_epoch
    then show ?thesis by simp
  next
    case no_reward_update
    then show ?thesis by simp
  qed
qed

lemma tick_value_preservation:
  assumes "gkeys \<turnstile> nes \<rightarrow>\<^bsub>TICK\<^esub>{s} nes'"
  and "inj addr_rwd"
  and "mono addr_rwd"
  shows "val_new_epoch_state nes = val_new_epoch_state nes'"
proof -
  from assms show ?thesis
  proof cases
    case (tick nes'' _ b\<^sub>p\<^sub>r\<^sub>e\<^sub>v _ es _ _ _ e\<^sub>l'' b\<^sub>p\<^sub>r\<^sub>e\<^sub>v'' b\<^sub>c\<^sub>u\<^sub>r'' es'' ru' pd'' osched'' ru'')
    from assms and \<open>(s, gkeys) \<turnstile> nes \<rightarrow>\<^bsub>NEWEPOCH\<^esub>{epoch s} nes''\<close> have "
      val_new_epoch_state nes = val_new_epoch_state nes''"
      using newepoch_value_preservation by simp
    also from \<open>nes' = (e\<^sub>l'', b\<^sub>p\<^sub>r\<^sub>e\<^sub>v'', b\<^sub>c\<^sub>u\<^sub>r'', es'', ru'', pd'', osched'')\<close> and
      \<open>(e\<^sub>l'', b\<^sub>p\<^sub>r\<^sub>e\<^sub>v'', b\<^sub>c\<^sub>u\<^sub>r'', es'', ru', pd'', osched'') = nes''\<close> have "
      \<dots> = val_new_epoch_state nes'"
      by auto
    finally show ?thesis .
  qed
qed

fun val_b_body_state :: "b_body_state \<Rightarrow> coin" where
  "val_b_body_state (ls, _) = val_ledgers_state ls"

lemma bbody_value_preservation:
  assumes "e \<turnstile> s \<rightarrow>\<^bsub>BBODY\<^esub>{block} s'"
  shows "val_b_body_state s = val_b_body_state s'"
proof -
  from assms show ?thesis
  proof cases
    case (block_body txs bhb hk pp reserves ls ls' oslots b)
    from \<open>(bslot bhb, pp, reserves) \<turnstile> ls \<rightarrow>\<^bsub>LEDGERS\<^esub>{txs} ls'\<close> have "
      val_ledgers_state ls = val_ledgers_state ls'"
      using ledgers_value_preservation by simp
    with \<open>s = (ls, b)\<close> and \<open>s' = (ls', incr_blocks (bslot bhb \<in> oslots) hk b)\<close> have "
      val_b_body_state s = val_b_body_state s'"
      by simp
    then show ?thesis .
  qed
qed

fun val_chain_state :: "chain_state \<Rightarrow> coin" where
  "val_chain_state s = val_new_epoch_state (fst s)"

theorem chain_value_preservation:
  assumes "e \<turnstile> s \<rightarrow>\<^bsub>CHAIN\<^esub>{block} s'"
  and "inj addr_rwd"
  and "mono addr_rwd"
  shows "val_chain_state s = val_chain_state s'"
proof -
  from assms show ?thesis
  proof cases
    case (chain bh bhb gkeys nes slot _ _ _ _ _ _ pp _ _ _ nes' _ _ b\<^sub>c\<^sub>u\<^sub>r es _ _ osched acnt _ ls pp'
        _ reserves ls' b'\<^sub>c\<^sub>u\<^sub>r nes'' cs' \<eta>'\<^sub>0 \<eta>'\<^sub>v \<eta>'\<^sub>c \<eta>'\<^sub>h h' s'\<^sub>l cs \<eta>\<^sub>0 \<eta>\<^sub>v \<eta>\<^sub>c \<eta>\<^sub>h h s\<^sub>l)
    from \<open>gkeys \<turnstile> nes \<rightarrow>\<^bsub>TICK\<^esub>{slot} nes'\<close> and \<open>inj addr_rwd\<close> and \<open>mono addr_rwd\<close> have "
      val_new_epoch_state nes = val_new_epoch_state nes'"
      using tick_value_preservation by simp
    moreover from \<open>(fmdom' osched, pp', reserves) \<turnstile> (ls, b\<^sub>c\<^sub>u\<^sub>r) \<rightarrow>\<^bsub>BBODY\<^esub>{block} (ls', b'\<^sub>c\<^sub>u\<^sub>r)\<close> have "
      val_ledgers_state ls = val_ledgers_state ls'"
      using bbody_value_preservation by (blast dest: val_b_body_state.elims)
    ultimately show ?thesis
      using
        \<open>s = (nes, cs, \<eta>\<^sub>0, \<eta>\<^sub>v, \<eta>\<^sub>c, \<eta>\<^sub>h, h, s\<^sub>l)\<close> and
        \<open>(_, _, b\<^sub>c\<^sub>u\<^sub>r, es, _, _, osched) = nes'\<close> and
        \<open>(acnt, _, ls, pp') = es\<close> and
        \<open>nes'' = update_nes nes' b'\<^sub>c\<^sub>u\<^sub>r ls'\<close> and
        \<open>s' = (nes'', cs', \<eta>'\<^sub>0, \<eta>'\<^sub>v, \<eta>'\<^sub>c, \<eta>'\<^sub>h, h', s'\<^sub>l)\<close>
      by auto
  qed
qed

end
