section \<open> Properties \<close>

theory Properties
  imports UTxO Delegation
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
  "val_utxo_state (utxo, deps, fees, _) = val_utxo utxo + deps + fees"

lemma val_map_add:
  assumes "k \<notin> fmdom' m"
  shows "val_map m(k $$:= c) = val_map m + c"
proof -
  let ?m' = "m(k $$:= c)"
  have "val_map ?m' = (\<Sum>k\<^sub>i \<in> fmdom' m \<union> {k}. ?m' $$! k\<^sub>i)"
    by simp
  also from assms have "\<dots> = (\<Sum>k\<^sub>i \<in> fmdom' m. ?m' $$! k\<^sub>i) + (?m' $$! k)"
    by simp
  also have "\<dots> = (\<Sum>k\<^sub>i \<in> fmdom' m. ?m' $$! k\<^sub>i) + c"
    by simp
  also from assms have "\<dots> = (\<Sum>k\<^sub>i \<in> fmdom' m. m $$! k\<^sub>i) + c"
    by (metis (no_types, lifting) fmupd_lookup sum.cong)
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
    moreover from fmupd.prems have "k \<notin> fmdom' m\<^sub>1"
      by auto
    moreover from fmupd.hyps have "k \<notin> fmdom' m\<^sub>2"
      by (simp add: fmdom'_notI)
    ultimately have "k \<notin> fmdom' (m\<^sub>1 ++\<^sub>f m\<^sub>2)"
      by simp
    then show ?thesis
      using val_map_add by metis
  qed
  also from fmupd.prems and fmupd.IH have "\<dots> = val_map m\<^sub>1 + val_map m\<^sub>2 + c"
    by simp
  also have "\<dots> = val_map m\<^sub>1 + val_map (m\<^sub>2(k $$:= c))"
  proof -
    from fmupd.hyps have "k \<notin> fmdom' m\<^sub>2"
      by (simp add: fmdom'_notI)
    then show ?thesis
      using val_map_add by (metis (full_types) add.assoc)
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
        have "fmdom'(txins tx \<lhd>/ utxo) \<inter> fmdom' (outs tx) = {}"
          using txins_outs_exc by blast
        then show ?thesis
          using val_map_union by (smt fmdom'_map sum.cong)
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
  "val_deleg_state rewards = val_map rewards"

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
    case (deleg_reg hk)
    from \<open>s' = s \<union>\<^sub>\<leftarrow> {addr_rwd hk $$:= 0}\<close>
    have *: "val_deleg_state s' = val_deleg_state (s \<union>\<^sub>\<leftarrow> {addr_rwd hk $$:= 0})"
      by simp
    then show ?thesis
    proof (cases "addr_rwd hk \<in> fmdom' s")
      case True
      then have "s \<union>\<^sub>\<leftarrow> {addr_rwd hk $$:= 0} = s"
        by simp
      then have "val_deleg_state (s \<union>\<^sub>\<leftarrow> {addr_rwd hk $$:= 0}) = val_deleg_state s"
        by simp
      with * show ?thesis
        by simp
    next
      case False
      then have **: "s \<union>\<^sub>\<leftarrow> {addr_rwd hk $$:= 0} = s ++\<^sub>f {addr_rwd hk $$:= 0}"
        by simp
      with False have "fmdom' s \<inter> fmdom' {addr_rwd hk $$:= 0} = {}"
        by simp
      then have "val_map (s ++\<^sub>f {addr_rwd hk $$:= 0}) = val_map s + val_map {addr_rwd hk $$:= 0}"
        using val_map_union by blast
      also have "\<dots> = val_map s + 0"
        by simp
      finally have "val_deleg_state (s ++\<^sub>f {addr_rwd hk $$:= 0}) = val_deleg_state s"
        by auto
      with * and ** show ?thesis
        by presburger
    qed
  next
    case (deleg_dereg hk)
    then have "val_deleg_state s' = val_map s'"
      by simp
    also from \<open>s' = {addr_rwd hk} \<lhd>/ s\<close> have "\<dots> = val_map ({addr_rwd hk} \<lhd>/ s)"
      by simp
    also from \<open>s $$ (addr_rwd hk) = Some 0\<close> have "\<dots> = val_map s - 0"
      using val_map_dom_exc_singleton by fast
    finally show ?thesis
      by simp
  qed
qed

fun val_delegs_state :: "d_p_state \<Rightarrow> coin" where
  "val_delegs_state (rewards, _) = val_deleg_state rewards"

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
      using val_map_add by (metis fmdom'_notI)
  qed
  finally show ?case .
qed

lemma fmran_fmmap_const:
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
      by (smt dom_res_singleton dom_res_singleton fmadd_empty(1) fmadd_empty(1) fmadd_empty(2) fmfilter_fmmap fmlookup_map fmmap_add fmupd_alt_def fmupd_lookup option.simps(9))
    then have "fmran (fmmap (\<lambda>_. v) m(k' $$:= v')) = fmran (fmmap (\<lambda>_. v) m ++\<^sub>f {k' $$:= v})"
      by simp
    also have "\<dots> = fmran (fmmap (\<lambda>_. v) m) |\<union>| fmran {k' $$:= v}"
    proof -
      from \<open>m $$ k' = None\<close> have "fmdom (fmmap (\<lambda>_. v) m) |\<inter>| fmdom {k' $$:= v} = {||}"
        by (simp add: fmdom_notI)
      with \<open>m $$ k' = None\<close> show ?thesis
        by (smt finter_absorb finter_commute finter_funion_distrib2 fmadd_restrict_right_dom fmap_singleton_comm fmdom_add fmdom_map fmdom_notD fmdom_notI fmimage_dom fmimage_union fmran_restrict_fset)
    qed
    also from True and fmupd.IH have "\<dots> = {|v|} |\<union>| fmran {k' $$:= v}"
      by simp
    finally show ?thesis
      by (simp add: fmran_singleton)
  next
    case False
    then have "fmmap (\<lambda>_. v) m(k' $$:= v') = {k' $$:= v}"
      by (smt dom_res_singleton dom_res_singleton fmadd_empty(1) fmadd_empty(1) fmadd_empty(2) fmfilter_fmmap fmlookup_map fmmap_add fmupd_alt_def fmupd_lookup option.simps(9))
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
  assumes "(slot, tx) \<turnstile> (rewards, pstate) \<rightarrow>\<^bsub>DELEGS\<^esub>{\<Gamma>} (rewards', pstate)"
  shows "val_delegs_state (rewards, pstate) =
         val_delegs_state (rewards', pstate) + wbalance (txwdrls tx)"
  using assms
proof (induction "(slot, tx)" "(rewards, pstate)" \<Gamma> "(rewards', pstate)" arbitrary: slot tx rewards
       pstate rewards' rule: delegs_sts.induct)
  case (seq_delg_base wdrls tx rewards rewards' slot pstate)
  have "val_delegs_state (rewards, pstate) = val_map rewards"
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
    finally show ?case
      by simp
next
  case (seq_delg_ind slot tx \<Gamma> dpstate' c)
  from \<open>slot \<turnstile> dpstate' \<rightarrow>\<^bsub>DELPL\<^esub>{c} (rewards', pstate)\<close> have "snd dpstate' = pstate"
    using delpl_sts.simps by auto
  with seq_delg_ind.hyps(2) have "val_delegs_state (rewards, pstate) =
    val_delegs_state (fst dpstate', pstate) + val_map (txwdrls tx)"
    by auto
  moreover have "val_deleg_state (fst dpstate') = val_deleg_state rewards'"
  proof -
    from \<open>slot \<turnstile> dpstate' \<rightarrow>\<^bsub>DELPL\<^esub>{c} (rewards', pstate)\<close>
    have "slot \<turnstile> (fst dpstate') \<rightarrow>\<^bsub>DELEG\<^esub>{c} rewards'"
      using delpl_sts.simps by auto
    then show ?thesis
      using deleg_value_preservation by simp
  qed
  ultimately show ?case
    by simp
qed

end
