section \<open> Properties \<close>

theory Properties
  imports UTxO
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

lemma val_map_union:
  assumes "fmdom' m\<^sub>1 \<inter> fmdom' m\<^sub>2 = {}"
  shows "val_map (m\<^sub>1 ++\<^sub>f m\<^sub>2) = val_map m\<^sub>1 + val_map m\<^sub>2"
  using assms
proof (induction m\<^sub>2 arbitrary: m\<^sub>1 rule: fmap_induct)
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
      using val_map_add by (metis sum.cong)
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
  \<^item> The proof in the document applies lemmas 15.3 and 15.4 on \<open>utxo\<close>'s,
    however this is incorrect since the range of \<open>utxo\<close> is not \<open>coin\<close> but
    \<open>(addr, coin)\<close>.
  \<^item> The proof in the document applies lemma 15.4 without proving its
    precondition, which is not trivial to formalize.
\<close>
lemma utxo_value_preservation:
  assumes "\<Gamma> \<turnstile> s \<rightarrow>\<^bsub>UTXO\<^esub>{tx} s'"
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

lemma delegation_value_preservation:
  assumes "\<Gamma> \<turnstile> s \<rightarrow>\<^bsub>DELEG\<^esub>{c} s'"
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

end
