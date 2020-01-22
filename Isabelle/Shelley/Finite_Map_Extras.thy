section \<open> Extra Features for Finite Maps \<close>

theory Finite_Map_Extras
  imports "HOL-Library.Finite_Map"
begin

text \<open> Extra lemmas and syntactic sugar for \<open>fmap\<close> \<close>

abbreviation fmap_update (\<open>_'(_ $$:= _')\<close> [1000,0,0] 1000) where
  "m(k $$:= v) \<equiv> fmupd k v m"

notation fmlookup (infixl \<open>$$\<close> 999)

notation fmempty (\<open>{$$}\<close>)

abbreviation fmap_singleton (\<open>{_ $$:= _}\<close> [0, 0] 1000) where
  "{k $$:= v} \<equiv> {$$}(k $$:= v)"

abbreviation fmap_lookup_the (infixl \<open>$$!\<close> 999) where
  "m $$! k \<equiv> the (m $$ k)"

lemma fmfilter_fmsubset: "fmfilter p m \<subseteq>\<^sub>f m"
proof -
  have "\<forall>k \<in> fmdom' m. \<exists>v. (fmfilter p m) $$ k = v \<longrightarrow> m $$ k = v"
    by blast
  then show ?thesis
    by (simp add: Ball_def_raw domIff fmsubset.rep_eq map_le_def)
qed

lemma fmadd_singletons_comm:
  assumes "k\<^sub>1 \<noteq> k\<^sub>2"
  shows "{k\<^sub>1 $$:= v\<^sub>1} ++\<^sub>f {k\<^sub>2 $$:= v\<^sub>2} = {k\<^sub>2 $$:= v\<^sub>2} ++\<^sub>f {k\<^sub>1 $$:= v\<^sub>1}"
proof (intro fmap_ext)
  fix k
  consider
    (a) "k = k\<^sub>1" |
    (b) "k = k\<^sub>2" |
    (c) "k \<noteq> k\<^sub>1 \<and> k \<noteq> k\<^sub>2"
    by auto
  with assms show "({k\<^sub>1 $$:= v\<^sub>1} ++\<^sub>f {k\<^sub>2 $$:= v\<^sub>2}) $$ k = ({k\<^sub>2 $$:= v\<^sub>2} ++\<^sub>f {k\<^sub>1 $$:= v\<^sub>1}) $$ k"
    by auto
qed

lemma fmap_singleton_comm:
  assumes "m $$ k = None"
  shows "m ++\<^sub>f {k $$:= v} = {k $$:= v} ++\<^sub>f m"
  using assms
proof (induction m arbitrary: k v)
  case fmempty
  then show ?case
    by simp
next
  case (fmupd x y m)
  have "m(x $$:= y) ++\<^sub>f {k $$:= v} = m ++\<^sub>f {x $$:= y} ++\<^sub>f {k $$:= v}"
    by simp
  also from fmupd.hyps and fmupd.IH have "\<dots> = {x $$:= y} ++\<^sub>f m ++\<^sub>f {k $$:= v}"
    by simp
  also from fmupd.prems and fmupd.hyps and fmupd.IH have "\<dots> = {x $$:= y} ++\<^sub>f {k $$:= v} ++\<^sub>f m"
    by (metis fmadd_assoc fmupd_lookup)
  also have "\<dots> = {k $$:= v} ++\<^sub>f m(x $$:= y)"
  proof (cases "x \<noteq> k")
    case True
    then have "{x $$:= y} ++\<^sub>f {k $$:= v} ++\<^sub>f m = {k $$:= v} ++\<^sub>f {x $$:= y} ++\<^sub>f m"
      using fmadd_singletons_comm by metis
    also from fmupd.prems and fmupd.hyps and fmupd.IH have "\<dots> = {k $$:= v} ++\<^sub>f m ++\<^sub>f {x $$:= y}"
      by (metis fmadd_assoc)
    finally show ?thesis
      by simp
  next
    case False
    with fmupd.prems show ?thesis
      by auto
  qed
  finally show ?case .
qed

lemma fmap_disj_comm:
  assumes "fmdom' m\<^sub>1 \<inter> fmdom' m\<^sub>2 = {}"
  shows "m\<^sub>1 ++\<^sub>f m\<^sub>2 = m\<^sub>2 ++\<^sub>f m\<^sub>1"
  using assms
proof (induction m\<^sub>2 arbitrary: m\<^sub>1)
  case fmempty
  then show ?case
    by simp
next
  case (fmupd k v m\<^sub>2)
  then show ?case
  proof (cases "m\<^sub>1 $$ k = None")
    case True
    from fmupd.hyps have "m\<^sub>1 ++\<^sub>f m\<^sub>2(k $$:= v) = m\<^sub>1 ++\<^sub>f m\<^sub>2 ++\<^sub>f {k $$:= v}"
      by simp
    also from fmupd.prems and fmupd.hyps and fmupd.IH have "\<dots> = m\<^sub>2 ++\<^sub>f m\<^sub>1 ++\<^sub>f {k $$:= v}"
      by simp
    also from True have "\<dots> = m\<^sub>2 ++\<^sub>f {k $$:= v} ++\<^sub>f m\<^sub>1"
      using fmap_singleton_comm by (metis fmadd_assoc)
    finally show ?thesis
      by simp
  next
    case False
    with fmupd.prems show ?thesis
      by auto
  qed
qed

lemma fmran_singleton: "fmran {k $$:= v} = {|v|}" (* TODO: Find a nicer proof *)
proof -
  have "\<And>v'. v' |\<in>| fmran {k $$:= v} \<Longrightarrow> v' = v"
    by (metis fmdom_empty fmdom_fmupd fmdom_notD fmranE fmupd_lookup fsingleton_iff
        option.distinct(1) option.sel)
  moreover have "v |\<in>| fmran {k $$:= v}"
    by (simp add: fmranI)
  ultimately show ?thesis
    by (simp add: fsubsetI fsubset_antisym)
qed

lemma fmmap_keys_hom:
  assumes "fmdom' m\<^sub>1 \<inter> fmdom' m\<^sub>2 = {}"
  shows "fmmap_keys f (m\<^sub>1 ++\<^sub>f m\<^sub>2) = fmmap_keys f m\<^sub>1 ++\<^sub>f fmmap_keys f m\<^sub>2"
  using assms
  by (simp add: fmap_ext)

lemma map_insort_is_insort_key:
  assumes "m $$ k = None"
  shows "map (\<lambda>k'. (k', m(k $$:= v) $$! k')) (insort k xs) =
    insort_key fst (k, v) (map (\<lambda>k'. (k', m(k $$:= v) $$! k')) xs)"
  using assms by (induction xs) auto

lemma sorted_list_of_fmap_is_insort_key_fst:
  assumes "m $$ k = None"
  shows "sorted_list_of_fmap m(k $$:= v) = insort_key fst (k, v) (sorted_list_of_fmap m)"
proof -
  have "sorted_list_of_fmap m(k $$:= v) =
    map (\<lambda>k'. (k', m(k $$:= v) $$! k')) (sorted_list_of_fset (fmdom (m(k $$:= v))))"
    unfolding sorted_list_of_fmap_def ..
  also have "\<dots> = 	map (\<lambda>k'. (k', m(k $$:= v) $$! k')) (sorted_list_of_fset (finsert k (fmdom m)))"
    by simp
  also from \<open>m $$ k = None\<close> have "\<dots> =
    map (\<lambda>k'. (k', m(k $$:= v) $$! k')) (insort k (sorted_list_of_fset (fmdom m - {|k|})))"
    by (simp add: sorted_list_of_fset.rep_eq)
  also from \<open>m $$ k = None\<close> have "\<dots> =
    map (\<lambda>k'. (k', m(k $$:= v) $$! k')) (insort k (sorted_list_of_fset (fmdom m)))"
    by (simp add: fmdom_notI)
  also from \<open>m $$ k = None\<close> have "\<dots> =
    insort_key fst (k, v) (map (\<lambda>k'. (k', m(k $$:= v) $$! k')) (sorted_list_of_fset (fmdom m)))"
    using map_insort_is_insort_key by fastforce
  also have "\<dots> = insort_key fst (k, v) (map (\<lambda>k'. (k', m $$! k')) (sorted_list_of_fset (fmdom m)))"
  proof -
    from \<open>m $$ k = None\<close> have "\<And>k'. k' \<in> fmdom' m \<Longrightarrow> m(k $$:= v) $$! k' = m $$! k'"
      using fmdom'_notI by force
    moreover from \<open>m $$ k = None\<close> have "k \<notin> set (sorted_list_of_fset (fmdom m))"
      using fmdom'_alt_def and fmdom'_notI and in_set_member by force
    ultimately show ?thesis
      by (metis (mono_tags, lifting) fmdom'_alt_def map_eq_conv sorted_list_of_fset_simps(1))
  qed
  finally show ?thesis
    unfolding sorted_list_of_fmap_def by simp
qed

lemma distinct_fst_inj:
  assumes "distinct (map fst ps)"
  and "inj f"
  shows "distinct (map fst (map (\<lambda>(k, v). (f k, v)) ps))"
proof -
  have "map fst (map (\<lambda>(k, v). (f k, v)) ps) = map f (map fst ps)"
    by (induction ps) auto
  moreover from assms have "distinct (map f (map fst ps))"
    by (simp add: distinct_map inj_on_def)
  ultimately show ?thesis
    by presburger
qed

lemma distinct_sorted_list_of_fmap:
  shows "distinct (map fst (sorted_list_of_fmap m))"
  unfolding sorted_list_of_fmap_def and sorted_list_of_fset_def
  by (simp add: distinct_map inj_on_def)

lemma map_inj_pair_non_membership:
  assumes "k \<notin> set (map fst ps)"
  and "inj f"
  shows "f k \<notin> set (map fst (map (\<lambda>(k, v). (f k, v)) ps))"
  using assms by (induction ps) (simp add: member_rec(2), fastforce simp add: injD)

lemma map_insort_key_fst:
  assumes "distinct (map fst ps)"
  and "k \<notin> set (map fst ps)"
  and "inj f"
  and "mono f"
  shows "map (\<lambda>(k, v). (f k, v)) (insort_key fst (k, v) ps) =
    insort_key fst (f k, v) (map (\<lambda>(k, v). (f k, v)) ps)"
  using assms
proof (induction ps)
  case Nil
  then show ?case
    by simp
next
  let ?g = "(\<lambda>(k, v). (f k, v))"
  case (Cons p ps)
  then show ?case
  proof (cases "k \<le> fst p")
    case True
    let ?f_p = "(f (fst p), snd p)"
    have "insort_key fst (f k, v) (map ?g (p # ps)) = insort_key fst (f k, v) (?f_p # map ?g ps)"
      by (simp add: prod.case_eq_if)
    moreover from Cons.prems(4) and True have "f k \<le> f (fst p)"
      by (auto dest: monoE)
    then have "insort_key fst (f k, v) (?f_p # map ?g ps) = (f k, v) # ?f_p # map ?g ps"
      by simp
    ultimately have "insort_key fst (f k, v) (map ?g (p # ps)) = (f k, v) # ?f_p # map ?g ps"
      by simp
    moreover from True have "map ?g (insort_key fst (k, v) (p # ps)) = (f k, v) # ?f_p # map ?g ps"
      by (simp add: case_prod_beta')
    ultimately show ?thesis
      by simp
  next
    case False
    let ?f_p = "(f (fst p), snd p)"
    have "insort_key fst (f k, v) (map ?g (p # ps)) = insort_key fst (f k, v) (?f_p # map ?g ps)"
      by (simp add: prod.case_eq_if)
    moreover from \<open>mono f\<close> and False have "f (fst p) \<le> f k"
      using not_le by (blast dest: mono_invE)
    ultimately have "insort_key fst (f k, v) (map ?g (p # ps)) =
      ?f_p # insort_key fst (f k, v) (map ?g ps)"
      using False and \<open>inj f\<close> by (fastforce dest: injD)
    also from Cons.IH and Cons.prems(1,2) and assms(3,4) have "\<dots> =
      ?f_p # (map ?g (insort_key fst (k, v) ps))"
      by (fastforce simp add: member_rec(1))
    also have "\<dots> = map ?g (p # insort_key fst (k, v) ps)"
      by (simp add: case_prod_beta)
    finally show ?thesis
      using False by simp
  qed
qed

lemma map_sorted_list_of_fmap:
  assumes "inj f"
  and "mono f"
  and "m $$ k = None"
  shows "map (\<lambda>(k, v). (f k, v)) (sorted_list_of_fmap m(k $$:= v)) =
    insort_key fst (f k, v) (map (\<lambda>(k, v). (f k, v)) (sorted_list_of_fmap m))"
proof -
  let ?g = "(\<lambda>(k, v). (f k, v))"
  from \<open>m $$ k = None\<close> have "map ?g (sorted_list_of_fmap m(k $$:= v)) =
  	map ?g (insort_key fst (k, v) (sorted_list_of_fmap m))"
  	using sorted_list_of_fmap_is_insort_key_fst by fastforce
  also have "\<dots> = insort_key fst (f k, v) (map ?g (sorted_list_of_fmap m))"
  proof -
    have "distinct (map fst (sorted_list_of_fmap m))"
      by (simp add: distinct_sorted_list_of_fmap)
    moreover from \<open>m $$ k = None\<close> have "k \<notin> set (map fst (sorted_list_of_fmap m))"
      by (metis image_set map_of_eq_None_iff map_of_sorted_list)
    ultimately show ?thesis
      by (simp add: map_insort_key_fst assms(1,2))
  qed
  finally show ?thesis .
qed

lemma fmap_of_list_insort_key_fst:
  assumes "distinct (map fst ps)"
  and "k \<notin> set (map fst ps)"
  shows "fmap_of_list (insort_key fst (k, v) ps) = (fmap_of_list ps)(k $$:= v)"
  using assms
proof (induction ps)
  case Nil
  then show ?case
    by simp
next
  case (Cons p ps)
  then show ?case
  proof (cases "k \<le> fst p")
    case True
    then show ?thesis
      by simp
  next
    case False
    then have "fmap_of_list (insort_key fst (k, v) (p # ps)) =
      fmap_of_list (p # insort_key fst (k, v) ps)"
      by simp
    also have "\<dots> = (fmap_of_list (insort_key fst (k, v) ps))(fst p $$:= snd p)"
      by (metis fmap_of_list_simps(2) prod.collapse)
    also from Cons.prems(1,2) and Cons.IH have "\<dots> = (fmap_of_list ps)(k $$:= v)(fst p $$:= snd p)"
      by (fastforce simp add: member_rec(1))
    finally show ?thesis
    proof -
      assume *: "fmap_of_list (insort_key fst (k, v) (p # ps)) =
        (fmap_of_list ps)(k $$:= v)(fst p $$:= snd p)"
      from Cons.prems(2) have "k \<notin> set (fst p # map fst ps)"
        by simp
      then have **: "{k $$:= v} $$ (fst p) = None"
        by (fastforce simp add: member_rec(1))
      have "fmap_of_list (p # ps) = (fmap_of_list ps)(fst p $$:= snd p)"
        by (metis fmap_of_list_simps(2) prod.collapse)
      with * and ** show ?thesis
        using fmap_singleton_comm by (metis fmadd_fmupd fmap_of_list_simps(1,2) fmupd_alt_def)
    qed
  qed
qed

lemma fmap_of_list_insort_key_fst_map:
  assumes "inj f"
  and "m $$ k = None"
  shows "fmap_of_list (insort_key fst (f k, v) (map (\<lambda>(k, v). (f k, v)) (sorted_list_of_fmap m))) =
    (fmap_of_list (map (\<lambda>(k, v). (f k, v)) (sorted_list_of_fmap m)))(f k $$:= v)"
proof -
  let ?g = "\<lambda>(k, v). (f k, v)"
  let ?ps = "map ?g (sorted_list_of_fmap m)"
  from \<open>inj f\<close> have "distinct (map fst ?ps)"
    using distinct_fst_inj and distinct_sorted_list_of_fmap by fastforce
  moreover have "f k \<notin> set (map fst ?ps)"
  proof -
    from \<open>m $$ k = None\<close> have "k \<notin> set (map fst (sorted_list_of_fmap m))"
      by (metis map_of_eq_None_iff map_of_sorted_list set_map)
    with \<open>inj f\<close> show ?thesis
      using map_inj_pair_non_membership by force
  qed
  ultimately show ?thesis
    using fmap_of_list_insort_key_fst by fast
qed

lemma fmap_of_list_sorted_list_of_fmap:
  fixes m :: "('a::linorder, 'b) fmap"
  and f :: "'a \<Rightarrow> 'c::linorder"
  assumes "inj f"
  and "mono f"
  and "m $$ k = None"
  shows "fmap_of_list (map (\<lambda>(k, v). (f k, v)) (sorted_list_of_fmap m(k $$:= v))) =
    (fmap_of_list (map (\<lambda>(k, v). (f k, v)) (sorted_list_of_fmap m)))(f k $$:= v)"
proof -
  let ?g = "\<lambda>(k, v). (f k, v)"
  from assms(3) have "fmap_of_list (map ?g (sorted_list_of_fmap m(k $$:= v))) =
    fmap_of_list (map ?g (insort_key fst (k, v) (sorted_list_of_fmap m)))"
    by (simp add: sorted_list_of_fmap_is_insort_key_fst)
  also from assms have "\<dots> = fmap_of_list (insort_key fst (f k, v) (map ?g (sorted_list_of_fmap m)))"
    using calculation and map_sorted_list_of_fmap by fastforce
  also from assms(1,3) have "\<dots> = (fmap_of_list (map ?g (sorted_list_of_fmap m)))(f k $$:= v)"
    by (simp add: fmap_of_list_insort_key_fst_map)
  finally show ?thesis .
qed

text \<open> Map difference \<close>

abbreviation
  fmdiff :: "('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap" (infixl \<open>--\<^sub>f\<close> 100) where
  "m\<^sub>1 --\<^sub>f m\<^sub>2 \<equiv> fmfilter (\<lambda>x. x \<notin> fmdom' m\<^sub>2) m\<^sub>1"

lemma fmdiff_partition: (* TODO: Find a nicer proof *)
  assumes "m\<^sub>2 \<subseteq>\<^sub>f m\<^sub>1"
  shows "m\<^sub>2 ++\<^sub>f (m\<^sub>1 --\<^sub>f m\<^sub>2) = m\<^sub>1"
proof -
  from assms have *: "m\<^sub>2 ++\<^sub>f (m\<^sub>1 --\<^sub>f m\<^sub>2) \<subseteq>\<^sub>f m\<^sub>1"
    by (smt fmfilter_subset fmlookup_add fmpred_iff fmsubset_alt_def)
  then have "m\<^sub>1 \<subseteq>\<^sub>f m\<^sub>2 ++\<^sub>f (m\<^sub>1 --\<^sub>f m\<^sub>2)"
    by (simp add: fmsubset.rep_eq map_le_def)
  with * show ?thesis
    by (metis (no_types, lifting) domIff fmap_ext fmsubset.rep_eq map_le_def)
qed

lemma fmdiff_fmupd: (* TODO: Find a nicer proof *)
  assumes "m $$ k = None"
  shows "m(k $$:= v) --\<^sub>f {k $$:= v} = m"
  using assms
  by (smt Diff_iff Diff_insert_absorb fmdom'_empty fmdom'_fmupd fmdom'_notD fmdom'_notI
      fmfilter_true fmfilter_upd option.simps(3) singletonI)

text \<open> Map symmetric difference \<close>

abbreviation fmsym_diff :: "('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap" (infixl \<open>\<Delta>\<^sub>f\<close> 100) where
  "m\<^sub>1 \<Delta>\<^sub>f m\<^sub>2 \<equiv> (m\<^sub>1 --\<^sub>f m\<^sub>2) ++\<^sub>f (m\<^sub>2 --\<^sub>f m\<^sub>1)"

text \<open> Domain restriction \<close>

abbreviation dom_res :: "'a set \<Rightarrow> ('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap" (infixl \<open>\<lhd>\<close> 150) where
  "s \<lhd> m \<equiv> fmfilter (\<lambda>x. x \<in> s) m"

text \<open> Domain exclusion \<close>

abbreviation dom_exc :: "'a set \<Rightarrow> ('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap" (infixl \<open>\<lhd>'/\<close> 150) where
  "s \<lhd>/ m \<equiv> fmfilter (\<lambda>x. x \<notin> s) m"

text \<open> Intersection plus \<close>

abbreviation intersection_plus :: "('a, 'b::monoid_add) fmap \<Rightarrow> ('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap"
  (infixl \<open>\<inter>\<^sub>+\<close> 100)
where
  "m\<^sub>1 \<inter>\<^sub>+ m\<^sub>2 \<equiv> fmmap_keys (\<lambda>k v. v + m\<^sub>1 $$! k) (fmdom' m\<^sub>1 \<lhd> m\<^sub>2)"

text \<open> Union override right \<close>

abbreviation union_override_right :: "('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap"
  (infixl \<open>\<union>\<^sub>\<rightarrow>\<close> 100)
where
  "m\<^sub>1 \<union>\<^sub>\<rightarrow> m\<^sub>2 \<equiv> (fmdom' m\<^sub>2 \<lhd>/ m\<^sub>1) ++\<^sub>f m\<^sub>2"

text \<open> Union override left \<close>

abbreviation union_override_left :: "('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap"
  (infixl \<open>\<union>\<^sub>\<leftarrow>\<close> 100)
where
  "m\<^sub>1 \<union>\<^sub>\<leftarrow> m\<^sub>2 \<equiv> m\<^sub>1 ++\<^sub>f (fmdom' m\<^sub>1 \<lhd>/ m\<^sub>2)"

text \<open> Union override plus \<close>

abbreviation union_override_plus :: "('a, 'b::monoid_add) fmap \<Rightarrow> ('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap"
  (infixl \<open>\<union>\<^sub>+\<close> 100)
where
  "m\<^sub>1 \<union>\<^sub>+ m\<^sub>2 \<equiv> (m\<^sub>1 \<Delta>\<^sub>f m\<^sub>2) ++\<^sub>f (m\<^sub>1 \<inter>\<^sub>+ m\<^sub>2)"

text \<open> Extra lemmas for the non-standard map operators \<close>

lemma dom_res_singleton:
  assumes "m $$ k = Some v"
  shows "{k} \<lhd> m = {k $$:= v}"
  using assms
proof (induction m)
  case fmempty
  then show ?case
    by simp
next
  case (fmupd k' v' m)
  then show ?case
  proof (cases "k = k'")
    case True
    with \<open>m(k' $$:= v') $$ k = Some v\<close> have "v = v'"
      by simp
    with True have "{k} \<lhd> m(k' $$:= v') = ({k} \<lhd> m)(k $$:= v)"
      by simp
    also from True and \<open>m $$ k' = None\<close> have "\<dots> = {$$}(k $$:= v)"
      by (simp add: fmap_ext)
    finally show ?thesis
      by simp
  next
    case False
    with \<open>m(k' $$:= v') $$ k = Some v\<close> have *: "m $$ k = Some v"
      by simp
    with False have "{k} \<lhd> m(k' $$:= v') = {k} \<lhd> m"
      by simp
    with * and fmupd.IH show ?thesis
      by simp
  qed
qed

lemma dom_res_union_distr: (* TODO: Find a nicer proof *)
  shows "(A \<union> B) \<lhd> m = A \<lhd> m ++\<^sub>f B \<lhd> m"
proof -
  have "(A \<union> B) \<lhd> m \<subseteq>\<^sub>f A \<lhd> m ++\<^sub>f B \<lhd> m"
    by (smt Un_iff domIff dom_fmlookup fmdom'_add fmdom'_filter fmfilter_subset fmlookup_add
        fmsubset.rep_eq map_le_def member_filter)
  moreover have "A \<lhd> m ++\<^sub>f B \<lhd> m \<subseteq>\<^sub>f (A \<union> B) \<lhd> m"
    by (smt Un_iff domIff dom_fmlookup fmdom'_filter fmfilter_subset fmlookup_add fmsubset.rep_eq
        map_le_def member_filter)
  ultimately show ?thesis
    by (smt Un_iff domIff dom_fmlookup fmadd_empty(2) fmdiff_partition fmdom'_add fmfilter_false
        option.simps(3))
qed

lemma dom_exc_add_distr:
  shows "s \<lhd>/ (m\<^sub>1 ++\<^sub>f m\<^sub>2) = (s \<lhd>/ m\<^sub>1) ++\<^sub>f (s \<lhd>/ m\<^sub>2)"
  by (blast intro: fmfilter_add_distrib)

lemma fmap_partition:
  shows "m = s \<lhd>/ m ++\<^sub>f s \<lhd> m"
proof (induction m)
  case fmempty
  then show ?case
    by simp
next
  case (fmupd k v m)
  from fmupd.hyps have "s \<lhd>/ m(k $$:= v) ++\<^sub>f s \<lhd> m(k $$:= v) =
    s \<lhd>/ (m ++\<^sub>f {k $$:= v}) ++\<^sub>f s \<lhd> (m ++\<^sub>f {k $$:= v})"
    by simp
  also have "\<dots> = s \<lhd>/ m ++\<^sub>f s \<lhd>/ {k $$:= v} ++\<^sub>f s \<lhd> m ++\<^sub>f s \<lhd> {k $$:= v}"
    using dom_exc_add_distr by simp
  finally show ?case
  proof (cases "k \<in> s")
    case True
    then have "s \<lhd>/ m ++\<^sub>f s \<lhd>/ {k $$:= v} ++\<^sub>f s \<lhd> m ++\<^sub>f s \<lhd> {k $$:= v} =
      s \<lhd>/ m ++\<^sub>f {$$} ++\<^sub>f s \<lhd> m ++\<^sub>f {k $$:= v}"
      by simp
    also have "\<dots> = s \<lhd>/ m ++\<^sub>f s \<lhd> m ++\<^sub>f {k $$:= v}"
      by simp
    also from fmupd.IH have "\<dots> = m ++\<^sub>f {k $$:= v}"
      by simp
    finally show ?thesis using fmupd.hyps
      by auto
  next
    case False
    then have "s \<lhd>/ m ++\<^sub>f s \<lhd>/ {k $$:= v} ++\<^sub>f s \<lhd> m ++\<^sub>f s \<lhd> {k $$:= v} =
      s \<lhd>/ m ++\<^sub>f {k $$:= v} ++\<^sub>f s \<lhd> m ++\<^sub>f {$$}"
      by simp
    also have "\<dots> = s \<lhd>/ m ++\<^sub>f {k $$:= v} ++\<^sub>f s \<lhd> m"
      by simp
    also from fmupd.hyps have "\<dots> = s \<lhd>/ m ++\<^sub>f s \<lhd> m ++\<^sub>f {k $$:= v}"
      using fmap_singleton_comm by (metis (full_types) fmadd_assoc fmlookup_filter)
    also from fmupd.IH have "\<dots> = m ++\<^sub>f {k $$:= v}"
      by simp
    finally show ?thesis
      by auto
  qed
qed

lemma dom_res_addition_in:
  assumes "m\<^sub>1 $$ k = None"
  and "m\<^sub>2 $$ k = Some v'"
  shows "fmdom' m\<^sub>1(k $$:= v) \<lhd> m\<^sub>2 = fmdom' m\<^sub>1 \<lhd> m\<^sub>2 ++\<^sub>f {k $$:= v'}"
proof -
  from \<open>m\<^sub>1 $$ k = None\<close> have "fmdom' m\<^sub>1(k $$:= v) \<lhd> m\<^sub>2 = (fmdom' m\<^sub>1 \<union> {k}) \<lhd> m\<^sub>2"
    by simp
  also have "\<dots> = fmdom' m\<^sub>1 \<lhd> m\<^sub>2 ++\<^sub>f {k} \<lhd> m\<^sub>2"
    using dom_res_union_distr .
  finally show ?thesis
    using \<open>m\<^sub>2 $$ k = Some v'\<close> and dom_res_singleton by fastforce
qed

lemma inter_plus_addition_in: (* TODO: Find nicer proofs for SMT calls. *)
  assumes "m\<^sub>1 $$ k = None"
  and "m\<^sub>2 $$ k = Some v'"
  shows "m\<^sub>1(k $$:= v) \<inter>\<^sub>+ m\<^sub>2 = (m\<^sub>1 \<inter>\<^sub>+ m\<^sub>2) ++\<^sub>f {k $$:= v' + v}"
proof -
  from assms have "m\<^sub>1(k $$:= v) \<inter>\<^sub>+ m\<^sub>2 =
    fmmap_keys (\<lambda>k' v'. v' + m\<^sub>1(k $$:= v) $$! k') ((fmdom' m\<^sub>1 \<lhd> m\<^sub>2) ++\<^sub>f {k $$:= v'})"
    using dom_res_addition_in by fastforce
  also have "\<dots> = fmmap_keys (\<lambda>k' v'. v' + m\<^sub>1(k $$:= v) $$! k') (fmdom' m\<^sub>1 \<lhd> m\<^sub>2)
    ++\<^sub>f fmmap_keys (\<lambda>k' v'. v' + m\<^sub>1(k $$:= v) $$! k') {k $$:= v'}"
  proof -
    from \<open>m\<^sub>1 $$ k = None\<close> have "fmdom' (fmdom' m\<^sub>1 \<lhd> m\<^sub>2) \<inter> fmdom' {k $$:= v'} = {}"
      by (simp add: fmdom'_notI)
    then show ?thesis
      using fmmap_keys_hom by blast
  qed
  also from assms
  have "\<dots> = fmmap_keys (\<lambda>k' v'. v' + m\<^sub>1(k $$:= v) $$! k') (fmdom' m\<^sub>1 \<lhd> m\<^sub>2) ++\<^sub>f {k $$:= v' + v}"
    using dom_res_singleton by (smt domIff dom_fmlookup fmfilter_fmmap_keys fmlookup_dom'_iff
      fmlookup_fmmap_keys fmupd_lookup map_option_is_None option.map_sel option.sel)
  also have "\<dots> = fmmap_keys (\<lambda>k' v'. v' + m\<^sub>1 $$! k') (fmdom' m\<^sub>1 \<lhd> m\<^sub>2) ++\<^sub>f {k $$:= v' + v}"
    by (simp add: fmap_ext)
  finally show ?thesis .
qed

lemma inter_plus_addition_notin: (* TODO: Find nicer proofs for SMT calls. *)
  assumes "m\<^sub>1 $$ k = None"
  and "m\<^sub>2 $$ k = None"
  shows "m\<^sub>1(k $$:= v) \<inter>\<^sub>+ m\<^sub>2 = (m\<^sub>1 \<inter>\<^sub>+ m\<^sub>2)"
proof -
  from \<open>m\<^sub>2 $$ k = None\<close>
  have "m\<^sub>1(k $$:= v) \<inter>\<^sub>+ m\<^sub>2 = fmmap_keys (\<lambda>k' v'. v' + m\<^sub>1(k $$:= v) $$! k') (fmdom' m\<^sub>1 \<lhd> m\<^sub>2)"
    by (smt fmdom'_fmupd fmdom'_notI fmfilter_cong' insert_iff)
  also have "\<dots> = fmmap_keys (\<lambda>k' v'. v' + m\<^sub>1 $$! k') (fmdom' m\<^sub>1 \<lhd> m\<^sub>2)"
  proof (intro fmap_ext)
    fix k'
    from \<open>m\<^sub>1 $$ k = None\<close>
    show "fmmap_keys (\<lambda>k' v'. v' + m\<^sub>1(k $$:= v) $$! k') (fmdom' m\<^sub>1 \<lhd> m\<^sub>2) $$ k' =
      fmmap_keys (\<lambda>k' v'. v' + m\<^sub>1 $$! k') (fmdom' m\<^sub>1 \<lhd> m\<^sub>2) $$ k'"
      by (smt domIff dom_fmlookup fmdiff_fmupd fmlookup_filter fmlookup_fmmap_keys
          map_option_is_None option.expand option.map_sel)
  qed
  finally show ?thesis .
qed

lemma union_plus_addition_notin: (* TODO: Find nicer proofs for SMT calls. *)
  assumes "m\<^sub>1 $$ k = None"
  and "m\<^sub>2 $$ k = None"
  shows "m\<^sub>1(k $$:= v) \<union>\<^sub>+ m\<^sub>2 = (m\<^sub>1 \<union>\<^sub>+ m\<^sub>2) ++\<^sub>f {k $$:= v}"
proof -
  from \<open>m\<^sub>2 $$ k = None\<close> have "m\<^sub>1(k $$:= v) \<union>\<^sub>+ m\<^sub>2 =
    fmdom' m\<^sub>2 \<lhd>/ m\<^sub>1 ++\<^sub>f {k $$:= v} ++\<^sub>f fmdom' m\<^sub>1(k $$:= v) \<lhd>/ m\<^sub>2 ++\<^sub>f (m\<^sub>1(k $$:= v) \<inter>\<^sub>+ m\<^sub>2)"
    by (simp add: fmdom'_notI)
  also from assms have "\<dots> =
    fmdom' m\<^sub>2 \<lhd>/ m\<^sub>1 ++\<^sub>f {k $$:= v} ++\<^sub>f fmdom' m\<^sub>1 \<lhd>/ m\<^sub>2 ++\<^sub>f (m\<^sub>1(k $$:= v) \<inter>\<^sub>+ m\<^sub>2)"
    by (smt fmdom'_fmupd fmfilter_cong insert_iff option.distinct(1))
  also from assms have "\<dots> = fmdom' m\<^sub>2 \<lhd>/ m\<^sub>1 ++\<^sub>f {k $$:= v} ++\<^sub>f fmdom' m\<^sub>1 \<lhd>/ m\<^sub>2 ++\<^sub>f (m\<^sub>1 \<inter>\<^sub>+ m\<^sub>2)"
    using inter_plus_addition_notin by metis
  also from assms have "\<dots> = fmdom' m\<^sub>2 \<lhd>/ m\<^sub>1 ++\<^sub>f fmdom' m\<^sub>1 \<lhd>/ m\<^sub>2 ++\<^sub>f (m\<^sub>1 \<inter>\<^sub>+ m\<^sub>2) ++\<^sub>f {k $$:= v}"
    using fmap_singleton_comm
    by (smt fmadd_assoc fmfilter_fmmap_keys fmlookup_filter fmlookup_fmmap_keys)
  finally show ?thesis .
qed

end
