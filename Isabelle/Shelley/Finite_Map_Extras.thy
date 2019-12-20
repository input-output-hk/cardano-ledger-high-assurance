section \<open> Extra Features for Finite Maps \<close>

theory Finite_Map_Extras
  imports "HOL-Library.Finite_Map"
begin

text \<open> Extra lemmas and syntactic sugar for \<open>fmap\<close> \<close>

abbreviation fmap_update (\<open>_'(_ $$:= _')\<close> [1000,0,0] 1000) where
  "fmap_update m k v \<equiv> fmupd k v m"

notation fmlookup (infixl \<open>$$\<close> 999)

notation fmempty (\<open>{$$}\<close>)

abbreviation fmap_singleton (\<open>{_ $$:= _}\<close> [0, 0] 1000) where
  "fmap_singleton k v \<equiv> {$$}(k $$:= v)"

abbreviation fmap_lookup_the (infixl \<open>$$!\<close> 999) where
  "fmap_lookup_the m k \<equiv> the (m $$ k)"

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
proof (induction m arbitrary: k v rule: fmap_induct)
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
proof (induction m\<^sub>2 arbitrary: m\<^sub>1 rule: fmap_induct)
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
    then show ?thesis
      using fmupd.prems by auto
  qed
qed

text \<open> Domain restriction \<close>

abbreviation dom_res :: "'a set \<Rightarrow> ('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap" (infixl \<open>\<lhd>\<close> 150) where
  "s \<lhd> m \<equiv> fmfilter (\<lambda>x. x \<in> s) m"

text \<open> Domain exclusion \<close>

abbreviation dom_exc :: "'a set \<Rightarrow> ('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap" (infixl \<open>\<lhd>'/\<close> 150) where
  "s \<lhd>/ m \<equiv> fmfilter (\<lambda>x. x \<notin> s) m"

text \<open> Union override left \<close>

abbreviation union_override_left :: "('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap" (infixl \<open>\<union>\<^sub>\<leftarrow>\<close> 100) where
  "m\<^sub>1 \<union>\<^sub>\<leftarrow> m\<^sub>2 \<equiv> m\<^sub>1 ++\<^sub>f (fmdom' m\<^sub>1 \<lhd>/ m\<^sub>2)"

text \<open> Extra lemmas for \<open>\<lhd>\<close> and \<open>\<lhd>/\<close> \<close>

lemma dom_res_singleton:
  assumes "m $$ k = Some v"
  shows "{k} \<lhd> m = {k $$:= v}"
  using assms
proof (induction m rule: fmap_induct)
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

lemma dom_exc_add_distr:
  shows "s \<lhd>/ (m\<^sub>1 ++\<^sub>f m\<^sub>2) = (s \<lhd>/ m\<^sub>1) ++\<^sub>f (s \<lhd>/ m\<^sub>2)"
  by (blast intro: fmfilter_add_distrib)

lemma fmap_partition:
  shows "m = s \<lhd>/ m ++\<^sub>f s \<lhd> m"
proof (induction m rule: fmap_induct)
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

end
