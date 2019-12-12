section \<open> Extra features for \<open>fmap\<close>'s \<close>

theory Finite_Map_Extras
  imports "HOL-Library.Finite_Map"
begin

text \<open> Some extra lemmas and syntactic sugar for \<open>fmap\<close> \<close>

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

text \<open> Domain restriction \<close>

abbreviation dom_res :: "'a set \<Rightarrow> ('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap" (infixl \<open>\<lhd>\<close> 150) where
  "s \<lhd> m \<equiv> fmfilter (\<lambda>x. x \<in> s) m"

text \<open> Domain exclusion \<close>

abbreviation dom_exc :: "'a set \<Rightarrow> ('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap" (infixl \<open>\<lhd>'/\<close> 150) where
  "s \<lhd>/ m \<equiv> fmfilter (\<lambda>x. x \<notin> s) m"

end
