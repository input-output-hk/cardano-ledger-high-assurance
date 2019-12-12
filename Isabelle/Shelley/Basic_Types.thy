section \<open> Basic Types \<close>

theory Basic_Types
  imports "HOL-Library.Countable"
begin

text \<open> Coin \<close>

type_synonym coin = int

text \<open> Index \<close>

typedecl ix

axiomatization ix_to_nat :: "ix \<Rightarrow> nat" where
  ix_to_nat_injectivity: "inj ix_to_nat"

instantiation ix :: countable
begin
instance by (standard, intro exI) (fact ix_to_nat_injectivity)
end

instantiation ix :: linorder
begin

definition less_ix :: "ix \<Rightarrow> ix \<Rightarrow> bool" where
  "less_ix x y = (ix_to_nat x < ix_to_nat y)"

definition less_eq_ix :: "ix \<Rightarrow> ix \<Rightarrow> bool" where
  "less_eq_ix x y = (ix_to_nat x \<le> ix_to_nat y)"

instance
proof
  fix x y z :: ix
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    unfolding less_eq_ix_def and less_ix_def by auto
  show "x \<le> x"
    unfolding less_eq_ix_def by simp
  show "\<lbrakk>x \<le> y; y \<le> z\<rbrakk> \<Longrightarrow> x \<le> z"
    unfolding less_eq_ix_def and less_ix_def by simp
  show "\<lbrakk>x \<le> y; y \<le> x\<rbrakk> \<Longrightarrow> x = y"
    unfolding less_eq_ix_def using ix_to_nat_injectivity by (meson antisym injD)
  show "x \<le> y \<or> y \<le> x"
    unfolding less_eq_ix_def by auto
qed

end

text \<open> Absolute slot \<close>

typedecl slot

end
