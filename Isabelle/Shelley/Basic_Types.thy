section \<open> Basic Types \<close>

theory Basic_Types
  imports "HOL-Library.Countable"
begin

text \<open> Epoch \<close>

typedecl epoch

text \<open> Unit of value \<close>

type_synonym coin = int

text \<open> Index \<close>

type_synonym ix = nat

text \<open> Absolute slot \<close>

typedecl slot

text \<open> Application versions \<close>

typedecl applications \<comment> \<open>NOTE: Abstract for now\<close>

end
