section \<open> Basic Types \<close>

theory Basic_Types
  imports Main
begin

text \<open> Epoch \<close>

type_synonym epoch = nat

text \<open> Unit of value \<close>

type_synonym coin = int

text \<open> Index \<close>

type_synonym ix = nat

text \<open> Absolute slot \<close>

type_synonym slot = nat

text \<open> Application versions \<close>

typedecl applications \<comment> \<open>NOTE: Abstract for now\<close>

end
