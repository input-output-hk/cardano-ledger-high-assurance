section \<open> Cryptographic Primitives \<close>

theory Cryptography
  imports Main
begin

text \<open> Public verifying key \<close>

typedecl v_key

text \<open> Hash of a key \<close>

typedecl key_hash

text \<open> Genesis key hash \<close>

typedecl key_hash_g

text \<open> hashKey function \<close>

consts hash_key :: "v_key \<Rightarrow> key_hash"

end
