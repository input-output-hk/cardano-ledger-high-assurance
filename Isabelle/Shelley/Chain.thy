section \<open> Blockchain layer \<close>

theory Chain
  imports Rewards
begin

subsection \<open> Verifiable Random Functions (VRF) \<close>

text \<open> Seed for pseudo-random number generator \<close>

typedecl seed

text \<open> Stake pool distribution \<close>

typedecl pool_distr \<comment> \<open>NOTE: Abstract for now\<close>

subsection \<open> Block Definitions \<close>

text \<open> Abstract Types \<close>

typedecl hash_header \<comment> \<open>hash of a block header\<close>

typedecl hash_b_body \<comment> \<open>hash of a block body\<close>

text \<open> Block Header Body \<close>

typedecl b_h_body \<comment> \<open>NOTE: Abstract for now\<close>

text \<open> Block Types \<close>

typedecl b_header \<comment> \<open>NOTE: Abstract for now\<close>

typedecl block \<comment> \<open>NOTE: Abstract for now\<close>

text \<open> Abstract Functions \<close>

consts b_header_size :: "b_header \<Rightarrow> nat" \<comment> \<open>size of a block header\<close>

consts b_body_size :: "tx list \<Rightarrow> nat" \<comment> \<open>size of a block body\<close>

text \<open> Accessor Functions \<close>

\<comment> \<open>NOTE: The following function is actually a block header body field in the spec. Abstract for now\<close>
consts bhash :: "b_h_body \<Rightarrow> hash_b_body" \<comment> \<open>block body hash\<close>

consts bheader :: "block \<Rightarrow> b_header" \<comment> \<open>NOTE: Abstract for now\<close>

consts bhbody :: "b_header \<Rightarrow> b_h_body" \<comment> \<open>NOTE: Abstract for now\<close>

consts bbody :: "block \<Rightarrow> tx list" \<comment> \<open>NOTE: Abstract for now\<close>

consts bvkcold :: "b_h_body \<Rightarrow> v_key" \<comment> \<open>NOTE: Abstract for now\<close>

consts bslot :: "b_h_body \<Rightarrow> slot" \<comment> \<open>NOTE: Abstract for now\<close>

consts h_b_bsize :: "b_h_body \<Rightarrow> nat" \<comment> \<open>NOTE: Abstract for now\<close>

consts bbodyhash :: "tx list \<Rightarrow> hash_b_body"

subsection \<open> New Epoch Transition \<close>

text \<open> New Epoch environments \<close>

type_synonym new_epoch_env = "
  slot \<times> \<comment> \<open>current slot\<close>
  key_hash_g set \<comment> \<open>genesis key hashes\<close>"

text \<open> New Epoch states \<close>

type_synonym new_epoch_state = "
  epoch \<times> \<comment> \<open>last epoch\<close>
  blocks_made \<times> \<comment> \<open>blocks made last epoch\<close>
  blocks_made \<times> \<comment> \<open>blocks made this epoch\<close>
  epoch_state \<times> \<comment> \<open>epoch state\<close>
  reward_update option \<times> \<comment> \<open>reward state\<close>
  pool_distr \<times> \<comment> \<open>pool stake distribution\<close>
  (slot, key_hash_g option) fmap \<comment> \<open>OBFT overlay schedule\<close>"

text \<open> New Epoch rules \<close>

text \<open>
  NOTE:
  \<^item> The general constraints in the spec are not enforced for now.
  \<^item> \<open>pd'\<close> and \<open>osched'\<close> are undefined for now.
\<close>
inductive new_epoch_sts :: "new_epoch_env \<Rightarrow> new_epoch_state \<Rightarrow> epoch \<Rightarrow> new_epoch_state \<Rightarrow> bool"
  (\<open>_ \<turnstile> _ \<rightarrow>\<^bsub>NEWEPOCH\<^esub>{_} _\<close> [51, 0, 51] 50)
  where
    new_epoch: "
      \<Gamma> \<turnstile>
        (e\<^sub>l, b\<^sub>p\<^sub>r\<^sub>e\<^sub>v, b\<^sub>c\<^sub>u\<^sub>r, es, ru, pd, osched) \<rightarrow>\<^bsub>NEWEPOCH\<^esub>{e} (e, b\<^sub>c\<^sub>u\<^sub>r, {$$}, es'', None, pd', osched')"
      if "e = e\<^sub>l + 1"
      and "ru = Some ru'"
      and "(\<Delta>t, \<Delta>r, rs, \<Delta>f, i\<^sub>r\<^sub>w\<^sub>d) = ru'"
      and "i\<^sub>r\<^sub>w\<^sub>d = get_ir es"
      and "\<Delta>f = - get_fee_ss es"
      and "rewards\<^sub>m\<^sub>i\<^sub>r = (\<Sum> k \<in> fmdom' i\<^sub>r\<^sub>w\<^sub>d. i\<^sub>r\<^sub>w\<^sub>d $$! k)"
      and "- \<Delta>r = \<Delta>r\<^sub>l + rewards\<^sub>m\<^sub>i\<^sub>r"
      and "\<Delta>t - \<Delta>r\<^sub>l + (\<Sum> k \<in> fmdom' rs. rs $$! k) + \<Delta>f = 0"
      and "es' = apply_r_upd ru' es"
      and "\<turnstile> es' \<rightarrow>\<^bsub>EPOCH\<^esub>{e} es''"
      and "pd' = undefined"
      and "osched' = undefined"
  | not_new_epoch: "
      \<Gamma> \<turnstile> nes \<rightarrow>\<^bsub>NEWEPOCH\<^esub>{e} nes"
      if "e \<noteq> e\<^sub>l + 1"
  | no_reward_update: "
      \<Gamma> \<turnstile> nes \<rightarrow>\<^bsub>NEWEPOCH\<^esub>{e} nes"
      if "e = e\<^sub>l + 1"
      and "(_, _, _, _, ru, _, _) = nes"
      and "ru = None"

subsection \<open> Reward Update Transition \<close>

text \<open> Reward Update environments \<close>

type_synonym r_upd_env = "
  blocks_made \<times> \<comment> \<open>blocks made\<close>
  epoch_state \<comment> \<open>epoch state\<close>"

text \<open> Reward Update rules \<close>

inductive rupd_sts :: "r_upd_env \<Rightarrow> reward_update option \<Rightarrow> slot \<Rightarrow> reward_update option \<Rightarrow> bool"
  (\<open>_ \<turnstile> _ \<rightarrow>\<^bsub>RUPD\<^esub>{_} _\<close> [51, 0, 51] 50)
  where
    create_reward_update: "
      (b, es) \<turnstile> ru \<rightarrow>\<^bsub>RUPD\<^esub>{s} ru'"
      if "s > first_slot (epoch s) + start_rewards"
      and "ru = None"
      and "ru' = Some (create_r_upd b es)"
  | reward_update_exists: "
      _ \<turnstile> ru \<rightarrow>\<^bsub>RUPD\<^esub>{s} ru"
      if "ru \<noteq> None"
  | reward_too_early: "
      _ \<turnstile> ru \<rightarrow>\<^bsub>RUPD\<^esub>{s} ru"
      if "ru = None"
      and "s \<le> first_slot (epoch s) + start_rewards"

subsection \<open> Chain Tick Transition \<close>

inductive tick_sts :: "key_hash_g set \<Rightarrow> new_epoch_state \<Rightarrow> slot \<Rightarrow> new_epoch_state \<Rightarrow> bool"
  (\<open>_ \<turnstile> _ \<rightarrow>\<^bsub>TICK\<^esub>{_} _\<close> [51, 0, 51] 50)
  where
    tick: "
      gkeys \<turnstile> nes \<rightarrow>\<^bsub>TICK\<^esub>{s} nes''"
      if "(s, gkeys) \<turnstile> nes \<rightarrow>\<^bsub>NEWEPOCH\<^esub>{epoch s} nes'"
      and "(_, b\<^sub>p\<^sub>r\<^sub>e\<^sub>v, _, es, _, _, _) = nes"
      and "(e\<^sub>l', b\<^sub>p\<^sub>r\<^sub>e\<^sub>v', b\<^sub>c\<^sub>u\<^sub>r', es', ru', pd', osched') = nes'"
      and "(b\<^sub>p\<^sub>r\<^sub>e\<^sub>v, es) \<turnstile> ru' \<rightarrow>\<^bsub>RUPD\<^esub>{s} ru''"
      and "nes'' = (e\<^sub>l', b\<^sub>p\<^sub>r\<^sub>e\<^sub>v', b\<^sub>c\<^sub>u\<^sub>r', es', ru'', pd', osched')"

subsection \<open> Block Body Transition \<close>

text \<open> BBody environments \<close>

type_synonym b_body_env = "
  slot set \<times> \<comment> \<open>overlay slots\<close>
  p_params \<times> \<comment> \<open>protocol parameters\<close>
  coin \<comment> \<open>total reserves\<close>"

text \<open> BBody states \<close>

type_synonym b_body_state = "
  l_state \<times> \<comment> \<open>ledger state\<close>
  blocks_made \<comment> \<open>blocks made\<close>"

text \<open> BBody helper function \<close>

fun incr_blocks :: "bool \<Rightarrow> key_hash \<Rightarrow> blocks_made \<Rightarrow> blocks_made" where
  "incr_blocks is_overlay hk b = undefined" \<comment> \<open>NOTE: Undefined for now\<close>

text \<open> BBody rules \<close>

inductive bbody_sts :: "b_body_env \<Rightarrow> b_body_state \<Rightarrow> block \<Rightarrow> b_body_state \<Rightarrow> bool"
  (\<open>_ \<turnstile> _ \<rightarrow>\<^bsub>BBODY\<^esub>{_} _\<close> [51, 0, 51] 50)
  where
    block_body: "
      (oslots, pp, reserves) \<turnstile>
        (ls, b) \<rightarrow>\<^bsub>BBODY\<^esub>{block} (ls', incr_blocks (bslot bhb \<in> oslots) hk b)"
      if "txs = bbody block"
      and "bhb = bhbody (bheader block)"
      and "hk = hash_key (bvkcold bhb)"
      and "b_body_size txs = h_b_bsize bhb"
      and "bbodyhash txs = bhash bhb"
      and "(bslot bhb, pp, reserves) \<turnstile> ls \<rightarrow>\<^bsub>LEDGERS\<^esub>{txs} ls'"

subsection \<open> Chain Transition \<close>

text \<open> Chain states \<close>

type_synonym chain_state = "
  new_epoch_state \<times> \<comment> \<open>epoch specific state\<close>
  (key_hash, nat) fmap \<times> \<comment> \<open>operational certificate issue numbers\<close>
  seed \<times> \<comment> \<open>epoch nonce\<close>
  seed \<times> \<comment> \<open>evolving nonce\<close>
  seed \<times> \<comment> \<open>candidate nonce\<close>
  seed \<times> \<comment> \<open>seed generated from hash of previous epoch\<close>
  hash_header \<times> \<comment> \<open>latest header hash\<close>
  slot \<comment> \<open>last slot\<close>"

text \<open> Chain Transition Helper Functions \<close>

fun get_g_keys :: "new_epoch_state \<Rightarrow> key_hash_g set" where
  "get_g_keys nes = undefined" \<comment> \<open>NOTE: Undefined for now\<close>

fun update_nes :: "new_epoch_state \<Rightarrow> blocks_made \<Rightarrow> l_state \<Rightarrow> new_epoch_state" where
  "update_nes (e\<^sub>l, b\<^sub>p\<^sub>r\<^sub>e\<^sub>v, _, (acnt, ss, _, pp), ru, pd, osched) b\<^sub>c\<^sub>u\<^sub>r ls =
    (e\<^sub>l, b\<^sub>p\<^sub>r\<^sub>e\<^sub>v, b\<^sub>c\<^sub>u\<^sub>r, (acnt, ss, ls, pp), ru, pd, osched)"

text \<open> Chain Rules \<close>

text \<open>
  NOTE:
  \<^item> The \<open>PRTCL\<close> rule is not included for now.
\<close>
inductive chain_sts :: "slot \<Rightarrow> chain_state \<Rightarrow> block \<Rightarrow> chain_state \<Rightarrow> bool"
  (\<open>_ \<turnstile> _ \<rightarrow>\<^bsub>CHAIN\<^esub>{_} _\<close> [51, 0, 51] 50)
  where
    chain: "
      s\<^sub>n\<^sub>o\<^sub>w \<turnstile> (nes, cs, \<eta>\<^sub>0, \<eta>\<^sub>v, \<eta>\<^sub>c, \<eta>\<^sub>h, h, s\<^sub>l) \<rightarrow>\<^bsub>CHAIN\<^esub>{block} (nes'', cs', \<eta>'\<^sub>0, \<eta>'\<^sub>v, \<eta>'\<^sub>c, \<eta>'\<^sub>h, h', s'\<^sub>l)"
      if "bh = bheader block"
      and "bhb = bhbody bh"
      and "gkeys = get_g_keys nes"
      and "s = bslot bhb"
      and "(_, _, _, (_, _, _, pp), _, _, _) = nes"
      and "b_header_size bh \<le> max_header_size pp"
      and "h_b_bsize bhb \<le> max_block_size pp"
      and "gkeys \<turnstile> nes \<rightarrow>\<^bsub>TICK\<^esub>{s} nes'"
      and "(_, _, b\<^sub>c\<^sub>u\<^sub>r, es, _, _, osched) = nes'"
      and "(acnt, _, ls, pp') = es"
      and "(_, reserves) = acnt"
      and "(fmdom' osched, pp', reserves) \<turnstile> (ls, b\<^sub>c\<^sub>u\<^sub>r) \<rightarrow>\<^bsub>BBODY\<^esub>{block} (ls', b'\<^sub>c\<^sub>u\<^sub>r)"
      and "nes'' = update_nes nes' b'\<^sub>c\<^sub>u\<^sub>r ls'"
      and "cs' = undefined"
      and "\<eta>'\<^sub>0 = undefined"
      and "\<eta>'\<^sub>v = undefined"
      and "\<eta>'\<^sub>c = undefined"
      and "\<eta>'\<^sub>h = undefined"
      and "h' = undefined"
      and "s'\<^sub>l = undefined"
end
