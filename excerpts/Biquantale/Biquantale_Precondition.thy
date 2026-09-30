(* Extracts from isabelle/new_rg_algebra/Biquantale/Biquantale_Precondition.thy. *)
(* These are source excerpts, not a standalone buildable theory. *)

(* Original lines 443-445. *)
text\<open>The precondition of an assertion is the assertion.\<close>
lemma pre_assert: "pre(\<lbrace>p\<rbrace>) = \<lbrace>p\<rbrace>"
  using neut_sync_assert neut_sync_to_pre assert_def by force
