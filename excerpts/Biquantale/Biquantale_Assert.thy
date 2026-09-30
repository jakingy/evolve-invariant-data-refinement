(* Extracts from isabelle/new_rg_algebra/Biquantale/Biquantale_Assert.thy. *)
(* These are source excerpts, not a standalone buildable theory. *)

(* Original lines 609-612. *)
lemma assert_stable_assert:
  assumes "test_stable p c"
  shows "\<lbrace>p\<rbrace> ; c = \<lbrace>p\<rbrace> ; c ; \<lbrace>p\<rbrace>"
  using assms assert_op_op_assert inv_alt test_stable_def by auto


(* Original lines 614-617. *)
lemma assert_stable_test:
  assumes "test_stable p c"
  shows "\<lbrace>p\<rbrace> ; c = \<lbrace>p\<rbrace> ; c ; \<tau> p"
  using assms inv_alt inv_assert_eq test_stable_def by auto
