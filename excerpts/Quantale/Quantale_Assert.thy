(* Extracts from isabelle/new_rg_algebra/Quantale/Quantale_Assert.thy. *)
(* These are source excerpts, not a standalone buildable theory. *)

(* Original lines 198-199. *)
lemma assert_op_test_idem: "\<lbrace>p\<rbrace> ; \<tau> p = \<lbrace>p\<rbrace>"
  by (simp add: assert_op_test) 


(* Original lines 502-506. *)
lemma assert_case_eq:
  assumes "\<lbrace>p\<rbrace> ; c = \<lbrace>p\<rbrace> ; d"
  assumes "\<lbrace>-p\<rbrace> ; c = \<lbrace>-p\<rbrace> ; d"
  shows "c = d"
  by (metis assert_neut assert_sup_op assms(1,2) boolean_algebra.disj_cancel_right left_neutral)
