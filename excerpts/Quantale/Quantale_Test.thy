(* Extracts from isabelle/new_rg_algebra/Quantale/Quantale_Test.thy. *)
(* These are source excerpts, not a standalone buildable theory. *)

(* Original lines 188-193. *)
lemma test_case_ref:
  assumes "t \<in> Test"
  assumes "t ; c \<le> t ; d"
  assumes "!t ; c \<le> !t ; d"
  shows "c \<le> d"
  by (metis assms(1,2,3) sup_mono test_split)


(* Original lines 195-200. *)
lemma test_case_eq:
  assumes "t \<in> Test"
  assumes "t ; c = t ; d"
  assumes "!t ; c = !t ; d"
  shows "c = d"
  by (metis assms(1,2,3) test_split)


(* Original lines 202-206. *)
lemma test_case_eq_alt:
  assumes "\<tau> p ; c = \<tau> p ; d"
  assumes "\<tau> (-p) ; c = \<tau> (-p) ; d"
  shows "c = d"
  using assms(1,2) image_is_test test_case_eq test_negate by auto
