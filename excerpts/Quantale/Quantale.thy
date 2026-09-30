(* Extracts from isabelle/new_rg_algebra/Quantale/Quantale.thy. *)
(* These are source excerpts, not a standalone buildable theory. *)

(* Original lines 210-221. *)
text \<open>If a command is idempotent with respect to \<open>(\<odot>)\<close>, then can compare operands separately.\<close>
lemma op_idem_mono:
  assumes idem: "c = c \<odot> c"
  assumes lft: "a \<le> c"
  assumes rht: "b \<le> c"
  shows "a \<odot> b \<le> c"
proof -
  have "a \<odot> b \<le> c \<odot> c"
    by (simp add: lft op_mono rht)
  then show ?thesis
    using idem by argo
qed
