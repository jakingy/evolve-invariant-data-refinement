(* Extracts from isabelle/new_rg_algebra/Rely_Guarantee/Optional_Command.thy. *)
(* These are source excerpts, not a standalone buildable theory. *)

(* Original lines 27-28. *)
lemma opt_assert_internalise: "\<lbrace>p\<rbrace> ; opt(q) = \<lbrace>p\<rbrace> ; opt(p \<triangleleft> q)" 
  by (metis seq.assert_op seq.assert_op_alt test_seq_opt)


(* Original lines 47-61. *)
lemma guar_opt:
  assumes refl_g: "refl g"
  shows "guar\<^sub>\<pi> g \<iinter> opt q = opt(g \<inter> q)"
proof -
  have a: "guar\<^sub>\<pi> g \<iinter> opt q = (guar\<^sub>\<pi> g \<iinter> \<pi> q) \<squnion> (guar\<^sub>\<pi> g \<iinter> \<tau>{\<sigma>. (\<sigma>,\<sigma>) \<in> q})" 
    using opt_def seq_conj.sync_sup by presburger
  then have b: "\<dots> = \<pi>(g \<inter> q) \<squnion> \<tau>{\<sigma>. (\<sigma>,\<sigma>) \<in> q}" 
    by (metis (no_types, lifting) env.hom_bot local.conj.commute pgm_guar_conj_atom 
        pgm_guar_conj_test sup_bot.right_neutral)
  then have c: "\<dots> = \<pi>(g \<inter> q) \<squnion> \<tau>{\<sigma>. (\<sigma>,\<sigma>)\<in> g \<inter> q}"
    using refl_g by (simp add: refl_onD) 
  show ?thesis using a b c opt_def by force
qed

find_theorems "\<tau> _"


(* Original lines 63-64. *)
lemma t: "\<tau> p = \<tau> p ; \<tau> p"
  by (simp add: seq.image_is_test seq.test_seq_idem)


(* Original lines 66-92. *)
lemma opt_range_constrain_test: "opt (q \<triangleright> a) = opt (q \<triangleright> a) ; \<tau> a"
proof-
  have subset_a: "{\<sigma>. (\<sigma>,\<sigma>) \<in> q \<triangleright> a} \<subseteq> a"
  proof(rule subsetI)
    fix \<sigma>
    assume asm: "\<sigma> \<in> {\<sigma>. (\<sigma>,\<sigma>) \<in> q \<triangleright> a}"
    have s_in: "(\<sigma>,\<sigma>) \<in> q \<triangleright> a" using asm by auto
    then show "\<sigma> \<in> a" by (simp add: restrict_range_def)
  qed

  have test_extract_a: "\<tau>{\<sigma>. (\<sigma>,\<sigma>) \<in> (q \<triangleright> a)} = \<tau>{\<sigma>. (\<sigma>,\<sigma>) \<in> (q \<triangleright> a)} ; \<tau> a"
  proof -
    have "\<forall>S Sa. \<not> (S::'state set) \<subseteq> Sa \<or> S = S \<inter> Sa"
      by (metis inf.orderE)
    then show ?thesis
      using seq.image_is_test seq.test_inf seq.test_seq_test subset_a by presburger
  qed

  have p1: "opt (q \<triangleright> a) = \<pi> (q \<triangleright> a) \<squnion> \<tau>{\<sigma>. (\<sigma>,\<sigma>) \<in> (q \<triangleright> a)}"
    using opt_def by auto
  also have "\<dots> = (\<pi> (q \<triangleright> a) ; \<tau> a) \<squnion> (\<tau>{\<sigma>. (\<sigma>,\<sigma>) \<in> (q \<triangleright> a)} ; \<tau> a)"
    using pgm_test_post test_extract_a by auto
  also have "\<dots> = (\<pi> (q \<triangleright> a) \<squnion> \<tau>{\<sigma>. (\<sigma>,\<sigma>) \<in> (q \<triangleright> a)}) ; \<tau> a"
    by (simp add: seq_par.sup_seq)
  finally show ?thesis
    by (simp add: p1)
qed


(* Original lines 94-107. *)
lemma opt_extract_test: 
  assumes q_establishes_a: "q \<subseteq> UNIV \<triangleright> a"
  shows "opt q = opt q ; \<tau> a"
proof-
  have "q = q \<triangleright> a"
  proof -
    have "q \<subseteq> UNIV"
      by blast
    then show ?thesis
      by (metis Int_absorb1 q_establishes_a range_restrict_inter)
  qed
  then show ?thesis
    by (metis opt_range_constrain_test)
qed


(* Original lines 109-118. *)
lemma opt_extract_assert: 
  assumes q_establishes_a: "q \<subseteq> UNIV \<triangleright> a"
  shows "opt q = opt q ; \<lbrace>a\<rbrace>"
proof-
  have a1: "opt q = opt q ; \<tau> a"
    by (simp add: opt_extract_test q_establishes_a)
  also have "\<dots> = opt q ; \<tau> a ; \<lbrace>a\<rbrace>"
    by (simp add: seq.test_op_assert seq_par.seq_assoc)
  then show ?thesis using a1 by simp
qed
