(* Extracts from isabelle/new_rg_algebra/Rely_Guarantee/Rely_Guarantee.thy. *)
(* These are source excerpts, not a standalone buildable theory. *)

(* Original lines 68-84. *)
text \<open>If a command c is test_stable for condition p, then if there is an assertion
infront of c iterated, the assertion can be brought inside the iterator sequentially prior to c.\<close>
lemma stable_iter_maintain_test: 
  assumes command_stable: "seq.test_stable p c"
  shows "\<tau> p ; c\<^sup>\<omega> = \<tau> p ; (\<tau> p ; c)\<^sup>\<omega>"
proof -
  have preserves_p: "\<tau> p ; c ; \<tau> p = \<tau> p ; c "
    using command_stable
    by (simp add: test_pre_post seq.test_stable_def)

  have is_test: "\<tau> p \<in> seq.Test"
    by (simp add: seq.image_is_test)

  show ?thesis
    by (metis is_test preserves_p seq.iter_leapfrog seq.test_seq_idem
        seq_par.iter_establish_test seq_par.seq_assoc)
qed


(* Original lines 86-98. *)
text \<open>If a command c is test_stable for condition p, then if there is an assertion
infront of c iterated, the assertion can be brought inside the iterator sequentially prior to c.\<close>
lemma stable_iter_maintain_assert: 
  assumes command_stable: "seq.test_stable p c"
  shows "\<lbrace>p\<rbrace> ; c\<^sup>\<omega> = (\<lbrace>p\<rbrace> ; c)\<^sup>\<omega>"
proof -
  have assert_stable: "\<lbrace>p\<rbrace> ; c \<ge> c ; \<lbrace>p\<rbrace>"
    using command_stable
    by (simp add: seq.test_stable_def seq_par.inv_alt)
  show ?thesis
    using assert_stable
    by (rule seq_par.iter_maintain_assert)
qed


(* Original lines 100-135. *)
text \<open>If a command c is test_stable for condition p, then if there is an assertion
infront of c iterated, a test can be added sequentially prior to c in the iterator.\<close>
lemma assert_stable_iter_maintains_test: 
  assumes command_stable: "seq.test_stable p c"
  shows "\<lbrace>p\<rbrace> ; c\<^sup>\<omega> = \<lbrace>p\<rbrace> ; (\<tau> p ; c)\<^sup>\<omega>"
  by (simp add: command_stable seq.assert_op_alt
      stable_iter_maintain_test)

(** Needed? 
lemma rely_guar_def:
  shows "(rely r) \<iinter> (guar\<^sub>\<pi> g) = (\<pi> g \<squnion> \<epsilon> r)\<^sup>\<omega>;(nil \<squnion> \<epsilon>(-r);\<top>)"
proof -
  have "(rely r) \<iinter> (guar\<^sub>\<pi> g) = (\<pi>(\<top>) \<squnion> \<epsilon> r)\<^sup>\<omega>;(nil \<squnion> \<epsilon>(-r);\<top>) \<iinter> (\<pi> g \<squnion> \<epsilon>(\<top>))\<^sup>\<omega>"
    using rely_def3 guar_def pgm_restrict_def Env_def by simp
  also have "... = ((\<pi>(\<top>) \<squnion> \<epsilon> r) \<iinter> (\<pi> g \<squnion> \<epsilon>(\<top>)))\<^sup>\<omega>;((nil \<squnion> \<epsilon>(-r);\<top>) \<iinter> (\<pi> g \<squnion> \<epsilon>(\<top>))\<^sup>\<omega>)"
    using conj.atomic_iter_pre_sync_iter pgm_or_env_atomic by metis
  also have "... = ((\<pi>(\<top> \<sqinter> g) \<squnion> \<epsilon>(r \<sqinter> \<top>)))\<^sup>\<omega>;((nil \<squnion> \<epsilon>(-r);\<top>) \<iinter> (\<pi> g \<squnion> \<epsilon>(\<top>))\<^sup>\<omega>)"
    using pgmenv_conj_pgmenv pgmenv_conj_env by presburger
  also have "... = ((\<pi>(\<top> \<sqinter> g) \<squnion> \<epsilon>(r \<sqinter> \<top>)))\<^sup>\<omega>;(nil \<squnion> (\<epsilon>(-r) \<iinter> (\<pi> g \<squnion> \<epsilon>(\<top>)));\<top>)"
    using conj.atomic_optional_sync_iter pgm_or_env_atomic env_atomic conj_abort_left by metis
  also have "... = ((\<pi>(\<top> \<sqinter> g) \<squnion> \<epsilon>(r \<sqinter> \<top>)))\<^sup>\<omega>;(nil \<squnion> \<epsilon>(-r \<sqinter> \<top>);\<top>)"
    by (metis inf_top.right_neutral inf_top_left local.conj_commute pgmenv_conj_env)
  finally show ?thesis by simp
qed  
lemma rely_guar_stable_step:
  assumes p_stable_under_rg: "stable p (r \<squnion> g)"
  shows "(\<pi> g \<squnion> \<epsilon> r) ; \<tau> p \<ge> \<tau> p ; (\<pi> g \<squnion> \<epsilon> r)"
proof -
  have "\<pi> g ; \<tau> p  \<ge> \<tau> p ; \<pi> g" sledgehamme
    using pgm_test_ref p_stable_under_rg unfolding stable_def by blast
  moreover have "\<epsilon> r;\<tau>(p) \<ge> \<tau>(p);\<epsilon>(r)"
      using env_test_ref p_stable_under_rg unfolding stable_def by blast
  ultimately show ?thesis 
    using sup_mono sup_seq_distrib seq_sup_distrib by simp
qed
*)


(* Original lines 196-216. *)
lemma
  assumes g: "seq.test_stable p (\<pi> g)"
  assumes r: "seq.test_stable p (\<epsilon> r)"
  shows "rely r \<iinter> guar\<^sub>\<pi> g ; \<tau> p \<ge> rely r \<iinter> \<tau> p ; guar\<^sub>\<pi> g" 
proof -
  have "rely r \<iinter> guar\<^sub>\<pi> g ; \<tau> p = (rely r \<iinter> guar\<^sub>\<pi> g) ; \<tau>(p)" 
    using seq.image_is_test seq_conj.sync_op_test by blast
  also have "\<dots> \<ge> \<tau> p ; (rely r \<iinter> guar\<^sub>\<pi> g)"  (is "_ \<ge> ?rhs")
    using g r rely_guar_stable seq.test_stable_def by blast
  also have "?rhs = rely r \<iinter> \<tau> p ; guar\<^sub>\<pi> g" 
    using seq.image_is_test test_seq_rely by blast
  finally show ?thesis .
qed

(**
abbreviation P' :: "'b \<Rightarrow> 'b" where
"P' p \<equiv> {(k, k'). k \<in> p \<longrightarrow> k' \<in> p}"

definition guar_inv :: "'b \<Rightarrow> 'a" where
"guar_inv p = (guar\<^sub>\<pi> (P' p))"
*)


(* Original lines 370-400. *)
text \<open>Lemmas that describe how a rely-guar can be transformed by a test when r and g are stable.
If r and g are stable over p, rely r guar g will maintain p and hence we can assume p holds in
the initial step of r and g until abort.\<close>
lemma test_rely_guar_atomic_stable: 
  assumes stable_r: "stable p r"
  assumes stable_g: "stable p g"
  shows "\<tau> p ; rely r \<iinter> guar\<^sub>\<pi> g = \<tau> p ; (\<pi> (p \<triangleleft> g) \<squnion> \<epsilon> (p \<triangleleft> r) \<squnion> \<epsilon> (p \<triangleleft> (-r)) ; \<top>)\<^sup>\<omega>"
proof-
  have stable_basis: "seq.test_stable p (\<pi> g \<squnion> \<epsilon> r \<squnion> \<epsilon>(-r) ; \<top>)"
  proof-
    have g: "seq.test_stable p (\<pi> g)"
      using stable_g stable_implies_test_stable_pgm by auto
    have r: "seq.test_stable p (\<epsilon> r)"
      using stable_implies_test_stable_env stable_r by auto
    have "seq.test_stable p (rely r \<iinter> guar\<^sub>\<pi> g)"
      using g r rely_guar_stable by auto
    then show ?thesis
      using g pgm_restrict_conj_env_assump r rely_guar_basis_stable
      by auto 
  qed

 have "\<tau> p ; rely r \<iinter> guar\<^sub>\<pi> g = \<tau> p ; (\<pi> g \<squnion> \<epsilon> r \<squnion> \<epsilon>(-r) ; \<top>)\<^sup>\<omega>"
  by (metis pgm_guar_pre rely_conj_guar seq.image_is_test
      seq_conj.test_pre_interchange_left)
  also have "\<dots> = \<tau> p ; (\<tau> p ; (\<pi> g \<squnion> \<epsilon> r \<squnion> \<epsilon>(-r) ; \<top>))\<^sup>\<omega>"
    using stable_basis stable_iter_maintain_test by auto
  also have "\<dots> = \<tau> p ; (\<tau> p ; \<pi> g \<squnion> \<tau> p ; \<epsilon> r \<squnion> \<tau> p ; \<epsilon>(-r) ; \<top>)\<^sup>\<omega>"
    by (simp add: seq_par.seq_assoc seq_par.seq_sup)
  finally show ?thesis
    using env_test_pre pgm_test_pre by auto
qed


(* Original lines 402-419. *)
lemma test_rely_guar_contrain_rely_domain:
  assumes stable_r: "stable p r"
  assumes stable_g: "stable p g"
  shows "\<tau> p ; rely r \<iinter> guar\<^sub>\<pi> g = \<tau> p ; rely (p \<triangleleft> r) \<iinter> guar\<^sub>\<pi> g"
proof-
  have dom_eq: "p \<triangleleft> r = p \<triangleleft> (p \<triangleleft> r)"
    by (auto simp: restrict_domain_def restrict_range_def)
  have dom_neg_eq: "p \<triangleleft> (-(r)) = p \<triangleleft> (-(p \<triangleleft> r))"
    by (auto simp: restrict_domain_def restrict_range_def)

  have stable_pr: "stable p (p \<triangleleft> r)"
    using domain_restrict_remove stable_r by blast

  have "\<tau> p ; (\<pi> g \<squnion> \<epsilon> (p \<triangleleft> r) \<squnion> \<epsilon> (p \<triangleleft> (-r)) ; \<top>)\<^sup>\<omega> = \<tau> p ; (\<pi> g \<squnion> \<epsilon> (p \<triangleleft> (p \<triangleleft> r)) \<squnion> \<epsilon> (p \<triangleleft> (-(p \<triangleleft> r))) ; \<top>)\<^sup>\<omega>"
    using dom_eq dom_neg_eq by force
  then show ?thesis
    using dom_eq dom_neg_eq stable_g stable_pr stable_r test_rely_guar_atomic_stable by auto
qed


(* Original lines 421-430. *)
lemma assert_rely_guar_contrain_rely_domain:
  assumes stable_r: "stable p r"
  assumes stable_g: "stable p g"
  shows "\<lbrace>p\<rbrace> ; rely r \<iinter> guar\<^sub>\<pi> g = \<lbrace>p\<rbrace> ; rely (p \<triangleleft> r) \<iinter> guar\<^sub>\<pi> g"
proof-
  have "\<lbrace>p\<rbrace> ; rely r \<iinter> guar\<^sub>\<pi> g = \<lbrace>p\<rbrace> ; (\<tau> p ; rely r \<iinter> guar\<^sub>\<pi> g)"
    by (metis seq.assert_op_test_idem seq_conj.assert_op_sync_left seq_par.seq_assoc)
  then show ?thesis
    by (metis seq.assert_op_test_idem seq_conj.assert_op_sync_left seq_par.seq_assoc stable_g stable_r test_rely_guar_contrain_rely_domain) 
qed


(* Original lines 432-433. *)
lemma stable_pre_p_implies_stable: "(stable p (p \<triangleleft> r)) \<longleftrightarrow> (stable p r)"
  by (simp add: domain_restrict_image)


(* Original lines 435-436. *)
lemma range_restricted_equiv_relation: "p \<triangleleft> ((-(p \<triangleleft> UNIV)) \<union> r) = p \<triangleleft> r"
  by (auto simp: restrict_domain_def restrict_range_def)


(* Original lines 438-453. *)
lemma test_rely_guar_not_p_any_rely:
  assumes stable_r: "stable p r"
  assumes stable_g: "stable p g"
  shows "\<tau> p ; rely r \<iinter> guar\<^sub>\<pi> g = \<tau> p ; rely (-(p \<triangleleft> UNIV) \<union> r) \<iinter> guar\<^sub>\<pi> g"
proof-
  have stable_pre_p: "stable p (p \<triangleleft> ((-(p \<triangleleft> UNIV)) \<union> r))"
    by (simp add: range_restricted_equiv_relation stable_pre_p_implies_stable stable_r)

  have stable_alt: "stable p ((-(p \<triangleleft> UNIV)) \<union> r)"
    by (metis stable_pre_p stable_pre_p_implies_stable)

  have "\<tau> p ; rely (-(p \<triangleleft> UNIV) \<union> r) \<iinter> guar\<^sub>\<pi> g = \<tau> p ; rely (p \<triangleleft> r) \<iinter> guar\<^sub>\<pi> g"
    by (simp add: range_restricted_equiv_relation stable_alt stable_g test_rely_guar_contrain_rely_domain)
  then show ?thesis
    by (simp add: stable_g stable_r test_rely_guar_contrain_rely_domain)
qed


(* Original lines 455-470. *)
lemma test_rely_guar_contrain_guar_domain:
  assumes stable_r: "stable p r"
  assumes stable_g: "stable p g"
  shows "\<tau> p ; rely r \<iinter> guar\<^sub>\<pi> g = \<tau> p ; rely r \<iinter> guar\<^sub>\<pi> (p \<triangleleft> g)"
proof-
  have dom_eq_g: "p \<triangleleft> g = p \<triangleleft> (p \<triangleleft> g)"
    by (auto simp: restrict_domain_def restrict_range_def)

  have stable_pg: "stable p (p \<triangleleft> g)"
    using domain_restrict_remove stable_g by blast

  have "\<tau> p ; (\<pi> (p \<triangleleft> g) \<squnion> \<epsilon> r \<squnion> \<epsilon> (-r) ; \<top>)\<^sup>\<omega> = \<tau> p ; (\<pi> (p \<triangleleft> (p \<triangleleft> g)) \<squnion> \<epsilon> r \<squnion> \<epsilon> (-r) ; \<top>)\<^sup>\<omega>"
    using dom_eq_g by force
  then show ?thesis
    using dom_eq_g stable_g stable_pg stable_r test_rely_guar_atomic_stable by auto
qed


(* Original lines 472-487. *)
lemma test_rely_guar_not_p_any_guar:
  assumes stable_r: "stable p r"
  assumes stable_g: "stable p g"
  shows "\<tau> p ; rely r \<iinter> guar\<^sub>\<pi> g = \<tau> p ; rely r \<iinter> guar\<^sub>\<pi> (-(p \<triangleleft> UNIV) \<union> g)"
proof-
  have stable_pre_p: "stable p (p \<triangleleft> ((-(p \<triangleleft> UNIV)) \<union> g))"
    by (simp add: range_restricted_equiv_relation stable_pre_p_implies_stable stable_g)

  have stable_alt: "stable p ((-(p \<triangleleft> UNIV)) \<union> g)"
    by (metis stable_pre_p stable_pre_p_implies_stable)

  have "\<tau> p ; rely r \<iinter> guar\<^sub>\<pi> ((-(p \<triangleleft> UNIV)) \<union> g) = \<tau> p ; rely r \<iinter> guar\<^sub>\<pi> (p \<triangleleft> g)"
    by (simp add: range_restricted_equiv_relation stable_alt stable_r test_rely_guar_contrain_guar_domain)
  then show ?thesis
    by (simp add: stable_g stable_r test_rely_guar_contrain_guar_domain)
qed


(* Original lines 489-502. *)
lemma test_rely_guar_contrain_domain:
  assumes stable_r: "stable p r"
  assumes stable_g: "stable p g"
  shows "\<tau> p ; rely r \<iinter> guar\<^sub>\<pi> g = \<tau> p ; rely (p \<triangleleft> r) \<iinter> guar\<^sub>\<pi> (p \<triangleleft> g)"
proof-
  have stable_pr: "stable p (p \<triangleleft> r)"
    using domain_restrict_remove stable_r by blast

  have "\<tau> p ; rely r \<iinter> guar\<^sub>\<pi> g = \<tau> p ; rely (p \<triangleleft> r) \<iinter> guar\<^sub>\<pi> g"
    using stable_r stable_g test_rely_guar_contrain_rely_domain by simp
  also have "\<dots> = \<tau> p ; rely (p \<triangleleft> r) \<iinter> guar\<^sub>\<pi> (p \<triangleleft> g)"
    using stable_g stable_pr test_rely_guar_contrain_guar_domain[where r="p \<triangleleft> r"] by simp
  finally show ?thesis .
qed


(* Original lines 504-520. *)
lemma test_rely_guar_not_p_any:
  assumes stable_r: "stable p r"
  assumes stable_g: "stable p g"
  shows "\<tau> p ; rely r \<iinter> guar\<^sub>\<pi> g = \<tau> p ; rely (-(p \<triangleleft> UNIV) \<union> r) \<iinter> guar\<^sub>\<pi> (-(p \<triangleleft> UNIV) \<union> g)"
proof-
  have stable_pre_p: "stable p (p \<triangleleft> ((-(p \<triangleleft> UNIV)) \<union> g))"
    by (simp add: range_restricted_equiv_relation stable_pre_p_implies_stable stable_g)

  have stable_alt: "stable p ((-(p \<triangleleft> UNIV)) \<union> g)"
    by (metis stable_pre_p stable_pre_p_implies_stable)

  have "\<tau> p ; rely r \<iinter> guar\<^sub>\<pi> g = \<tau> p ; rely r \<iinter> guar\<^sub>\<pi> (-(p \<triangleleft> UNIV) \<union> g)"
    using stable_r stable_g test_rely_guar_not_p_any_guar by simp
  also have "\<dots> = \<tau> p ; rely (-(p \<triangleleft> UNIV) \<union> r) \<iinter> guar\<^sub>\<pi> (-(p \<triangleleft> UNIV) \<union> g)"
    by (simp add: stable_alt stable_r test_rely_guar_not_p_any_rely)
  finally show ?thesis .
qed
