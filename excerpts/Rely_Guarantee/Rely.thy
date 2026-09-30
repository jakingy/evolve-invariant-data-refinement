(* Extracts from isabelle/new_rg_algebra/Rely_Guarantee/Rely.thy. *)
(* These are source excerpts, not a standalone buildable theory. *)

(* Original lines 217-218. *)
lemma rely_pre: "seq.pre(rely r) = nil"
  using rely_not_immed_abort seq.not_immed_abort_def by auto


(* Original lines 274-283. *)
lemma rely_par_iter: 
  shows "rely r \<parallel> c\<^sup>\<omega> = (rely r \<parallel> c)\<^sup>\<omega>"  
proof -     
  have env: "env_assump r \<in> pure_seq_conj.PseudoAtom" 
    using env_assump_pseudo by auto 
  then show ?thesis 
    unfolding rely_def using pure_decomposes
      pure_seq_par.pseudo_atom.atom_iter_sync_iter[where a = "env_assump r" and c = c] 
    by blast
qed


(* Original lines 285-306. *)
lemma rely_distrib_step_atom: "rely r \<iinter> (\<pi> g \<squnion> \<epsilon> q) = \<pi> g \<squnion> \<epsilon> q \<squnion> \<epsilon>(-r \<sqinter> q) ; \<top>"
proof -
  have "rely r \<iinter> (\<pi> g \<squnion> \<epsilon> q)  = (\<A> \<squnion> \<epsilon>(-r) ; \<top>)\<^sup>\<omega> \<iinter> (\<pi> g \<squnion> \<epsilon> q)" 
    unfolding rely_def by simp 
  also have "\<dots> = ((\<A> \<squnion> \<epsilon>(-r) ; \<top>) \<iinter> (\<pi> g \<squnion> \<epsilon> q)) ; seq.pre (\<A> \<squnion> \<epsilon>(-r) ; \<top>)" 
    using env_assump_pseudo guar_basis_is_atom pure_seq_conj.pseudo_atom.atom_iter_sync_atom 
      pure_seq_par.atomic_is_pseudo_atomic pure_seq_par.pseudo_not_immed_abort seq.not_immed_abort_def 
      by force
  also have "... = (\<A> \<iinter> (\<pi> g \<squnion> \<epsilon> q)) \<squnion> (\<epsilon>(-r) ; \<top> \<iinter> (\<pi> g \<squnion> \<epsilon> q))" 
    using env_assump_pseudo pure_seq_par.pseudo_not_immed_abort seq.not_immed_abort_def 
      seq_conj.sup_sync by force 
  also have "\<dots> = \<pi> g \<squnion> \<epsilon> q \<squnion> (\<epsilon>(-r) \<iinter> (\<pi> g \<squnion> \<epsilon> q)) ; \<top>" 
    by (metis seq_conj.atom_sync_atom_top conj.iota_sync_compat env_atomic 
        guar_basis_is_atom local.conj.commute)
  also have "\<dots> = \<pi> g \<squnion> \<epsilon> q \<squnion> (\<epsilon>(-r) \<iinter> \<pi> g) ; (\<top> \<iinter> nil) \<squnion> (\<epsilon>(-r) \<iinter> \<epsilon> q) ; (\<top> \<iinter> nil)" 
    by (simp add: seq.sup_quantale.assoc seq_conj.abort_op2 seq_conj.sync_sup 
        seq_par.sup_seq)
  also have "\<dots> = \<pi> g \<squnion> \<epsilon> q \<squnion> \<epsilon>(-r \<sqinter> q) ; \<top>" 
    by (metis env_conj_env env_conj_pgm local.conj.commute local.conj.conj_abort 
        seq.bot_annihilates_left seq.sup_quantale.right_neutral)
  finally show ?thesis .
qed


(* Original lines 308-317. *)
lemma rely_conj_iter: 
  shows "rely r \<iinter> c\<^sup>\<omega> = (rely r \<iinter> c)\<^sup>\<omega>"  
proof -     
  have env: "env_assump r \<in> pure_seq_conj.PseudoAtom" 
    using env_assump_pseudo by auto 
  then show ?thesis 
    unfolding rely_def using pure_decomposes
      pure_seq_conj.pseudo_atom.atom_iter_sync_iter[where a = "env_assump r" and c = c]  
    by blast
qed


(* Original lines 319-328. *)
lemma rely_conj_pgm: "rely r \<iinter> \<pi> g = \<pi> g"
proof-
  have "rely r \<iinter> \<pi> g = rely r \<iinter> (\<pi> g \<squnion> \<epsilon> \<bottom>)"
    using env.hom_bot by auto
  also have "... = \<pi> g \<squnion> \<epsilon> \<bottom> \<squnion> \<epsilon> \<bottom> ; \<top>"
    using rely_distrib_step_atom by simp
  also have "... = \<pi> g"
    using env.hom_bot seq.bot_annihilates_left by fastforce
  finally show ?thesis .
qed


(* Original lines 330-339. *)
lemma rely_conj_env: "rely r \<iinter> \<epsilon> q = \<epsilon> q \<squnion> \<epsilon> (-r \<sqinter> q) ; \<top>"
proof-
  have "rely r \<iinter> \<epsilon> q = rely r \<iinter> (\<pi> \<bottom> \<squnion> \<epsilon> q)"
    using env.hom_bot by auto
  also have "... = \<pi> \<bottom> \<squnion> \<epsilon> q \<squnion> \<epsilon> (-r \<sqinter> q) ; \<top>"
    using rely_distrib_step_atom by simp
  also have "... = \<epsilon> q \<squnion> \<epsilon> (-r \<sqinter> q) ; \<top>"
    using env.hom_bot seq.bot_annihilates_left by fastforce
  finally show ?thesis .
qed


(* Original lines 341-370. *)
lemma rely_conj_env_assump: "rely r1 \<iinter> env_assump r2 = env_assump (r1 \<sqinter> r2)"
proof-
  have t1: "(rely r1 \<iinter> \<Pi>) =  \<Pi>"
    using rely_conj_pgm by auto

  have t2: "rely r1 \<iinter> \<E> = \<E> \<squnion> \<epsilon> (-r1) ; \<top>"
    using rely_conj_env by auto

  have t3: "(rely r1 \<iinter> \<epsilon> (-r2) ; (rely r1 \<iinter> \<top>)) = ((\<epsilon> (-r2) \<squnion> \<epsilon> ((-r1) \<sqinter> (-r2));\<top>); \<top>)"
    using local.conj.conj_abort rely_conj_env rely_conj_seq by fastforce

  have "rely r1 \<iinter> env_assump r2 = rely r1 \<iinter> (\<Pi> \<squnion> \<E> \<squnion> \<epsilon> (-r2) ; \<top>)"
    by (simp add: Atomic_def2)
  also have "... = (rely r1 \<iinter> \<Pi>) \<squnion> (rely r1 \<iinter> \<E>) \<squnion> (rely r1 \<iinter> \<epsilon> (-r2) ; (rely r1 \<iinter> \<top>))"
    by (simp add: seq_conj.sync_sup rely_conj_seq)
  also have "... = \<Pi> \<squnion> \<E> \<squnion> \<epsilon> (-r1) ; \<top> \<squnion> ((\<epsilon> (-r2) \<squnion> \<epsilon> ((-r1) \<sqinter> (-r2));\<top>); \<top>)"
    using t1 t2 t3
    by (simp add: seq.sup_quantale.assoc)
  also have "... = \<A> \<squnion> \<epsilon> ((-r1) \<squnion> (-r2)) ; \<top>"
  proof -
    have "\<epsilon> (- r2) = \<epsilon> (- r2) \<squnion> \<epsilon> (- r1 \<inter> - r2)"
      by (metis Int_Un_eq(4) env.hom_sup)
    then show ?thesis
      by (metis (no_types) env.hom_sup guar_basis_top seq.op_inf_biq.neut2_op_neut2_eq_neut2 
          seq.sup_quantale.assoc seq_par.seq_assoc seq_par.sup_seq)
  qed
  also have "... = \<A> \<squnion> \<epsilon> (-(r1 \<sqinter> r2)) ; \<top>"
    by simp
  finally show ?thesis by (simp only: env_assump_def) 
qed


(* Original lines 372-385. *)
lemma test_pre_env_assump:
  "\<tau> p ; env_assump r =
    \<alpha>(p \<triangleleft> UNIV) \<squnion> \<epsilon>(p \<triangleleft> (-r)) ; \<top>"
proof -
  have "\<tau> p ; env_assump r = \<tau> p ; (\<A> \<squnion> \<epsilon>(-r) ; \<top>)"
    by (simp only: env_assump_def sup_assoc)
  also have "\<dots> = \<tau> p ; \<A> \<squnion> \<tau> p ; (\<epsilon>(-r) ; \<top>)"
    by (simp add: seq_par.seq_sup sup_assoc)
  also have "\<dots> = \<tau> p ; \<A> \<squnion> \<tau> p ; \<epsilon>(-r) ; \<top>"
    by (simp add: seq_par.seq_assoc)
  also have "\<dots> = \<alpha>(p \<triangleleft> UNIV) \<squnion> \<epsilon>(p \<triangleleft> (-r)) ; \<top>"
    by (metis (full_types) aczel_atom_alt env_test_pre general_atomic_def guar_basis_top pgm_test_pre seq_par.seq_sup)
  finally show ?thesis .
qed


(* Original lines 387-413. *)
lemma assert_seq_env_assump: "\<lbrace>p\<rbrace> ; env_assump r = \<lbrace>p\<rbrace> ; env_assump (p \<triangleleft> r)"
proof -
  have dom_eq: "p \<triangleleft> r = p \<triangleleft> p \<triangleleft> r"
    by (auto simp: restrict_domain_def restrict_range_def)
  have dom_neg_eq: "p \<triangleleft> (-r) = p \<triangleleft> (-(p \<triangleleft> r))"
    by (auto simp: restrict_domain_def restrict_range_def)

  have tau_eq: "\<tau> p ; env_assump r = \<tau> p ; env_assump (p \<triangleleft> r)"
  proof -
    have "\<tau> p ; env_assump r = \<alpha>(p \<triangleleft> UNIV) \<squnion> \<epsilon>(p \<triangleleft> (-r)) ; \<top>"
      by (rule test_pre_env_assump)
    also have "\<dots> =  \<alpha>(p \<triangleleft> UNIV) \<squnion> \<epsilon>(p \<triangleleft> (-(p \<triangleleft> r))) ; \<top>"
      using dom_eq dom_neg_eq by simp
    also have "\<dots> = \<tau> p ; env_assump (p \<triangleleft> r)"
      by (simp only: test_pre_env_assump[symmetric])
    finally show ?thesis .
  qed


  have "\<lbrace>p\<rbrace> ; env_assump r = \<tau> p ; env_assump r \<squnion> seq.test.negate(\<tau> p) ; \<top>"
    by (simp add: seq.assert_op_alt)
  also have "\<dots> = \<tau> p ; env_assump (p \<triangleleft> r) \<squnion> seq.test.negate(\<tau> p) ; \<top>"
    using tau_eq by simp
  also have "\<dots> = \<lbrace>p\<rbrace> ; env_assump (p \<triangleleft> r)"
    by (simp add: seq.assert_op_alt)
  finally show ?thesis .
qed
