section \<open>Evolve command\<close>

theory Evolve
  imports Rely_Guarantee.Rely_Guarantee 
begin 

context constrained_aczel_cra
begin

subsection \<open>Evolve as a rely and guarantee\<close>
text \<open>The evolve command guarantees program transitions and assumes environments steps satisfy relation r.
All transitions will satisfy r or an environment transitions that does not satisfy r leads to abort.
Used primarily by the invariant command.\<close>
definition evolve :: "'state rel \<Rightarrow> 'a::complete_distrib_lattice" where
  "evolve r = rely r \<iinter> guar\<^sub>\<pi> r"

text \<open>The evolve command of the universal set does not assume anything nor guarantee anything.\<close>
lemma evolve_univ: "evolve UNIV = chaos"
proof -
  have "evolve UNIV = rely UNIV \<iinter> guar\<^sub>\<pi> UNIV"
    by (simp add: evolve_def)
  also have "\<dots> = chaos \<iinter> chaos"
    by (simp only: pgm_guar_top rely_top)
  also have "\<dots> = chaos"
    by (simp)
  finally show ?thesis .
qed

text \<open>The following lemmas describe the interaction between the evolve command and primitive commands.\<close>
lemma evolve_test: "evolve r \<iinter> \<tau> p1 = \<tau> p1" 
proof -
  have "evolve r \<iinter> \<tau> p1 = rely r \<iinter> guar\<^sub>\<pi> r \<iinter> \<tau> p1" 
    by (simp only: evolve_def)
  also have "\<dots> = rely r \<iinter> (guar\<^sub>\<pi> r \<iinter> \<tau> p1)"  
    by (simp only: conj.conj_assoc)
  also have "\<dots> = rely r \<iinter> \<tau> p1"
    by (simp only: pgm_guar_conj_test conj.commute)
  also have "\<dots> = \<tau> p1" 
    by (simp only: test_rely_conj conj.commute)
  finally show ?thesis .
qed

lemma evolve_conj_atom: "evolve r \<iinter> (\<pi> g \<squnion> \<epsilon> q) = \<pi> (r \<inter> g) \<squnion> \<epsilon> q \<squnion> \<epsilon> (-r \<inter> q) ; \<top>"
proof-
  have "evolve r \<iinter> (\<pi> g \<squnion> \<epsilon> q) = rely r \<iinter> guar\<^sub>\<pi> r \<iinter> (\<pi> g \<squnion> \<epsilon> q)"
    by (simp only: evolve_def)
  also have "\<dots> = rely r \<iinter> (\<pi> (r \<inter> g) \<squnion> \<epsilon> q)"
    by (simp only: pgm_guar_conj_atom conj.assoc)
  also have "\<dots> = \<pi> (r \<inter> g) \<squnion> \<epsilon> q \<squnion> (\<epsilon> (-r \<inter> q) ; \<top>)"
    by (simp only: rely_distrib_step_atom)
  finally show ?thesis .
qed

lemma evolve_conj_atom_alt: "evolve r \<iinter> (\<pi> g \<squnion> \<epsilon> q) = \<pi> (r \<inter> g) \<squnion> \<epsilon> (r \<inter> q) \<squnion> \<epsilon> (-r \<inter> q) ; \<top>"
proof-
  have split_r: "\<epsilon> q = \<epsilon> (r \<inter> q) \<squnion> \<epsilon> (-r \<inter> q)"
    by (metis Int_commute boolean_algebra.conj_one_right boolean_algebra.disj_cancel_right
        env.hom_sup seq.inf_quantale.weak_left_quantale_axioms
        weak_left_quantale.op_sup)

  have "evolve r \<iinter> (\<pi> g \<squnion> \<epsilon> q) = \<pi> (r \<inter> g) \<squnion> \<epsilon> q \<squnion> \<epsilon> (-r \<inter> q) ; \<top>"
    using evolve_conj_atom by auto
  also have "\<dots> = \<pi> (r \<inter> g) \<squnion> (\<epsilon> (r \<inter> q) \<squnion> \<epsilon> (-r \<inter> q)) \<squnion>  \<epsilon> (-r \<inter> q) ; \<top>"
    using split_r by auto
  also have "\<dots> =  \<pi> (r \<inter> g) \<squnion> \<epsilon> (r \<inter> q) \<squnion> (\<epsilon> (-r \<inter> q) \<squnion>  \<epsilon> (-r \<inter> q) ; \<top>)"
    by (simp add: seq.sup_quantale.assoc)

  finally show ?thesis
    by (simp add: seq.sup_op_top)
qed

lemma evolve_conj_pgm: "evolve r \<iinter> \<pi> g = \<pi> (r \<inter> g)"
proof-
  have "evolve r \<iinter> \<pi> g  = evolve r \<iinter> (\<pi> g \<squnion> \<epsilon> \<bottom>)"
    using env.hom_bot by auto
  also have "\<dots> = \<pi> (r \<inter> g) \<squnion> \<epsilon> \<bottom> \<squnion> \<epsilon> (-r \<inter> \<bottom>) ; \<top>"
    by (simp only: evolve_conj_atom)
  also have "\<dots> = \<pi> (r \<inter> g)"
    by (simp only: env.hom_bot inf_bot_right sup_bot_right seq.bot_annihilates_left)
  finally show ?thesis .
qed

lemma evolve_conj_env: "evolve r \<iinter> \<epsilon> q = \<epsilon> q \<squnion> (\<epsilon> (-r \<inter> q) ; \<top>)"
proof-
  have "evolve r \<iinter> \<epsilon> q = evolve r \<iinter> (\<pi> \<bottom> \<squnion> \<epsilon> q)"
    using pgm.hom_bot by auto
  also have "\<dots> = \<pi> (r \<inter> \<bottom>) \<squnion> \<epsilon> q \<squnion> \<epsilon> (-r \<inter> q) ; \<top>"
    by (simp only: evolve_conj_atom)
  also have "\<dots> = \<epsilon> q \<squnion> \<epsilon> (-r \<inter> q) ; \<top>"
    by (simp only: sup_bot_left pgm.hom_bot inf_bot_right)
  finally show ?thesis .
qed

text\<open>The precondition of the evolve command is nil.\<close>
lemma evolve_pre: "seq.pre(evolve r) = nil"
proof -
  have "seq.pre(evolve r) = seq.pre(rely r \<iinter> guar\<^sub>\<pi> r)"
    using evolve_def by simp
  also have "\<dots> =  seq.pre(rely r) ; seq.pre(guar\<^sub>\<pi> r)"
    by (simp add: seq_conj.pre_sync_is_seq)
  also have "\<dots> = nil"
    by (simp add: pgm_guar_pre rely_pre)
  finally show ?thesis .
qed

text \<open>Evolve command distributive laws.\<close>
lemma evolve_distrib_par: "evolve r \<iinter> (c1 \<parallel> c2) = (evolve r \<iinter> c1) \<parallel> (evolve r \<iinter> c2)"
proof -
  have "evolve r \<iinter> (c1 \<parallel> c2)  = rely r \<iinter> guar\<^sub>\<pi> r \<iinter> (c1 \<parallel> c2)"
    by (simp only: evolve_def)
  also have "\<dots> = (rely r \<iinter> guar\<^sub>\<pi> r \<iinter> c1) \<parallel> (rely r \<iinter> guar\<^sub>\<pi> r \<iinter> c2)" 
    by (simp only: rely_guar_par)
  then show ?thesis
    using evolve_def
    by (simp)
qed

lemma evolve_distrib_seq: "evolve r \<iinter> (c1 ; c2) = (evolve r \<iinter> c1) ; (evolve r \<iinter> c2)"
proof -
  have "evolve r \<iinter> (c1 ; c2)  = rely r \<iinter> guar\<^sub>\<pi> r \<iinter> (c1 ; c2)"
    by (simp only: evolve_def)
  also have "\<dots> = (rely r \<iinter> guar\<^sub>\<pi> r \<iinter> c1) ; (rely r \<iinter> guar\<^sub>\<pi> r \<iinter> c2)" 
    by (simp only: conj.assoc rely_conj_seq pgm_guar_conj_seq)
  then show ?thesis
    using evolve_def
    by (simp)
qed

lemma evolve_distrib_power: "evolve r \<iinter> c^i = (evolve r \<iinter> c)^i" 
  using evolve_distrib_seq evolve_pre seq_conj.distrib_fixed_iter_nil by simp

lemma evolve_distrib_fiter: "evolve r \<iinter> c* = (evolve r \<iinter> c)*" 
  using evolve_distrib_seq seq_conj.distributive_finite_iter by simp

lemma evolve_distrib_iter:
  shows "evolve r \<iinter> c\<^sup>\<omega> = (evolve r \<iinter> c)\<^sup>\<omega>"
proof -
  have "evolve r \<iinter> c\<^sup>\<omega> = rely r \<iinter> guar\<^sub>\<pi> r \<iinter> c\<^sup>\<omega>"
    by (simp only: evolve_def)
  also have "\<dots> = rely r \<iinter> (guar\<^sub>\<pi> r \<iinter> c)\<^sup>\<omega>" 
    by (simp only: conj.assoc pgm_guar_conj_iter)
  finally show ?thesis
    using rely_conj_iter[where c = "guar\<^sub>\<pi> r \<iinter> c"] evolve_def conj.assoc
    by auto
qed

subsection \<open>Basis of the evolve command\<close>
text \<open>The evolve command can be written as a psuedo atomic in an iter.\<close>
definition evolve_pseudo_atomic :: "'state rel \<Rightarrow> 'a::complete_distrib_lattice" where
  "evolve_pseudo_atomic r = \<pi> r \<squnion> \<epsilon> r \<squnion> \<epsilon>(-r) ; \<top>"

lemma evolve_pseudo_atomic_pseudo:
  "evolve_pseudo_atomic r \<in> pure_seq_par.PseudoAtom"
proof -
  have basis_atomic: "\<pi> r \<squnion> \<epsilon> r \<in> AczelAtom"
    by (rule guar_basis_is_atom)
  have env_atomic': "\<epsilon>(-r) \<in> AczelAtom"
    by (rule env_atomic)
  have "(\<pi> r \<squnion> \<epsilon> r) \<squnion> \<epsilon>(-r) ; \<top> \<in> pure_seq_conj.PseudoAtom"
    using basis_atomic env_atomic'
    by (rule pure_seq_par.pseudo_atomic_compose)
  then show ?thesis
    by (simp only: evolve_pseudo_atomic_def)
qed

lemma evolve_atomic_iter_def: "evolve r = (evolve_pseudo_atomic r)\<^sup>\<omega>"
proof -
  have "evolve r = rely r \<iinter> guar\<^sub>\<pi> r"
    by (simp add: evolve_def)
  also have "\<dots> = (\<pi> r \<squnion> \<epsilon> r \<squnion> \<epsilon>(-r) ; \<top>)\<^sup>\<omega>"
    by (simp only: rely_conj_guar)
  also have "\<dots> = (evolve_pseudo_atomic r)\<^sup>\<omega>"
    by (simp only: evolve_pseudo_atomic_def)
  finally show ?thesis .
qed

lemma test_pre_evolve_pseudo_atomic:
  "\<tau> p ; evolve_pseudo_atomic r = \<pi>(p \<triangleleft> r) \<squnion> \<epsilon>(p \<triangleleft> r) \<squnion> \<epsilon>(p \<triangleleft> (-r)) ; \<top>"
proof -
  have "\<tau> p ; evolve_pseudo_atomic r = \<tau> p ; (\<pi> r \<squnion> (\<epsilon> r \<squnion> \<epsilon>(-r) ; \<top>))"
    by (simp add: evolve_pseudo_atomic_def sup_assoc)
  also have "\<dots> = \<tau> p ; \<pi> r \<squnion> \<tau> p ; \<epsilon> r \<squnion> \<tau> p ; \<epsilon>(-r) ; \<top>"
    by (simp add: seq.sup_quantale.assoc seq_par.seq_assoc
        seq_par.seq_sup)
  also have "\<dots> = \<pi>(p \<triangleleft> r) \<squnion> \<epsilon>(p \<triangleleft> r) \<squnion> \<epsilon>(p \<triangleleft> (-r)) ; \<top>"
    by (simp only: pgm_test_pre env_test_pre seq_par.seq_assoc sup_assoc)
  finally show ?thesis .
qed

lemma evolve_pseudo_atomic_stable:
  assumes stable_r: "stable p r"
  shows "seq.test_stable p (evolve_pseudo_atomic r)"
proof -
  have "seq.test_stable p ((\<pi> r \<squnion> \<E>) \<iinter> env_assump r)"
    by (simp only: stable_r stable_implies_test_stable_pgm stable_implies_test_stable_env
      rely_guar_basis_stable)
  then show ?thesis
    by (simp only: pgm_restrict_conj_env_assump evolve_pseudo_atomic_def)
qed

lemma evolve_pseudo_atomic_range_restricted_stable: "seq.test_stable p (evolve_pseudo_atomic (UNIV \<triangleright> p))"
proof -
  have stable_restrict: "stable p (UNIV \<triangleright> p)"
    by (auto simp: restrict_range_def)
  then show ?thesis
    using stable_restrict evolve_pseudo_atomic_stable
    by (simp)
qed

text \<open>The evolve command on the universal relation with range constrained to p maintains p if it holds initially and does not abort.\<close>
lemma evolve_range_restricted_stable: "seq.test_stable p (evolve (UNIV \<triangleright> p))"
  by (simp add: evolve_atomic_iter_def evolve_pseudo_atomic_range_restricted_stable
      seq.stable_iter)

lemma test_stable_evolve_alt:
  assumes stable_r: "stable p r"
  shows "\<tau> p ; evolve r = \<tau> p ; evolve (p \<triangleleft> r)"
proof -
  have "\<tau> p ; evolve r = \<tau> p ; rely r \<iinter> guar\<^sub>\<pi> r"
    by (simp add: evolve_def local.conj.commute pgm_guar_conj_seq pgm_guar_conj_test)
  also have "\<dots> =  \<tau> p ; rely (p \<triangleleft> r) \<iinter> guar\<^sub>\<pi> (p \<triangleleft> r)"
    by (simp add: stable_r test_rely_guar_contrain_domain)
  finally show ?thesis
    by (simp add: evolve_def local.conj.commute pgm_guar_conj_seq pgm_guar_conj_test)
qed

lemma assert_stable_evolve_alt:
  assumes stable_r: "stable p r"
  shows "\<lbrace>p\<rbrace> ; evolve r = \<lbrace>p\<rbrace> ; evolve (p \<triangleleft> r)"
  by (simp add: seq.assert_op_alt stable_r test_stable_evolve_alt)

lemma test_stable_evolve_alt2:
  assumes stable_r: "stable p r"
  shows "\<tau> p ; evolve r = \<tau> p ; evolve (-(p \<triangleleft> UNIV) \<union> r)"
proof -
  have "\<tau> p ; evolve r = \<tau> p ; rely r \<iinter> guar\<^sub>\<pi> r"
    by (simp add: evolve_def local.conj.commute pgm_guar_conj_seq pgm_guar_conj_test)
  also have "\<dots> =  \<tau> p ; rely (-(p \<triangleleft> UNIV) \<union> r) \<iinter> guar\<^sub>\<pi> (-(p \<triangleleft> UNIV) \<union> r)"
    by (simp add: stable_r test_rely_guar_not_p_any)
  finally show ?thesis
    by (simp add: evolve_def local.conj.commute pgm_guar_conj_seq pgm_guar_conj_test)
qed

lemma assert_stable_evolve_alt2:
  assumes stable_r: "stable p r"
  shows "\<lbrace>p\<rbrace> ; evolve r = \<lbrace>p\<rbrace> ; evolve (-(p \<triangleleft> UNIV) \<union> r)"
  by (simp add: seq.assert_op_alt stable_r test_stable_evolve_alt2)

text \<open>The individual rely and guar parts of evolve can be extracted.\<close>
lemma evolve_extract_rely: "evolve r = evolve r \<iinter> rely r"
proof -
  have "evolve r = rely r \<iinter> guar\<^sub>\<pi> r"
    by (simp add: evolve_def)
  also have "\<dots> =  rely r \<iinter> rely r \<iinter> guar\<^sub>\<pi> r"
    by (simp only: conj.idem)
  also have "\<dots> = rely r \<iinter> guar\<^sub>\<pi> r \<iinter> rely r"
    using local.conj.commute seq_conj.sync_assoc by auto
  also have "\<dots> =  evolve r \<iinter> rely r"
    by (simp only: evolve_def)
  finally show ?thesis .
qed



lemma evolve_extract_guar: "evolve r = evolve r \<iinter> guar\<^sub>\<pi> r"
proof -
  have "evolve r = rely r \<iinter> guar\<^sub>\<pi> r"
    by (simp add: evolve_def)
  also have "\<dots> =  rely r \<iinter> (guar\<^sub>\<pi> r \<iinter> guar\<^sub>\<pi> r)"
    by (simp only: conj.idem)
  also have "\<dots> = rely r \<iinter> guar\<^sub>\<pi> r \<iinter> guar\<^sub>\<pi> r"
    using local.conj.commute seq_conj.sync_assoc by auto
  also have "\<dots> =  evolve r \<iinter> guar\<^sub>\<pi> r"
    by (simp only: evolve_def)
  finally show ?thesis .
qed

end
end
