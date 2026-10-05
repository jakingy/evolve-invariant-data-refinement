section \<open>Invariant\<close>

theory Invariant
  imports Rely_Guarantee.Evolve Atomic_Specification
begin 

context constrained_aczel_cra
begin

subsection\<open>Invariant as an assert and range restricted evolve\<close>
definition inv :: "'state set \<Rightarrow> 'a" where
  "inv I = \<lbrace>I\<rbrace> ; evolve (UNIV \<triangleright> I)"

text \<open>An assertion can be added before an invariant.\<close>
lemma inv_extract_assert: "inv I  = \<lbrace>I\<rbrace> ; inv I"
proof -
  have "\<lbrace>I\<rbrace> ; inv I = \<lbrace>I\<rbrace> ; \<lbrace>I\<rbrace> ; evolve (UNIV \<triangleright> I)"
    by (simp only: inv_def seq.assoc)
  also have "\<dots> = \<lbrace>I\<rbrace> ; evolve (UNIV \<triangleright> I)"
    by (simp add: seq.assert_op_assert_idem)
  also have "\<dots> = inv I"
    by (simp only: inv_def)
  finally show ?thesis
    by simp
qed

lemma inv_conj_extract_assert: "inv I \<iinter> c = inv I \<iinter> \<lbrace>I\<rbrace> ; c"
proof-
  have "inv I \<iinter> c = \<lbrace>I\<rbrace> ; inv I \<iinter> c"
    using inv_extract_assert by auto
  then show ?thesis
    by (simp add: seq_conj.assert_op_sync_left seq_conj.assert_op_sync_right)
qed

text \<open>An evolution invariant of the universal set does not assume anything nor guarantee anything.\<close>
lemma inv_univ: "inv UNIV = chaos"
proof -
  have "inv UNIV = \<lbrace>UNIV\<rbrace> ; evolve (UNIV \<triangleright> UNIV)"
    by (simp add: inv_def)
  also have "\<dots> = \<lbrace>UNIV\<rbrace> ; evolve UNIV"
    by (simp add: range_restrict_univ)
  also have "\<dots> = chaos"
    by (simp add: evolve_univ seq.assert_neut)
  finally show ?thesis .
qed

text \<open>The following lemmas describe the interaction between invariants and primitive commands.\<close>
lemma inv_test: "inv I \<iinter> \<tau> p1 = \<lbrace>I\<rbrace> ; \<tau> p1" 
proof -
  have "inv I \<iinter> \<tau> p1 = \<lbrace>I\<rbrace> ; evolve (UNIV \<triangleright> I) \<iinter> \<tau> p1" 
    by (simp only: inv_def)
  also have "\<dots> = \<lbrace>I\<rbrace> ; (evolve (UNIV \<triangleright> I) \<iinter> \<tau> p1)"
    by (simp only: seq_conj.assert_op_sync_right local.conj.commute)
  also have "\<dots> = \<lbrace>I\<rbrace> ; \<tau> p1"  
    by (simp only: evolve_test) 
  finally show ?thesis .
qed

lemma inv_test_alt: "inv I \<iinter> \<tau> p1 = \<lbrace>I\<rbrace> ; \<tau>(I \<inter> p1)"
  using inv_test seq.assert_op seq.assert_op_alt seq.test_inf seq.test_seq_test 
  by (metis seq.image_is_test)

text \<open>As a corollary to \<open>inv_test\<close>, we have that the invariant weak conjoined with nil is
just the corresponding assertion.\<close>
lemma inv_conj_nil: "inv I \<iinter> nil = \<lbrace>I\<rbrace>"
  using inv_test local.seq.seq_nil seq.test_set_top by auto

text \<open>The precondition of an invariant is just its corresponding assertion.\<close>
lemma inv_pre: "seq.pre(inv I) = \<lbrace>I\<rbrace>" 
proof -
  have "seq.pre(inv I) = seq.pre(\<lbrace>I\<rbrace> ; evolve (UNIV \<triangleright> I))" 
    using inv_def by simp 
  also have "\<dots> = seq.pre(\<lbrace>I\<rbrace> ; seq.pre(evolve(UNIV \<triangleright> I)))"
    using seq_par.pre_of_seq[where ?c1.0 = "\<lbrace>I\<rbrace>" and ?c2.0 = "evolve(UNIV \<triangleright> I)"] by simp
  also have "\<dots> = seq.pre(\<lbrace>I\<rbrace> ; nil)" 
    by (simp only: evolve_pre)
  also have "\<dots> = seq.pre(\<lbrace>I\<rbrace>)"
    by (simp only: seq.seq_nil)
  also have "\<dots> = \<lbrace>I\<rbrace>"  
    by (simp only: seq_conj.pre_assert)
  finally show ?thesis .
qed

text\<open>Alternate invariant definitions.\<close>
lemma inv_alt_def2: "inv I = \<lbrace>I\<rbrace> ; evolve (I \<triangleleft> (UNIV \<triangleright> I))"
proof -
  have "stable I (UNIV \<triangleright> I)"
    by (auto simp: restrict_range_def)
  then show ?thesis
    by (simp add: assert_stable_evolve_alt local.inv_def)   
qed

lemma inv_alt_def3: "inv I = \<lbrace>I\<rbrace> ; evolve (-(I \<triangleleft> UNIV) \<union> (UNIV \<triangleright> I))"
proof -
   have "stable I (UNIV \<triangleright> I)"
    by (auto simp: restrict_range_def)
  then show ?thesis
    by (simp add: assert_stable_evolve_alt2 local.inv_def)  
qed

subsection\<open>Invariant as a weak atomic\<close>
definition inv_weak_atomic :: "'state set \<Rightarrow> 'a" where
  "inv_weak_atomic I = \<lbrace>I\<rbrace> ; evolve_pseudo_atomic (UNIV \<triangleright> I)"

text\<open>An invariant is a weak atomic iterated.\<close>
lemma inv_atomic_iter_def: "inv I = (inv_weak_atomic I)\<^sup>\<omega>"
proof -
  have "inv I = \<lbrace>I\<rbrace> ; (evolve_pseudo_atomic (UNIV \<triangleright> I))\<^sup>\<omega>"
    by (simp only: inv_def evolve_atomic_iter_def)
  also have "\<dots> = (\<lbrace>I\<rbrace> ; evolve_pseudo_atomic (UNIV \<triangleright> I))\<^sup>\<omega>"
    using evolve_pseudo_atomic_range_restricted_stable
    by (rule stable_iter_maintain_assert)
  also have "\<dots> = (inv_weak_atomic I)\<^sup>\<omega>"
    by (simp only: inv_weak_atomic_def)
  finally show ?thesis .
qed

subsection \<open>More invariant laws\<close>
text \<open>The following lemmas describe how invariants distribute over
non-deterministic choice, sequential composition and parallel composition
and into fixed, finite, possibly infinite and infinite iterations.
Distribution over weak conjunction is trivial, so a lemma is not needed.\<close>

text \<open>The invariant is established after the invariant command.\<close>
lemma inv_establish: "inv I ; \<lbrace>I\<rbrace> = inv I"
proof -
  have finite_iter: "inv I = ((inv_weak_atomic I)\<^sup>\<omega>)*"
    by (simp add: inv_atomic_iter_def seq.iter_finite_iter)

  have "inv I ; \<lbrace>I\<rbrace> =  inv I ; seq.pre(inv I)"
    by (simp add: inv_pre)
  also have "\<dots> = ((inv_weak_atomic I)\<^sup>\<omega>)* ; seq.pre((inv_weak_atomic I)\<^sup>\<omega>)"
    by (simp add: inv_atomic_iter_def seq.iter_finite_iter)
  also have "\<dots> = inv I"
    by (simp add: finite_iter seq.finite_iter_seq_pre)
  finally show ?thesis .
qed

text \<open>An invariant of \<open>I\<close> establishes a test of \<open>p\<close>.\<close>
lemma inv_establish_test: "inv I = inv I ; \<tau> I" 
  by (metis inv_establish inv_pre seq.guard_test seq.pre_seq_guard seq_par.seq_assoc)

text\<open>An invariant is stable under its condition.\<close>
lemma inv_stable: "seq.test_stable I (inv I)"
  using inv_establish_test inv_extract_assert seq.test_assert_galois seq.test_stable_def
  by auto

lemma inv_conj_stable: "seq.test_stable I (inv I \<iinter> c)"  
  by (simp add: inv_stable seq_conj.stable_conj_stable)

text\<open>A command weak conjoined with an invariant will satisfy I after.\<close>
lemma inv_conj_right_assert: "inv I \<iinter> c = (inv I \<iinter> c) ; \<lbrace>I\<rbrace>"
proof-
  have "inv I \<iinter> c = \<lbrace>I\<rbrace> ; inv I \<iinter> c"
    using inv_extract_assert by auto
  also have "\<dots> = \<lbrace>I\<rbrace> ; (inv I \<iinter> c)"
    by (simp add: seq_conj.assert_op_sync_left)
  also have "\<dots> = \<lbrace>I\<rbrace> ; (inv I \<iinter> c) ; \<lbrace>I\<rbrace>"
    using seq_par.assert_stable_assert inv_conj_stable by auto
  finally show ?thesis
    using \<open>\<lbrace>I\<rbrace> ; local.inv I \<iinter> c = \<lbrace>I\<rbrace> ; (local.inv I \<iinter> c)\<close> \<open>local.inv I \<iinter> c = \<lbrace>I\<rbrace> ; local.inv I \<iinter> c\<close> by argo
qed

text\<open>Distribution laws\<close>
lemma inv_distrib_Sup: "inv I \<iinter> \<Squnion>C = \<lbrace>I\<rbrace> ; (\<Squnion>c \<in> C. inv I \<iinter> c)" 
 by (metis SUP_empty Sup_empty conj.op_Sup_nonempty inv_extract_assert inv_test seq.test_Union
      seq_conj.assert_op_sync_left)

lemma inv_distrib_seq: "inv I \<iinter> (c1 ; c2) = (inv I \<iinter> c1) ; (inv I \<iinter> c2)"  
proof -
  have evolve: "inv I \<iinter> (c1 ; c2) = \<lbrace>I\<rbrace> ; evolve (UNIV \<triangleright> I) \<iinter> (c1 ; c2)" 
    by (simp add: local.inv_def inv_extract_assert)
  also have "\<dots> = \<lbrace>I\<rbrace> ; (evolve (UNIV \<triangleright> I) \<iinter> (c1;c2))"
    by (simp only: conj.commute seq_conj.assert_op_sync_right)
  also have "\<dots> = (inv I \<iinter> c1) ; (evolve (UNIV \<triangleright> I) \<iinter> c2)"
    by (simp add: evolve_distrib_seq local.inv_def seq_conj.assert_op_sync_left seq_par.seq_assoc)
  also have "\<dots> = (inv I \<iinter> c1) ; \<lbrace>I\<rbrace> ; (evolve (UNIV \<triangleright> I) \<iinter> c2)"
    using inv_conj_right_assert by auto
  also have "\<dots> = (inv I \<iinter> c1) ; (inv I \<iinter> c2)"
    by (simp add: inv_def seq.assoc seq_conj.assert_op_sync_left)
  finally show ?thesis .
qed

lemma inv_distrib_par: "inv I \<iinter> (c1 \<parallel> c2) = (inv I \<iinter> c1) \<parallel> (inv I \<iinter> c2)"
proof -
  have "inv I \<iinter> (c1 \<parallel> c2) = \<lbrace>I\<rbrace> ; (evolve (UNIV \<triangleright> I) \<iinter> (c1 \<parallel> c2))" 
    using inv_def seq_conj.assert_op_sync_left by simp 
  also have "\<dots> = \<lbrace>I\<rbrace> ; (evolve (UNIV \<triangleright> I) \<iinter> c1 \<parallel> evolve (UNIV \<triangleright> I) \<iinter> c2)" 
    by (simp only: evolve_distrib_par)
  also have "\<dots> = (\<lbrace>I\<rbrace> ; evolve (UNIV \<triangleright> I) \<iinter> c1 \<parallel> \<lbrace>I\<rbrace> ; evolve (UNIV \<triangleright> I) \<iinter> c2)" 
    by (simp add: conj.conj_commute seq_conj.assert_op_sync_right seq_par.assert_op_sync') 
  also have "\<dots> = (inv I \<iinter> c1) \<parallel> (inv I \<iinter> c2)" 
    by (simp only: inv_def)
  finally show ?thesis .
qed

lemma inv_distrib_power: "inv I \<iinter> c^i = \<lbrace>I\<rbrace> ; (inv I \<iinter> c)^i" 
  using inv_distrib_seq inv_pre seq_conj.distrib_fixed_iter_nil by simp

lemma inv_distrib_fiter: "inv I \<iinter> c* = (inv I \<iinter> c)*" 
  using inv_distrib_seq seq_conj.distributive_finite_iter by simp 

lemma inv_distrib_iter: "inv I \<iinter> c\<^sup>\<omega> = (inv I \<iinter> c)\<^sup>\<omega>" 
proof -
  have stable_ec: "seq.test_stable I (evolve (UNIV \<triangleright> I) \<iinter> c)"
    using evolve_range_restricted_stable seq_conj.stable_conj_stable
    by auto

  have "inv I \<iinter> c\<^sup>\<omega> = \<lbrace>I\<rbrace> ; evolve (UNIV \<triangleright> I) \<iinter> c\<^sup>\<omega>"
    by (simp only: inv_def)
  also have "\<dots> = \<lbrace>I\<rbrace> ; (evolve (UNIV \<triangleright> I) \<iinter> c)\<^sup>\<omega>"
    by (simp only: evolve_distrib_iter seq_conj.assert_op_sync_left)
  also have "\<dots> = (\<lbrace>I\<rbrace> ; (evolve (UNIV \<triangleright> I) \<iinter> c))\<^sup>\<omega>"
    using stable_ec
    by (rule stable_iter_maintain_assert)
  also have "\<dots> = (inv I \<iinter> c)\<^sup>\<omega>"
    by (simp add: local.inv_def seq_conj.assert_op_sync_left)
  finally show ?thesis .  
qed

lemma inv_distrib_infiter: "inv I \<iinter> c\<^sup>\<infinity> = (inv I \<iinter> c)\<^sup>\<infinity>" 
  by (metis inf_as_conj inv_distrib_iter seq_conj.sync_assoc)

text \<open>An invariant weak conjoined with an assert is an assertion of the intersection of
conditions for the invariant and assertion.\<close>
lemma inv_assert: "inv I \<iinter> \<lbrace>p1\<rbrace> = \<lbrace>I \<inter> p1\<rbrace>" 
proof -
  have "inv I \<iinter> \<lbrace>p1\<rbrace> = \<lbrace>p1\<rbrace> ; (inv I \<iinter> nil)" 
    by (metis seq.seq_nil seq_conj.assert_op_sync_right)
  also have "\<dots> = \<lbrace>p1\<rbrace> ; \<lbrace>I\<rbrace>" 
    using inv_conj_nil by simp 
  also have "\<dots> = \<lbrace>I \<inter> p1\<rbrace>" 
    by (simp add: inf_commute seq.assert_op_assert seq.assert_op_test)
  finally show ?thesis .
qed

lemma inv_extract_rely: "inv I = inv I \<iinter> rely (UNIV \<triangleright> I)"
  using evolve_extract_rely inv_def seq_conj.assert_op_sync_left by auto

lemma inv_extract_rely3: "inv I = inv I \<iinter> rely (-(I \<triangleleft> UNIV) \<union> (UNIV \<triangleright> I))"
  using evolve_extract_rely inv_alt_def3 seq_conj.assert_op_sync_left by auto

text\<open>Can also extract the invariant's domain and range-restricted rely.\<close>
lemma inv_extract_rely2: "inv I = inv I \<iinter> rely (I \<triangleleft> (UNIV \<triangleright> I))"
proof-
  let ?r = "I \<triangleleft> (UNIV \<triangleright> I)"
  have "inv I = \<lbrace>I\<rbrace> ; (rely ?r \<iinter> guar\<^sub>\<pi> ?r)"
    by (simp add: inv_alt_def2 evolve_def)
  also have "... = \<lbrace>I\<rbrace> ; (rely ?r \<iinter> rely ?r \<iinter> guar\<^sub>\<pi> ?r)"
    by (simp only: conj.idem)
  also have "... = (\<lbrace>I\<rbrace> ; (rely ?r \<iinter> guar\<^sub>\<pi> ?r) \<iinter> rely ?r)"
    using conj.commute seq_conj.assert_op_sync_right seq_conj.sync_assoc by auto
  also have "... = inv I \<iinter> rely ?r"
    by (simp only: inv_alt_def2 evolve_def)
  finally show ?thesis .
qed

text \<open>inv_def_alt3 is useful if you need reflexive rely conditions.\<close>
lemma inv_rely_refl:
  "refl (-(I \<triangleleft> UNIV) \<union> (UNIV \<triangleright> I))"
proof (rule reflI)
  fix \<sigma>
  show "(\<sigma>, \<sigma>) \<in> -(I \<triangleleft> UNIV) \<union> (UNIV \<triangleright> I)"
  proof (cases "\<sigma> \<in> I")
    case True
    then show ?thesis  by (simp add: restrict_range_def)
  next
    case False
    then show ?thesis by (simp add: restrict_domain_def)
  qed
qed

text \<open>Invariant relation preserves the invariant.\<close>
lemma inv_rely_stable:
  "stable I (-(I \<triangleleft> UNIV) \<union> (UNIV \<triangleright> I))"
  unfolding stable_def restrict_domain_def restrict_range_def
  by blast

lemma inv_extract_rely_assert: "inv I \<iinter> c = inv I \<iinter> rely (UNIV \<triangleright> I) \<iinter> \<lbrace>I\<rbrace> ; c"
  using inv_conj_extract_assert inv_extract_rely by auto

lemma inv_extract_rely_assert3: "inv I \<iinter> c = inv I \<iinter> rely (-(I \<triangleleft> UNIV) \<union> (UNIV \<triangleright> I)) \<iinter> \<lbrace>I\<rbrace> ; c"
  using inv_conj_extract_assert inv_extract_rely3 by auto

text \<open>Unpack invariant in existing rely-guarantee.\<close>
lemma inv_extract_context:
  "inv I \<iinter> (rely r \<iinter> guar\<^sub>\<pi> g \<iinter> c) =
    inv I \<iinter>
      (rely (r \<inter> (-(I \<triangleleft> UNIV) \<union> (UNIV \<triangleright> I))) \<iinter>
        guar\<^sub>\<pi> g \<iinter> (\<lbrace>I\<rbrace> ; c))"
proof -
  let ?R = "-(I \<triangleleft> UNIV) \<union> (UNIV \<triangleright> I)"
  have combine_relies:
    "rely ?R \<iinter> rely r = rely (r \<inter> ?R)"
    by (simp add: rely_conj_rely local.conj.commute)
  have absorb_combined_rely:
    "rely ?R \<iinter> rely (r \<inter> ?R) = rely (r \<inter> ?R)"
  proof-
    have "?R \<inter> (r \<inter> ?R) = (r \<inter> ?R)"
      by (simp add: Int_absorb1)
    then show ?thesis using rely_conj_rely by simp
  qed
  have lhs_normal:
    "inv I \<iinter> (rely r \<iinter> guar\<^sub>\<pi> g \<iinter> c) = \<lbrace>I\<rbrace> ; (rely ?R \<iinter> guar\<^sub>\<pi> ?R \<iinter> rely r \<iinter> guar\<^sub>\<pi> g \<iinter> c)"
    by (simp add: evolve_def inv_alt_def3 seq_conj.assert_op_sync_left seq_conj.sync_assoc)
  have rhs_normal:
    "inv I \<iinter> (rely (r \<inter> ?R) \<iinter> guar\<^sub>\<pi> g \<iinter> (\<lbrace>I\<rbrace> ; c))
   = \<lbrace>I\<rbrace> ; (rely ?R \<iinter> guar\<^sub>\<pi> ?R \<iinter> rely (r \<inter> ?R) \<iinter> guar\<^sub>\<pi> g \<iinter> c)"
  proof -
    have "local.inv I \<iinter> (rely (r \<inter> (- I \<triangleleft> UNIV \<union> UNIV \<triangleright> I)) \<iinter> guar\<^sub>\<pi> g \<iinter> \<lbrace>I\<rbrace> ; c) = \<lbrace>I\<rbrace> ; (evolve (- I \<triangleleft> UNIV \<union> UNIV \<triangleright> I) \<iinter> (rely (r \<inter> (- I \<triangleleft> UNIV \<union> UNIV \<triangleright> I)) \<iinter> guar\<^sub>\<pi> g \<iinter> c))"
      using inv_alt_def3 seq_conj.assert_op_sync' seq_conj.assert_op_sync_right by auto
    then show ?thesis
      using evolve_def seq_conj.sync_assoc by auto
  qed

  have "inv I \<iinter> (rely r \<iinter> guar\<^sub>\<pi> g \<iinter> c) = \<lbrace>I\<rbrace> ; (rely ?R \<iinter> guar\<^sub>\<pi> ?R \<iinter> rely r \<iinter> guar\<^sub>\<pi> g \<iinter> c)"
      by (rule lhs_normal)
  also have "\<dots> = inv I \<iinter> (rely (r \<inter> ?R) \<iinter> guar\<^sub>\<pi> g \<iinter> (\<lbrace>I\<rbrace> ; c))"
  proof -
    have "rely (- I \<triangleleft> UNIV \<union> UNIV \<triangleright> I) \<iinter> guar\<^sub>\<pi> (- I \<triangleleft> UNIV \<union> UNIV \<triangleright> I) \<iinter> rely (r \<inter> (- I \<triangleleft> UNIV \<union> UNIV \<triangleright> I)) = rely (- I \<triangleleft> UNIV \<union> UNIV \<triangleright> I) \<iinter> (guar\<^sub>\<pi> (- I \<triangleleft> UNIV \<union> UNIV \<triangleright> I) \<iinter> rely r)"
      by (simp add: combine_relies local.conj.conj_conj)
    then show ?thesis
      using rhs_normal seq_conj.sync_assoc by auto
  qed
  finally show ?thesis by simp
qed

text \<open>The Hoare-triple form of \<open>inv_extract_context\<close>.\<close>
lemma inv_extract_context_triple:
  "{. p0 .} inv I \<iinter> (rely r \<iinter> guar\<^sub>\<pi> g \<iinter> c) {. q .}
   \<longleftrightarrow>
   {. p0 .} inv I \<iinter>
      (rely (r \<inter> (-(I \<triangleleft> UNIV) \<union> (UNIV \<triangleright> I))) \<iinter>
        guar\<^sub>\<pi> g \<iinter> (\<lbrace>I\<rbrace> ; c)) {. q .}"
  using inv_extract_context by simp

lemma inv_rely_restrict:
  "inv I \<iinter> rely r \<iinter> c =
    inv I \<iinter> rely (I \<triangleleft> r \<triangleright> I) \<iinter> c"
proof -
  have restrict_rely: "(I \<triangleleft> (UNIV \<triangleright> I)) \<inter> r = I \<triangleleft> r \<triangleright> I"
    unfolding restrict_domain_def restrict_range_def
    by blast
  have invariant_rely:
    "inv I \<iinter> rely r \<iinter> c = inv I \<iinter> rely (I \<triangleleft> (UNIV \<triangleright> I)) \<iinter> rely r \<iinter> c"
    using inv_extract_rely2
    by (metis conj.commute)
  also have "\<dots> = inv I \<iinter> rely ((I \<triangleleft> (UNIV \<triangleright> I)) \<inter> r) \<iinter> c"
    by (simp add: rely_conj_rely seq_conj.sync_assoc)
  also have "\<dots> = inv I \<iinter> rely (I \<triangleleft> r \<triangleright> I) \<iinter> c"
    using restrict_rely by simp
  finally show ?thesis .
qed

lemma inv_rely_restrict_cong:
  assumes "rely (I \<triangleleft> r \<triangleright> I) \<iinter> c = rely (I \<triangleleft> r \<triangleright> I) \<iinter> d"
  shows "inv I \<iinter> rely r \<iinter> c = inv I \<iinter> rely r \<iinter> d"
proof -
  have restrict_d: "inv I \<iinter> rely r \<iinter> d =  inv I \<iinter> rely (I \<triangleleft> r \<triangleright> I) \<iinter> d"
    by (rule inv_rely_restrict)
  have "inv I \<iinter> rely r \<iinter> c = inv I \<iinter> rely (I \<triangleleft> r \<triangleright> I) \<iinter> c"
    by (rule inv_rely_restrict)
  also have "\<dots> = inv I \<iinter> rely r \<iinter> d"
    using assms restrict_d seq_conj.sync_assoc by auto
  finally show ?thesis .
qed

text \<open>An invariant can be introduced provided it holds initially and a sufficient rely is present.\<close>
lemma inv_introduce_eq:
  assumes stable_r: "stable I r"
  shows "rely r \<iinter> guar\<^sub>\<pi> (UNIV \<triangleright> I) \<iinter> \<lbrace>I\<rbrace> ; c = rely r \<iinter> inv I \<iinter> c"
proof -
  have image_of_p_in_p: "I \<triangleleft> r = I \<triangleleft> r \<triangleright> I"
    by (meson assms stable_maintains_invariant)
  have split_r: "I \<triangleleft> r \<triangleright> I = r \<inter> (I \<triangleleft> (UNIV \<triangleright> I))"
    by (metis domain_restrict_inter range_restrict_inter seq.inf_quantale.right_neutral 
        seq.sup_inf_biq.op2.left_commute)
  have split_rely: "rely (I \<triangleleft> r \<triangleright> I) = rely r \<iinter> rely (I \<triangleleft> (UNIV \<triangleright> I))"
    by (simp add: rely_conj_rely split_r)
  have stable_domain_constrain: "stable I (UNIV \<triangleright> I)"
    by (simp add: range_restrict_image)
  have with_guar_eq: "rely r \<iinter> guar\<^sub>\<pi> (UNIV \<triangleright> I) \<iinter> \<lbrace>I\<rbrace> ; c = rely r \<iinter> inv I \<iinter> c"
  proof-
    have "rely r \<iinter> guar\<^sub>\<pi> (UNIV \<triangleright> I) \<iinter> \<lbrace>I\<rbrace> ; c =  (\<lbrace>I\<rbrace> ; rely r \<iinter> guar\<^sub>\<pi> (UNIV \<triangleright> I)) \<iinter> c"
      by (simp add: seq_conj.assert_op_sync_left seq_conj.assert_op_sync_right)
    also have "\<dots> = ((\<lbrace>I\<rbrace> ; \<tau> I) ; rely r \<iinter> guar\<^sub>\<pi> (UNIV \<triangleright> I)) \<iinter> c"
      by (simp add: seq.assert_op_test_idem)
    also have "\<dots> = ((\<lbrace>I\<rbrace> ; \<tau> I) ; rely (I \<triangleleft> r) \<iinter> guar\<^sub>\<pi> (I \<triangleleft> (UNIV \<triangleright> I))) \<iinter> c"
      by (simp add: assms seq_conj.assert_op_sync_left seq_par.seq_assoc stable_domain_constrain test_rely_guar_contrain_domain)
    also have "\<dots> = (\<lbrace>I\<rbrace> ; rely (I \<triangleleft> r \<triangleright> I) \<iinter> guar\<^sub>\<pi> (I \<triangleleft> (UNIV \<triangleright> I))) \<iinter> c"
      using image_of_p_in_p seq.assert_op_test_idem by auto
    also have "\<dots> = (\<lbrace>I\<rbrace> ; (rely r \<iinter> rely (I \<triangleleft> (UNIV \<triangleright> I))) \<iinter> guar\<^sub>\<pi> (I \<triangleleft> (UNIV \<triangleright> I))) \<iinter> c"
      by (simp add: split_rely)
    also have "\<dots> = rely r \<iinter> inv I \<iinter> c"
      by (simp add: evolve_def inv_alt_def2 local.conj.commute local.conj.left_commute seq_conj.assert_op_sync_right)
    finally show ?thesis .
  qed
  then show ?thesis .
qed

lemma inv_introduce: 
  assumes "stable I r"
  shows "rely r \<iinter> \<lbrace>I\<rbrace> ; c \<ge> rely r \<iinter> inv I \<iinter> c"
proof -
  have "rely r \<iinter> \<lbrace>I\<rbrace> ; c \<ge> rely r \<iinter> guar\<^sub>\<pi> (UNIV \<triangleright> I) \<iinter> \<lbrace>I\<rbrace> ; c " (is "_ \<ge> ?rhs")
    by (metis local.conj.commute pgm_guar_introduce seq_conj.sync_mono_left)
  also have "?rhs = rely r \<iinter> inv I \<iinter> c"
    using inv_introduce_eq assms by simp
  finally show ?thesis
    using evolve_extract_guar local.conj.commute local.conj.left_commute local.inv_def seq_conj.assert_op_sync_left by auto
qed

lemma inv_introduce_alt: "rely (UNIV \<triangleright> I) \<iinter> \<lbrace>I\<rbrace> ; c \<ge> inv I \<iinter> c"
proof -
  have stable_domain_constrain: "stable I (UNIV \<triangleright> I)"
    by (simp add: range_restrict_image)

  have "inv I \<iinter> c = rely (UNIV \<triangleright> I) \<iinter> inv I \<iinter> c"
    using inv_extract_rely local.conj.commute by auto

  then show ?thesis
    by (simp add: inv_introduce stable_domain_constrain)
qed

lemma inv_introduce_from_pre:
  assumes "p \<subseteq> I"
  shows "rely (UNIV \<triangleright> I) \<iinter> \<lbrace>p\<rbrace> ; c \<ge> inv I \<iinter> \<lbrace>p\<rbrace> ; c"
proof -
  have "\<lbrace>I\<rbrace> ; \<lbrace>p\<rbrace> = \<lbrace>p\<rbrace>"
    by (metis assms seq.assert_op_commute seq.assert_seq_implied_assert)
  then show ?thesis
    by (metis inv_introduce_alt seq_par.seq_assoc)
qed

lemma inv_inv: "(rely (UNIV \<triangleright> I) \<iinter> \<lbrace>I\<rbrace> ; c \<ge> inv I \<iinter> d) \<longleftrightarrow> (inv I \<iinter> c \<ge> inv I \<iinter> d)" 
proof (rule iffI)
  show "(rely (UNIV \<triangleright> I) \<iinter> \<lbrace>I\<rbrace> ; c \<ge> inv I \<iinter> d) \<Longrightarrow> (inv I \<iinter> c \<ge> inv I \<iinter> d)" 
  proof -
    assume assm: "rely (UNIV \<triangleright> I) \<iinter> \<lbrace>I\<rbrace> ; c \<ge> inv I \<iinter> d"
    have "inv I \<iinter> c = inv I \<iinter> rely (UNIV \<triangleright> I) \<iinter> \<lbrace>I\<rbrace> ; c"
      using inv_extract_rely_assert by blast
    also have "\<dots> \<ge> inv I \<iinter> d"
    proof -
      have "inv I \<iinter> (inv I \<iinter> d) \<le> inv I \<iinter> (\<lbrace>I\<rbrace> ; c \<iinter> rely (UNIV \<triangleright> I))"
        by (metis assm local.conj.commute seq_conj.sync_mono_right)
      then show ?thesis
        using seq_conj.sync_assoc seq_conj.sync_commute by fastforce
    qed
    finally show ?thesis .
  qed
  show "inv I \<iinter> c \<ge> inv I \<iinter> d \<Longrightarrow> rely (UNIV \<triangleright> I) \<iinter> \<lbrace>I\<rbrace> ; c \<ge> inv I \<iinter> d"
    using inv_introduce_alt order_trans by blast
qed

text \<open>An evolve invariant of \<open>I\<^sub>1\<close> can be strengthened to an invariant of \<open>p\<^sub>2\<close> provided \<open>p\<^sub>2\<close> 
      holds initially and the rely for \<open>I2\<close> is introduced\<close>
lemma inv_strengthen:
  assumes "I\<^sub>1 \<supseteq> I\<^sub>2"
  assumes "I\<^sub>2 \<triangleleft> (r \<triangleright> I\<^sub>1) \<subseteq> UNIV \<triangleright> I\<^sub>2"
  shows "\<lbrace>I\<^sub>2\<rbrace> ; (inv I\<^sub>1 \<iinter> rely r) \<ge> inv I\<^sub>2"
proof -
  have r2_le_r1: "UNIV \<triangleright> I\<^sub>2 \<subseteq> UNIV \<triangleright> I\<^sub>1"
    using assms(1)
    by (rule range_restrict_p_mono)

  have rely_absorb: "rely r \<iinter> rely (UNIV \<triangleright> I\<^sub>1) = rely (r \<triangleright> I\<^sub>1)"
  proof-
    have "r \<inter> (UNIV \<triangleright> I\<^sub>1) = r \<triangleright> I\<^sub>1"
      by (metis Int_commute boolean_algebra.conj_one_right range_restrict_inter)
    then show ?thesis
      by (simp add: rely_conj_rely)
  qed

  have stable_p2_range_restrict: "stable I\<^sub>2 (UNIV \<triangleright> I\<^sub>2)"
    by (simp add: range_restrict_image)

  have stable_p2_r: "stable I\<^sub>2 (r \<triangleright> I\<^sub>1)"
    by (metis assms(2) domain_restrict_remove inf.absorb_iff2 range_restrict_inter stable_def2 top_greatest)

  have restrict_guar: "\<lbrace>I\<^sub>2\<rbrace> ; (inv I\<^sub>1 \<iinter> rely r) \<ge> \<lbrace>I\<^sub>2\<rbrace> ; (rely (UNIV \<triangleright> I\<^sub>1) \<iinter> guar\<^sub>\<pi> (UNIV \<triangleright> I\<^sub>2) \<iinter> rely r)"
  proof-
     have "\<lbrace>I\<^sub>2\<rbrace> ; (inv I\<^sub>1 \<iinter> rely r) = \<lbrace>I\<^sub>2\<rbrace> ; ((\<lbrace>I\<^sub>1\<rbrace> ; rely (UNIV \<triangleright> I\<^sub>1) \<iinter> guar\<^sub>\<pi> (UNIV \<triangleright> I\<^sub>1)) \<iinter> rely r)"
      by (simp add: evolve_def local.inv_def seq_conj.assert_op_sync_left)
    also have "\<dots> = \<lbrace>I\<^sub>2\<rbrace> ; \<lbrace>I\<^sub>1\<rbrace> ;  (rely (UNIV \<triangleright> I\<^sub>1) \<iinter> guar\<^sub>\<pi> (UNIV \<triangleright> I\<^sub>1) \<iinter> rely r)"
      by (simp add: seq_conj.assert_op_sync_left seq_par.seq_assoc)
    also have "\<dots> = \<lbrace>I\<^sub>2\<rbrace> ; (rely (UNIV \<triangleright> I\<^sub>1) \<iinter> guar\<^sub>\<pi> (UNIV \<triangleright> I\<^sub>1) \<iinter> rely r)"
      by (simp add: assms(1) seq.assert_seq_implied_assert)
    also have "\<dots> \<ge> \<lbrace>I\<^sub>2\<rbrace> ; (rely (UNIV \<triangleright> I\<^sub>1) \<iinter> guar\<^sub>\<pi> (UNIV \<triangleright> I\<^sub>2) \<iinter> rely r)"
      by (simp add: pgm_guar_strengthen r2_le_r1 seq_conj.sync_mono_left seq_conj.sync_mono_right seq_par.seq_mono_right)
    finally show ?thesis .
  qed

  have expand_rely: "\<lbrace>I\<^sub>2\<rbrace> ; (rely (UNIV \<triangleright> I\<^sub>1) \<iinter> guar\<^sub>\<pi> (UNIV \<triangleright> I\<^sub>2) \<iinter> rely r) \<ge> \<lbrace>I\<^sub>2\<rbrace> ; rely (UNIV \<triangleright> I\<^sub>2) \<iinter> guar\<^sub>\<pi> (UNIV \<triangleright> I\<^sub>2)"
  proof-
    have "\<lbrace>I\<^sub>2\<rbrace> ; (rely (UNIV \<triangleright> I\<^sub>1) \<iinter> guar\<^sub>\<pi> (UNIV \<triangleright> I\<^sub>2) \<iinter> rely r) = \<lbrace>I\<^sub>2\<rbrace> ;  (rely r \<iinter> guar\<^sub>\<pi> (UNIV \<triangleright> I\<^sub>2) \<iinter> rely (UNIV \<triangleright> I\<^sub>1))"
      using local.conj.commute seq_conj.sync_assoc by auto
    also have "\<dots> = \<lbrace>I\<^sub>2\<rbrace> ; (rely r \<iinter> rely (UNIV \<triangleright> I\<^sub>1) \<iinter> guar\<^sub>\<pi> (UNIV \<triangleright> I\<^sub>2))"
      using local.conj.commute seq_conj.sync_assoc by auto
    also have "\<dots> = \<lbrace>I\<^sub>2\<rbrace> ; (rely (r \<triangleright> I\<^sub>1) \<iinter> guar\<^sub>\<pi> (UNIV \<triangleright> I\<^sub>2))"
      by (simp add: rely_absorb)
    also have "\<dots> =  (\<lbrace>I\<^sub>2\<rbrace> ; rely (r \<triangleright> I\<^sub>1) \<iinter> guar\<^sub>\<pi> (UNIV \<triangleright> I\<^sub>2))"
      by (simp add: seq_conj.assert_op_sync_left)
    also have "\<dots> =  (\<lbrace>I\<^sub>2\<rbrace> ; rely (I\<^sub>2 \<triangleleft> (r \<triangleright> I\<^sub>1)) \<iinter> guar\<^sub>\<pi> (UNIV \<triangleright> I\<^sub>2))"
      by (simp add: assert_rely_guar_contrain_rely_domain stable_p2_r stable_p2_range_restrict)
    also have "... \<ge> (\<lbrace>I\<^sub>2\<rbrace> ; rely (UNIV \<triangleright> I\<^sub>2) \<iinter> guar\<^sub>\<pi> (UNIV \<triangleright> I\<^sub>2))"
      by (simp add: assms(2) rely_weaken seq_conj.sync_mono_left seq_par.seq_mono_right)
    finally show ?thesis .
  qed

  have "\<lbrace>I\<^sub>2\<rbrace> ; rely (UNIV \<triangleright> I\<^sub>2) \<iinter> guar\<^sub>\<pi> (UNIV \<triangleright> I\<^sub>2) = inv I\<^sub>2"
    by (simp add: evolve_def local.inv_def seq_conj.assert_op_sync_left)
  then show ?thesis 
    using expand_rely restrict_guar by auto
qed

lemma inv_strengthen_alt:
  assumes "I\<^sub>1 \<supseteq> I\<^sub>2"
  shows "\<lbrace>I\<^sub>2\<rbrace> ; (inv I\<^sub>1 \<iinter> rely (UNIV \<triangleright> I\<^sub>2)) \<ge> inv I\<^sub>2"
proof -
  have "I\<^sub>2 \<triangleleft> ((UNIV \<triangleright> I\<^sub>2) \<triangleright> I\<^sub>1) \<subseteq> (UNIV \<triangleright> I\<^sub>2)"
    using domain_range_restrict_remove restrict_domain_range_assoc by blast
  then show ?thesis
    by (simp add: assms inv_strengthen) 
qed

lemma inv_pgm: "inv I \<iinter> \<pi> r = \<lbrace>I\<rbrace> ; \<pi>(r \<triangleright> I)" 
proof - 
  have "inv I \<iinter> \<pi> r = \<lbrace>I\<rbrace> ; (evolve (UNIV \<triangleright> I) \<iinter> \<pi> r)"
    by (simp add: local.inv_def seq_conj.assert_op_sync_left) 
  also have "\<dots> = \<lbrace>I\<rbrace> ; \<pi>(UNIV \<triangleright> I \<inter> r)" 
    by (simp only: evolve_conj_pgm)   
  also have "\<dots> = \<lbrace>I\<rbrace> ; \<pi>(r \<triangleright> I)" 
    by (simp add: inf_commute restrict_range_def)
  finally show ?thesis .
qed

lemma inv_pgm_alt: "inv I \<iinter> \<pi> r = inv I \<iinter> \<pi>(I \<triangleleft> r \<triangleright> I)" 
proof -
  have "inv I \<iinter> \<pi> r = \<lbrace>I\<rbrace> ; \<tau> I ; \<pi>(r \<triangleright> I)" 
    using inv_pgm by (simp add: seq.assert_op_test) 
  also have "\<dots> = \<lbrace>I\<rbrace> ; \<pi>(I \<triangleleft> r \<triangleright> I)" 
    by (metis pgm_test_pre restrict_domain_range_assoc seq_par.seq_assoc)
  also have "\<dots> = \<lbrace>I\<rbrace> ; \<pi>((I \<triangleleft> r \<triangleright> I) \<triangleright> I)"
    by (metis (no_types, lifting) inv_pgm local.conj.conj_idem seq_conj.assert_op_sync_left
        seq_conj.assert_op_sync_right seq_conj.sync_assoc)
  also have "\<dots> = inv I \<iinter> \<pi>(I \<triangleleft> r \<triangleright> I)"
    by (simp only: inv_pgm)
  finally show ?thesis .
qed

lemma inv_env: "inv I \<iinter> \<epsilon> r = \<lbrace>I\<rbrace> ; (\<epsilon> r \<squnion> \<epsilon>(r \<triangleright> (-I)) ; \<top>)" 
proof - 
  have range_restriction_complement: "\<And>r I. -range_restriction I = range_restriction (-I)"
    by auto
  have restrict_range_complement: "\<And>r I. -(r \<triangleright> I) = (-r) \<union> range_restriction (-I)"
    by (simp only: range_restriction_complement restrict_range_def compl_inf)
  have univ_restrict_range_complement: "-(UNIV \<triangleright> I) = UNIV \<triangleright> (-I)"
  proof-
    have "-(UNIV \<triangleright> I) = (-UNIV) \<union> range_restriction(-I)"
      by (rule restrict_range_complement)
    also have "\<dots> = UNIV \<triangleright> (-I)"
      by (simp add: restrict_range_def)
    finally show ?thesis .
  qed 

  have "inv I \<iinter> \<epsilon> r = \<lbrace>I\<rbrace> ; (evolve (UNIV \<triangleright> I) \<iinter> \<epsilon> r)"
    by (simp add: local.inv_def seq_conj.assert_op_sync_left) 
  also have "\<dots> = \<lbrace>I\<rbrace> ; (\<epsilon> r \<squnion> \<epsilon>(-(UNIV \<triangleright> I) \<inter> r); \<top>)" 
    by (simp only: evolve_conj_env)
  also have "\<dots> = \<lbrace>I\<rbrace> ; (\<epsilon> r \<squnion> \<epsilon>(UNIV \<triangleright> (-I) \<inter> r); \<top>)" 
    by (simp only: univ_restrict_range_complement)
  also have "\<dots> = \<lbrace>I\<rbrace> ; (\<epsilon> r \<squnion> \<epsilon>(r \<triangleright> (-I)); \<top>)" 
    by (simp add: inf_commute restrict_range_def)
  finally show ?thesis .
qed

lemma inv_env_alt: "inv I \<iinter> \<epsilon> r = inv I \<iinter> \<epsilon>(I \<triangleleft> r)"
  by (metis env_test_pre inv_distrib_seq inv_conj_extract_assert seq.assert_op_test_idem)

lemma inv_test_rel: "inv I \<iinter> \<tau>{\<sigma>. (\<sigma>,\<sigma>) \<in> q} = inv I \<iinter> \<tau>{\<sigma>. (\<sigma>,\<sigma>) \<in> I \<triangleleft> q \<triangleright> I}" 
proof -
  have z0: "\<And>r. {\<sigma>. \<sigma> \<in> I \<and> (\<sigma>,\<sigma>) \<in> r} = I \<inter> {\<sigma>. (\<sigma>,\<sigma>) \<in> r}" 
    by blast
  have "inv I \<iinter> \<tau>{\<sigma>. (\<sigma>,\<sigma>) \<in> q} = \<lbrace>I\<rbrace> ; \<tau>(I \<inter> {\<sigma>. (\<sigma>,\<sigma>) \<in> q})" 
    using inv_test_alt by blast
  also have "\<dots> = \<lbrace>I\<rbrace> ; \<tau>{\<sigma>. \<sigma> \<in> I \<and> (\<sigma>,\<sigma>) \<in> q}" 
    by (simp add: Collect_conj_eq) 
  also have "\<dots> = \<lbrace>I\<rbrace> ; \<tau>{\<sigma>. \<sigma> \<in> I \<and> (\<sigma>,\<sigma>) \<in> domain_restriction I \<inter> q \<inter> range_restriction I}" 
    by (simp add: Collect_conj_eq inf_sup_aci(1)) 
  also have "\<dots> = \<lbrace>I\<rbrace> ; \<tau>{\<sigma>. \<sigma> \<in> I \<and> (\<sigma>,\<sigma>) \<in> I \<triangleleft> q \<triangleright> I}" 
    by (simp add: restrict_domain_def restrict_range_def) 
  also have "\<dots> = \<lbrace>I\<rbrace> ; \<tau>(I \<inter> {\<sigma>. (\<sigma>,\<sigma>) \<in> I \<triangleleft> q \<triangleright> I})" 
    using z0 by simp 
  also have "\<dots> = inv I \<iinter> \<tau>{\<sigma>. (\<sigma>,\<sigma>) \<in> I \<triangleleft> q \<triangleright> I}" 
    using inv_test_alt by presburger
  finally show ?thesis .
qed

lemma inv_opt_equiv: "inv I \<iinter> opt q = inv I \<iinter> opt(I \<triangleleft> q \<triangleright> I)"
proof -
  have "inv I \<iinter> opt q = inv I \<iinter> \<pi> q \<squnion> inv I \<iinter> \<tau>{\<sigma>. (\<sigma>,\<sigma>) \<in> q}" 
    by (simp add: opt_def seq_conj.sync_sup) 
  also have "\<dots> = inv I \<iinter> \<pi>(I \<triangleleft> q \<triangleright> I) \<squnion> inv I \<iinter> \<tau>{\<sigma>. (\<sigma>,\<sigma>) \<in> q}" 
    using inv_pgm_alt by force 
  also have "\<dots> = inv I \<iinter> \<pi>(I \<triangleleft> q \<triangleright> I) \<squnion> inv I \<iinter> \<tau>{\<sigma>. (\<sigma>,\<sigma>) \<in> I \<triangleleft> q \<triangleright> I}" 
    using inv_test_rel by presburger
  also have "\<dots> = inv I \<iinter> opt(I \<triangleleft> q \<triangleright> I)" 
    by (simp add: opt_def seq_conj.sync_sup) 
  finally show ?thesis .
qed

end

context frame_state
begin


text\<open>Can assume the invariant holds before and after every step of the atomic specification.\<close>
lemma inv_atomic_spec_equiv: "inv I \<iinter> \<langle>p, q\<rangle> = inv I \<iinter> \<langle>I \<inter> p, I \<triangleleft> q \<triangleright> I\<rangle>"
proof -
  have "inv I \<iinter> \<langle>p,q\<rangle> =
      (inv I \<iinter> idle) ; (inv I \<iinter> \<lbrace>p\<rbrace>) ;
      (inv I \<iinter> opt q) ; (inv I \<iinter> idle)"
    by (simp add: atomic_spec_def inv_distrib_seq)
  also have "\<dots> =
      (inv I \<iinter> idle) ; (inv I \<iinter> \<lbrace>I \<inter> p\<rbrace>) ;
      (inv I \<iinter> opt(I \<triangleleft> q \<triangleright> I)) ; (inv I \<iinter> idle)"
    using inv_assert inv_opt_equiv by auto
  also have "\<dots> = inv I \<iinter> \<langle>I \<inter> p,I \<triangleleft> q \<triangleright> I\<rangle>"
    by (simp add: atomic_spec_def inv_distrib_seq)
  finally show ?thesis .
qed

lemma inv_atomic_pre: "inv I \<iinter> \<langle>p, q\<rangle> = inv I \<iinter> \<langle>I \<inter> p, q\<rangle>"
proof-
  have "inv I \<iinter> \<langle>p, q\<rangle> = inv I \<iinter> (idle ; (inv I \<iinter> \<lbrace>p\<rbrace>) ; opt q ; idle)"
    by (simp add: atomic_spec_def inv_distrib_seq)
  then show ?thesis
    by (simp add: atomic_spec_def inv_assert) 
qed

lemma inv_atomic_post: "inv I \<iinter> \<langle>p, q\<rangle> = inv I \<iinter> \<langle>p, I \<triangleleft> q \<triangleright> I\<rangle>"
  using inv_atomic_spec_equiv inv_atomic_pre by simp

lemma inv_rely_atomic_spec_equiv: "inv I \<iinter> rely r \<iinter> \<langle>p,q\<rangle> = inv I \<iinter> rely r \<iinter> \<langle>I \<inter> p,I \<triangleleft> q \<triangleright> I\<rangle>"
  using inv_atomic_spec_equiv local.conj.left_commute seq_conj.sync_assoc by auto

lemma inv_rely_atomic_spec_seq_equiv:
  "inv I \<iinter> rely r \<iinter> (\<langle>p,q\<rangle> ; c) =
    inv I \<iinter> rely r \<iinter> (\<langle>I \<inter> p,I \<triangleleft> q \<triangleright> I\<rangle> ; c)"
  using inv_atomic_spec_equiv inv_distrib_seq local.conj.left_commute seq_conj.sync_assoc by fastforce

lemma inv_rely_assert_atomic_spec_into_pre:
  assumes stable_q': "stable q' (I \<triangleleft> r \<triangleright> I)"
  shows "inv I \<iinter> rely r \<iinter> (\<lbrace>q'\<rbrace> ; \<langle>p,q\<rangle>) = inv I \<iinter> rely r \<iinter> (\<lbrace>q'\<rbrace> ; \<langle>q' \<inter> p,q\<rangle>)"
  by (rule inv_rely_restrict_cong
      [OF assert_atomic_spec_into_pre[OF stable_q']])

text \<open>Under an invariant, an atomic specification may establish an
assertion using the invariant-restricted atomic relation and rely.\<close>
lemma atomic_spec_extract_post_assert_under_invariant:
  assumes q_establishes_q'_under_I: "(I \<inter> p) \<triangleleft> q \<triangleright> I \<subseteq> UNIV \<triangleright> q'"
  assumes stable_q': "stable q' (I \<triangleleft> r \<triangleright> I)"
  shows "inv I \<iinter> rely r \<iinter> \<langle>p,q\<rangle> = inv I \<iinter> rely r \<iinter> (\<langle>p,q\<rangle> ; \<lbrace>q'\<rbrace>)"
proof -
  let ?p = "I \<inter> p"
  let ?q = "I \<triangleleft> q \<triangleright> I"
  let ?r = "I \<triangleleft> r \<triangleright> I"
  have establish_q': "?p \<triangleleft> ?q \<subseteq> UNIV \<triangleright> q'"
  proof -
    have "?p \<triangleleft> ?q = (I \<inter> p) \<triangleleft> q \<triangleright> I"
      unfolding restrict_domain_def restrict_range_def by blast
    then show ?thesis
      using q_establishes_q'_under_I by simp
  qed
  have extract_q': "rely ?r \<iinter> \<langle>?p,?q\<rangle> = rely ?r \<iinter> (\<langle>?p,?q\<rangle> ; \<lbrace>q'\<rbrace>)"
    by (rule atomic_spec_extract_post_assert[OF establish_q' stable_q'])
  have extracted:
    "inv I \<iinter> rely r \<iinter> \<langle>?p,?q\<rangle> = inv I \<iinter> rely r \<iinter> (\<langle>?p,?q\<rangle> ; \<lbrace>q'\<rbrace>)"
    by (rule inv_rely_restrict_cong[OF extract_q'])
  have "inv I \<iinter> rely r \<iinter> \<langle>p,q\<rangle> = inv I \<iinter> rely r \<iinter> \<langle>?p,?q\<rangle>"
    by (rule inv_rely_atomic_spec_equiv)
  also have "\<dots> = inv I \<iinter> rely r \<iinter> (\<langle>p,q\<rangle> ; \<lbrace>q'\<rbrace>)"
    using extracted inv_rely_atomic_spec_seq_equiv by auto
  finally show ?thesis .
qed

lemma atomic_spec_extract_post_assert_under_inv_rely_guar_ctx:
  assumes refl_g: "refl g"
  assumes q_establishes_q'_under_ctx: "(I \<inter> p \<inter> p0) \<triangleleft> (q \<inter> g) \<triangleright> I \<subseteq> UNIV \<triangleright> q'"
  assumes stable_q': "stable q' (I \<triangleleft> r \<triangleright> I)"
  assumes stable_p0: "stable p0 (I \<triangleleft> r \<triangleright> I)"
  shows "inv I \<iinter> rely r \<iinter> guar\<^sub>\<pi> g \<iinter> \<lbrace>p0\<rbrace> ; \<langle>p,q\<rangle> = inv I \<iinter> rely r \<iinter> guar\<^sub>\<pi> g \<iinter> \<lbrace>p0\<rbrace> ; \<langle>p,q\<rangle> ; \<lbrace>q'\<rbrace>"
proof -
  have guar_normal: "guar\<^sub>\<pi> g \<iinter> (\<lbrace>p0\<rbrace> ; \<langle>p,q\<rangle>) = \<lbrace>p0\<rbrace> ; \<langle>p,g \<inter> q\<rangle>"
    by (simp add: atomic_guar refl_g seq_conj.assert_op_sync_right)
  have guar_post_normal: "guar\<^sub>\<pi> g \<iinter> (\<lbrace>p0\<rbrace> ; \<langle>p,q\<rangle> ; \<lbrace>q'\<rbrace>) = \<lbrace>p0\<rbrace> ; \<langle>p,g \<inter> q\<rangle> ; \<lbrace>q'\<rbrace>"
    by (metis guar_normal local.conj.commute pgm_guar_conj_assert pgm_guar_conj_seq)
  have establish_q': "(I \<inter> (p0 \<inter> p)) \<triangleleft> (g \<inter> q) \<triangleright> I \<subseteq> UNIV \<triangleright> q'"
    using q_establishes_q'_under_ctx
    by (simp add: Int_assoc Int_left_commute Int_commute)
  have extract_q':
    "inv I \<iinter> rely r \<iinter> \<langle>p0 \<inter> p,g \<inter> q\<rangle> =  inv I \<iinter> rely r \<iinter> (\<langle>p0 \<inter> p,g \<inter> q\<rangle> ; \<lbrace>q'\<rbrace>)"
    by (rule atomic_spec_extract_post_assert_under_invariant[OF establish_q' stable_q'])
  have into_pre:
    "inv I \<iinter> rely r \<iinter> (\<lbrace>p0\<rbrace> ; \<langle>p,g \<inter> q\<rangle>) = inv I \<iinter> rely r \<iinter> (\<lbrace>p0\<rbrace> ; \<langle>p0 \<inter> p,g \<inter> q\<rangle>)"
    by (rule inv_rely_assert_atomic_spec_into_pre[OF stable_p0])
  have into_pre_post:
    "inv I \<iinter> rely r \<iinter> (\<lbrace>p0\<rbrace> ; \<langle>p,g \<inter> q\<rangle> ; \<lbrace>q'\<rbrace>) = inv I \<iinter> rely r \<iinter> (\<lbrace>p0\<rbrace> ; \<langle>p0 \<inter> p,g \<inter> q\<rangle> ; \<lbrace>q'\<rbrace>)"
    by (rule inv_rely_restrict_cong
        [OF equal_within_rely_left[OF assert_atomic_spec_into_pre[OF stable_p0]]])
  have absorb_pre: "\<lbrace>p0\<rbrace> ; \<langle>p0 \<inter> p,g \<inter> q\<rangle> = \<langle>p0 \<inter> p,g \<inter> q\<rangle>"
    by (metis atomic_extract_pre_left seq.assert_inter_to_assert_left seq.assert_to_eq seq_par.seq_mono_left)
  have "inv I \<iinter> rely r \<iinter> guar\<^sub>\<pi> g \<iinter> \<lbrace>p0\<rbrace> ; \<langle>p,q\<rangle> = inv I \<iinter> rely r \<iinter> (\<lbrace>p0\<rbrace> ; \<langle>p,g \<inter> q\<rangle>)"
    using guar_normal by (simp add: seq_conj.sync_assoc)
  also have "\<dots> = inv I \<iinter> rely r \<iinter> (\<lbrace>p0\<rbrace> ; \<langle>p,g \<inter> q\<rangle> ; \<lbrace>q'\<rbrace>)"
    by (simp add: absorb_pre extract_q' into_pre into_pre_post)
  also have "\<dots> = inv I \<iinter> rely r \<iinter> guar\<^sub>\<pi> g \<iinter> \<lbrace>p0\<rbrace> ; \<langle>p,q\<rangle> ; \<lbrace>q'\<rbrace>"
    using guar_post_normal by (simp add: seq_conj.sync_assoc)
  finally show ?thesis .
qed

lemma framed_atomic_spec_extract_post_assert_under_invariant:
  assumes q_establishes_q'_under_I: "(I \<inter> p) \<triangleleft> q \<triangleright> I \<subseteq> UNIV \<triangleright> q'"
  assumes stable_q': "stable q' (I \<triangleleft> r \<triangleright> I)"
  shows "inv I \<iinter> rely r \<iinter> vars:\<^sub>s\<langle>p,q\<rangle> = inv I \<iinter> rely r \<iinter> (vars:\<^sub>s\<langle>p,q\<rangle> ; \<lbrace>q'\<rbrace>)"
proof -
  have frame_atomic: "vars:\<^sub>s\<langle>p,q\<rangle> = \<langle>p, id_bar vars \<inter> q\<rangle>"
    by (rule atomic_frame)
  have establish_q':
    "(I \<inter> p) \<triangleleft> (id_bar vars \<inter> q) \<triangleright> I \<subseteq> UNIV \<triangleright> q'"
  proof -
    have "(I \<inter> p) \<triangleleft> (id_bar vars \<inter> q) \<triangleright> I \<subseteq> (I \<inter> p) \<triangleleft> q \<triangleright> I"
      unfolding restrict_domain_def restrict_range_def by blast
    then show ?thesis
      using q_establishes_q'_under_I by blast
  qed
  have extract_q':
    "inv I \<iinter> rely r \<iinter> \<langle>p, id_bar vars \<inter> q\<rangle> = inv I \<iinter> rely r \<iinter> (\<langle>p, id_bar vars \<inter> q\<rangle> ; \<lbrace>q'\<rbrace>)"
    by (rule atomic_spec_extract_post_assert_under_invariant
        [OF establish_q' stable_q'])
  have "inv I \<iinter> rely r \<iinter> vars:\<^sub>s\<langle>p,q\<rangle> = inv I \<iinter> rely r \<iinter> \<langle>p, id_bar vars \<inter> q\<rangle>"
    using frame_atomic by simp
  also have "\<dots> = inv I \<iinter> rely r \<iinter>(\<langle>p, id_bar vars \<inter> q\<rangle> ; \<lbrace>q'\<rbrace>)"
    by (rule extract_q')
  also have "\<dots> = inv I \<iinter> rely r \<iinter> (vars:\<^sub>s\<langle>p,q\<rangle> ; \<lbrace>q'\<rbrace>)"
    using frame_atomic by simp
  finally show ?thesis .
qed

lemma inv_spec_equiv: "inv I \<iinter> \<lparr>q\<rparr> = inv I \<iinter> \<lparr>I \<triangleleft> q \<triangleright> I\<rparr>"
proof -
  have "inv I \<iinter> \<lparr>q\<rparr> = inv I \<iinter> \<lbrace>I\<rbrace> ; \<lparr>q\<rparr>"
    by (rule inv_conj_extract_assert)
  also have "\<dots> = inv I \<iinter> \<lbrace>I\<rbrace> ; \<lparr>I \<triangleleft> q\<rparr>"
    using assert_restricts_spec by auto
  also have "\<dots> = inv I \<iinter> \<lparr>I \<triangleleft> q\<rparr>"
    using inv_conj_extract_assert by auto
  also have "\<dots> = inv I \<iinter> (\<lparr>I \<triangleleft> q\<rparr> ; \<tau> I)"
    using inv_conj_right_assert inv_distrib_seq inv_test seq.assert_op_test_idem by auto
  also have "\<dots> = inv I \<iinter> \<lparr>I \<triangleleft> q \<triangleright> I\<rparr>"
    by (simp only: spec_test_restricts)
  finally show ?thesis .
qed

lemma inv_full_spec_equiv: "inv I \<iinter> \<lbrace>p\<rbrace> ; \<lparr>q\<rparr> = inv I \<iinter> \<lbrace>I \<inter> p\<rbrace> ; \<lparr>I \<triangleleft> q \<triangleright> I\<rparr>"
proof -
  have "inv I \<iinter> \<lbrace>p\<rbrace> ; \<lparr>q\<rparr> = (inv I \<iinter> \<lbrace>p\<rbrace>) ; (inv I \<iinter> \<lparr>q\<rparr>)"
    by (simp add: inv_distrib_seq)
  also have "\<dots> = (inv I \<iinter> \<lbrace>I \<inter> p\<rbrace>) ; (inv I \<iinter> \<lparr>I \<triangleleft> q \<triangleright> I\<rparr>)"
    using inv_assert inv_spec_equiv by force
  finally show ?thesis
    by (simp add: inv_distrib_seq)
qed
end

(* The strong invariant is equivalent to the evolve invariant weak conjoined to an 
environment guarantee.
lemma strong_inv_eq_inv_conj_envguar: "Generalised_Invariants.inv(p) = inv(p) \<iinter> guar\<^sub>\<epsilon> (UNIV \<triangleright> p)"
proof -
oops *)
end
