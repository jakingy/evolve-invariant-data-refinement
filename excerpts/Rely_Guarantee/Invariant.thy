(* Extracts from isabelle/new_rg_algebra/Rely_Guarantee/Invariant.thy. *)
(* These are source excerpts, not a standalone buildable theory. *)

(* Original lines 11-12. *)
definition inv :: "'state set \<Rightarrow> 'a" where
  "inv p = \<lbrace>p\<rbrace> ; evolve (UNIV \<triangleright> p)"


(* Original lines 14-25. *)
text \<open>An assertion can be added before an invariant.\<close>
lemma inv_extract_assert: "inv p  = \<lbrace>p\<rbrace> ; inv p"
proof -
  have "\<lbrace>p\<rbrace> ; inv p = \<lbrace>p\<rbrace> ; \<lbrace>p\<rbrace> ; evolve (UNIV \<triangleright> p)"
    by (simp only: inv_def seq.assoc)
  also have "\<dots> = \<lbrace>p\<rbrace> ; evolve (UNIV \<triangleright> p)"
    by (simp add: seq.assert_op_assert_idem)
  also have "\<dots> = inv p"
    by (simp only: inv_def)
  finally show ?thesis
    by simp
qed


(* Original lines 27-33. *)
lemma inv_conj_extract_assert: "inv p \<iinter> c = inv p \<iinter> \<lbrace>p\<rbrace> ; c"
proof-
  have "inv p \<iinter> c = \<lbrace>p\<rbrace> ; inv p \<iinter> c"
    using inv_extract_assert by auto
  then show ?thesis
    by (simp add: seq_conj.assert_op_sync_left seq_conj.assert_op_sync_right)
qed


(* Original lines 35-45. *)
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


(* Original lines 47-57. *)
text \<open>The following lemmas describe the interaction between invariants and primitive commands.\<close>
lemma inv_test: "inv p \<iinter> \<tau> p1 = \<lbrace>p\<rbrace> ; \<tau> p1" 
proof -
  have "inv p \<iinter> \<tau> p1 = \<lbrace>p\<rbrace> ; evolve (UNIV \<triangleright> p) \<iinter> \<tau> p1" 
    by (simp only: inv_def)
  also have "\<dots> = \<lbrace>p\<rbrace> ; (evolve (UNIV \<triangleright> p) \<iinter> \<tau> p1)"
    by (simp only: seq_conj.assert_op_sync_right local.conj.commute)
  also have "\<dots> = \<lbrace>p\<rbrace> ; \<tau> p1"  
    by (simp only: evolve_test) 
  finally show ?thesis .
qed


(* Original lines 59-61. *)
lemma inv_test_alt: "inv p \<iinter> \<tau> p1 = \<lbrace>p\<rbrace> ; \<tau>(p \<inter> p1)"
  using inv_test seq.assert_op seq.assert_op_alt seq.test_inf seq.test_seq_test 
  by (metis seq.image_is_test)


(* Original lines 63-66. *)
text \<open>As a corollary to \<open>inv_test\<close>, we have that the invariant weak conjoined with nil is
just the corresponding assertion.\<close>
lemma inv_conj_nil: "inv p \<iinter> nil = \<lbrace>p\<rbrace>"
  using inv_test local.seq.seq_nil seq.test_set_top by auto


(* Original lines 68-82. *)
text \<open>The precondition of an invariant is just its corresponding assertion.\<close>
lemma inv_pre: "seq.pre(inv p) = \<lbrace>p\<rbrace>" 
proof -
  have "seq.pre(inv p) = seq.pre(\<lbrace>p\<rbrace> ; evolve (UNIV \<triangleright> p))" 
    using inv_def by simp 
  also have "\<dots> = seq.pre(\<lbrace>p\<rbrace> ; seq.pre(evolve(UNIV \<triangleright> p)))"
    using seq_par.pre_of_seq[where ?c1.0 = "\<lbrace>p\<rbrace>" and ?c2.0 = "evolve(UNIV \<triangleright> p)"] by simp
  also have "\<dots> = seq.pre(\<lbrace>p\<rbrace> ; nil)" 
    by (simp only: evolve_pre)
  also have "\<dots> = seq.pre(\<lbrace>p\<rbrace>)"
    by (simp only: seq.seq_nil)
  also have "\<dots> = \<lbrace>p\<rbrace>"  
    by (simp only: seq_conj.pre_assert)
  finally show ?thesis .
qed


(* Original lines 84-91. *)
text\<open>Alternate invariant definitions.\<close>
lemma inv_alt_def2: "inv p = \<lbrace>p\<rbrace> ; evolve (p \<triangleleft> (UNIV \<triangleright> p))"
proof -
  have "stable p (UNIV \<triangleright> p)"
    by (auto simp: restrict_range_def)
  then show ?thesis
    by (simp add: assert_stable_evolve_alt local.inv_def)   
qed


(* Original lines 93-99. *)
lemma inv_alt_def3: "inv p = \<lbrace>p\<rbrace> ; evolve (-(p \<triangleleft> UNIV) \<union> (UNIV \<triangleright> p))"
proof -
   have "stable p (UNIV \<triangleright> p)"
    by (auto simp: restrict_range_def)
  then show ?thesis
    by (simp add: assert_stable_evolve_alt2 local.inv_def)  
qed


(* Original lines 102-103. *)
definition inv_weak_atomic :: "'state set \<Rightarrow> 'a" where
  "inv_weak_atomic p = \<lbrace>p\<rbrace> ; evolve_pseudo_atomic (UNIV \<triangleright> p)"


(* Original lines 105-116. *)
text\<open>An invariant is a weak atomic iterated.\<close>
lemma inv_atomic_iter_def: "inv p = (inv_weak_atomic p)\<^sup>\<omega>"
proof -
  have "inv p = \<lbrace>p\<rbrace> ; (evolve_pseudo_atomic (UNIV \<triangleright> p))\<^sup>\<omega>"
    by (simp only: inv_def evolve_atomic_iter_def)
  also have "\<dots> = (\<lbrace>p\<rbrace> ; evolve_pseudo_atomic (UNIV \<triangleright> p))\<^sup>\<omega>"
    using evolve_pseudo_atomic_range_restricted_stable
    by (rule stable_iter_maintain_assert)
  also have "\<dots> = (inv_weak_atomic p)\<^sup>\<omega>"
    by (simp only: inv_weak_atomic_def)
  finally show ?thesis .
qed


(* Original lines 119-137. *)
text \<open>The following lemmas describe how invariants distribute over
non-deterministic choice, sequential composition and parallel composition
and into fixed, finite, possibly infinite and infinite iterations.
Distribution over weak conjunction is trivial, so a lemma is not needed.\<close>

text \<open>The invariant is established after the invariant command.\<close>
lemma inv_establish: "inv p ; \<lbrace>p\<rbrace> = inv p"
proof -
  have finite_iter: "inv p = ((inv_weak_atomic p)\<^sup>\<omega>)*"
    by (simp add: inv_atomic_iter_def seq.iter_finite_iter)

  have "inv p ; \<lbrace>p\<rbrace> =  inv p ; seq.pre(inv p)"
    by (simp add: inv_pre)
  also have "\<dots> = ((inv_weak_atomic p)\<^sup>\<omega>)* ; seq.pre((inv_weak_atomic p)\<^sup>\<omega>)"
    by (simp add: inv_atomic_iter_def seq.iter_finite_iter)
  also have "\<dots> = inv p"
    by (simp add: finite_iter seq.finite_iter_seq_pre)
  finally show ?thesis .
qed


(* Original lines 139-141. *)
text \<open>An invariant of \<open>p\<close> establishes a test of \<open>p\<close>.\<close>
lemma inv_establish_test: "inv p = inv p ; \<tau> p" 
  by (metis inv_establish inv_pre seq.guard_test seq.pre_seq_guard seq_par.seq_assoc)


(* Original lines 143-146. *)
text\<open>An invariant is stable under its condition.\<close>
lemma inv_stable: "seq.test_stable p (inv p)"
  using inv_establish_test inv_extract_assert seq.test_assert_galois seq.test_stable_def
  by auto


(* Original lines 148-149. *)
lemma inv_conj_stable: "seq.test_stable p (inv p \<iinter> c)"  
  by (simp add: inv_stable seq_conj.stable_conj_stable)


(* Original lines 151-162. *)
text\<open>A command weak conjoined with an invariant will satisfy p after.\<close>
lemma inv_conj_right_assert: "inv p \<iinter> c = (inv p \<iinter> c) ; \<lbrace>p\<rbrace>"
proof-
  have "inv p \<iinter> c = \<lbrace>p\<rbrace> ; inv p \<iinter> c"
    using inv_extract_assert by auto
  also have "\<dots> = \<lbrace>p\<rbrace> ; (inv p \<iinter> c)"
    by (simp add: seq_conj.assert_op_sync_left)
  also have "\<dots> = \<lbrace>p\<rbrace> ; (inv p \<iinter> c) ; \<lbrace>p\<rbrace>"
    using seq_par.assert_stable_assert inv_conj_stable by auto
  finally show ?thesis
    using \<open>\<lbrace>p\<rbrace> ; local.inv p \<iinter> c = \<lbrace>p\<rbrace> ; (local.inv p \<iinter> c)\<close> \<open>local.inv p \<iinter> c = \<lbrace>p\<rbrace> ; local.inv p \<iinter> c\<close> by argo
qed


(* Original lines 164-167. *)
text\<open>Distribution laws\<close>
lemma inv_distrib_Sup: "inv p \<iinter> \<Squnion>C = \<lbrace>p\<rbrace> ; (\<Squnion>c \<in> C. inv p \<iinter> c)" 
 by (metis SUP_empty Sup_empty conj.op_Sup_nonempty inv_extract_assert inv_test seq.test_Union
      seq_conj.assert_op_sync_left)


(* Original lines 169-182. *)
lemma inv_distrib_seq: "inv p \<iinter> (c1 ; c2) = (inv p \<iinter> c1) ; (inv p \<iinter> c2)"  
proof -
  have evolve: "inv p \<iinter> (c1 ; c2) = \<lbrace>p\<rbrace> ; evolve (UNIV \<triangleright> p) \<iinter> (c1 ; c2)" 
    by (simp add: local.inv_def inv_extract_assert)
  also have "\<dots> = \<lbrace>p\<rbrace> ; (evolve (UNIV \<triangleright> p) \<iinter> (c1;c2))"
    by (simp only: conj.commute seq_conj.assert_op_sync_right)
  also have "\<dots> = (inv p \<iinter> c1) ; (evolve (UNIV \<triangleright> p) \<iinter> c2)"
    by (simp add: evolve_distrib_seq local.inv_def seq_conj.assert_op_sync_left seq_par.seq_assoc)
  also have "\<dots> = (inv p \<iinter> c1) ; \<lbrace>p\<rbrace> ; (evolve (UNIV \<triangleright> p) \<iinter> c2)"
    using inv_conj_right_assert by auto
  also have "\<dots> = (inv p \<iinter> c1) ; (inv p \<iinter> c2)"
    by (simp add: inv_def seq.assoc seq_conj.assert_op_sync_left)
  finally show ?thesis .
qed


(* Original lines 184-195. *)
lemma inv_distrib_par: "inv p \<iinter> (c1 \<parallel> c2) = (inv p \<iinter> c1) \<parallel> (inv p \<iinter> c2)"
proof -
  have "inv p \<iinter> (c1 \<parallel> c2) = \<lbrace>p\<rbrace> ; (evolve (UNIV \<triangleright> p) \<iinter> (c1 \<parallel> c2))" 
    using inv_def seq_conj.assert_op_sync_left by simp 
  also have "\<dots> = \<lbrace>p\<rbrace> ; (evolve (UNIV \<triangleright> p) \<iinter> c1 \<parallel> evolve (UNIV \<triangleright> p) \<iinter> c2)" 
    by (simp only: evolve_distrib_par)
  also have "\<dots> = (\<lbrace>p\<rbrace> ; evolve (UNIV \<triangleright> p) \<iinter> c1 \<parallel> \<lbrace>p\<rbrace> ; evolve (UNIV \<triangleright> p) \<iinter> c2)" 
    by (simp add: conj.conj_commute seq_conj.assert_op_sync_right seq_par.assert_op_sync') 
  also have "\<dots> = (inv p \<iinter> c1) \<parallel> (inv p \<iinter> c2)" 
    by (simp only: inv_def)
  finally show ?thesis .
qed


(* Original lines 197-198. *)
lemma inv_distrib_power: "inv p \<iinter> c^i = \<lbrace>p\<rbrace> ; (inv p \<iinter> c)^i" 
  using inv_distrib_seq inv_pre seq_conj.distrib_fixed_iter_nil by simp


(* Original lines 200-201. *)
lemma inv_distrib_fiter: "inv p \<iinter> c* = (inv p \<iinter> c)*" 
  using inv_distrib_seq seq_conj.distributive_finite_iter by simp 


(* Original lines 203-219. *)
lemma inv_distrib_iter: "inv p \<iinter> c\<^sup>\<omega> = (inv p \<iinter> c)\<^sup>\<omega>" 
proof -
  have stable_ec: "seq.test_stable p (evolve (UNIV \<triangleright> p) \<iinter> c)"
    using evolve_range_restricted_stable seq_conj.stable_conj_stable
    by auto

  have "inv p \<iinter> c\<^sup>\<omega> = \<lbrace>p\<rbrace> ; evolve (UNIV \<triangleright> p) \<iinter> c\<^sup>\<omega>"
    by (simp only: inv_def)
  also have "\<dots> = \<lbrace>p\<rbrace> ; (evolve (UNIV \<triangleright> p) \<iinter> c)\<^sup>\<omega>"
    by (simp only: evolve_distrib_iter seq_conj.assert_op_sync_left)
  also have "\<dots> = (\<lbrace>p\<rbrace> ; (evolve (UNIV \<triangleright> p) \<iinter> c))\<^sup>\<omega>"
    using stable_ec
    by (rule stable_iter_maintain_assert)
  also have "\<dots> = (inv p \<iinter> c)\<^sup>\<omega>"
    by (simp add: local.inv_def seq_conj.assert_op_sync_left)
  finally show ?thesis .  
qed


(* Original lines 221-222. *)
lemma inv_distrib_infiter: "inv p \<iinter> c\<^sup>\<infinity> = (inv p \<iinter> c)\<^sup>\<infinity>" 
  by (metis inf_as_conj inv_distrib_iter seq_conj.sync_assoc)


(* Original lines 224-235. *)
text \<open>An invariant weak conjoined with an assert is an assertion of the intersection of
conditions for the invariant and assertion.\<close>
lemma inv_assert: "inv p \<iinter> \<lbrace>p1\<rbrace> = \<lbrace>p \<inter> p1\<rbrace>" 
proof -
  have "inv p \<iinter> \<lbrace>p1\<rbrace> = \<lbrace>p1\<rbrace> ; (inv p \<iinter> nil)" 
    by (metis seq.seq_nil seq_conj.assert_op_sync_right)
  also have "\<dots> = \<lbrace>p1\<rbrace> ; \<lbrace>p\<rbrace>" 
    using inv_conj_nil by simp 
  also have "\<dots> = \<lbrace>p \<inter> p1\<rbrace>" 
    by (simp add: inf_commute seq.assert_op_assert seq.assert_op_test)
  finally show ?thesis .
qed


(* Original lines 237-238. *)
lemma inv_extract_rely: "inv p = inv p \<iinter> rely (UNIV \<triangleright> p)"
  using evolve_extract_rely inv_def seq_conj.assert_op_sync_left by auto


(* Original lines 240-241. *)
lemma inv_extract_rely3: "inv p = inv p \<iinter> rely (-(p \<triangleleft> UNIV) \<union> (UNIV \<triangleright> p))"
  using evolve_extract_rely inv_alt_def3 seq_conj.assert_op_sync_left by auto


(* Original lines 243-256. *)
text\<open>Can also extract the invariant's domain and range-restricted rely.\<close>
lemma inv_extract_rely2: "inv p = inv p \<iinter> rely (p \<triangleleft> (UNIV \<triangleright> p))"
proof-
  let ?r = "p \<triangleleft> (UNIV \<triangleright> p)"
  have "inv p = \<lbrace>p\<rbrace> ; (rely ?r \<iinter> guar\<^sub>\<pi> ?r)"
    by (simp add: inv_alt_def2 evolve_def)
  also have "... = \<lbrace>p\<rbrace> ; (rely ?r \<iinter> rely ?r \<iinter> guar\<^sub>\<pi> ?r)"
    by (simp only: conj.idem)
  also have "... = (\<lbrace>p\<rbrace> ; (rely ?r \<iinter> guar\<^sub>\<pi> ?r) \<iinter> rely ?r)"
    using conj.commute seq_conj.assert_op_sync_right seq_conj.sync_assoc by auto
  also have "... = inv p \<iinter> rely ?r"
    by (simp only: inv_alt_def2 evolve_def)
  finally show ?thesis .
qed


(* Original lines 258-271. *)
text \<open>inv_def_alt3 is useful if you need reflexive rely conditions.\<close>
lemma inv_rely_refl:
  "refl (-(p \<triangleleft> UNIV) \<union> (UNIV \<triangleright> p))"
proof (rule reflI)
  fix \<sigma>
  show "(\<sigma>, \<sigma>) \<in> -(p \<triangleleft> UNIV) \<union> (UNIV \<triangleright> p)"
  proof (cases "\<sigma> \<in> p")
    case True
    then show ?thesis  by (simp add: restrict_range_def)
  next
    case False
    then show ?thesis by (simp add: restrict_domain_def)
  qed
qed


(* Original lines 273-277. *)
text \<open>Invariant relation preserves the invariant.\<close>
lemma inv_rely_stable:
  "stable p (-(p \<triangleleft> UNIV) \<union> (UNIV \<triangleright> p))"
  unfolding stable_def restrict_domain_def restrict_range_def
  by blast


(* Original lines 279-280. *)
lemma inv_extract_rely_assert: "inv p \<iinter> c = inv p \<iinter> rely (UNIV \<triangleright> p) \<iinter> \<lbrace>p\<rbrace> ; c"
  using inv_conj_extract_assert inv_extract_rely by auto


(* Original lines 282-283. *)
lemma inv_extract_rely_assert3: "inv p \<iinter> c = inv p \<iinter> rely (-(p \<triangleleft> UNIV) \<union> (UNIV \<triangleright> p)) \<iinter> \<lbrace>p\<rbrace> ; c"
  using inv_conj_extract_assert inv_extract_rely3 by auto


(* Original lines 285-326. *)
text \<open>Unpack invariant in existing rely-guarantee.\<close>
lemma inv_extract_context:
  "inv p \<iinter> (rely r \<iinter> guar\<^sub>\<pi> g \<iinter> c) =
    inv p \<iinter>
      (rely (r \<inter> (-(p \<triangleleft> UNIV) \<union> (UNIV \<triangleright> p))) \<iinter>
        guar\<^sub>\<pi> g \<iinter> (\<lbrace>p\<rbrace> ; c))"
proof -
  let ?R = "-(p \<triangleleft> UNIV) \<union> (UNIV \<triangleright> p)"
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
    "inv p \<iinter> (rely r \<iinter> guar\<^sub>\<pi> g \<iinter> c) = \<lbrace>p\<rbrace> ; (rely ?R \<iinter> guar\<^sub>\<pi> ?R \<iinter> rely r \<iinter> guar\<^sub>\<pi> g \<iinter> c)"
    by (simp add: evolve_def inv_alt_def3 seq_conj.assert_op_sync_left seq_conj.sync_assoc)
  have rhs_normal:
    "inv p \<iinter> (rely (r \<inter> ?R) \<iinter> guar\<^sub>\<pi> g \<iinter> (\<lbrace>p\<rbrace> ; c))
   = \<lbrace>p\<rbrace> ; (rely ?R \<iinter> guar\<^sub>\<pi> ?R \<iinter> rely (r \<inter> ?R) \<iinter> guar\<^sub>\<pi> g \<iinter> c)"
  proof -
    have "local.inv p \<iinter> (rely (r \<inter> (- p \<triangleleft> UNIV \<union> UNIV \<triangleright> p)) \<iinter> guar\<^sub>\<pi> g \<iinter> \<lbrace>p\<rbrace> ; c) = \<lbrace>p\<rbrace> ; (evolve (- p \<triangleleft> UNIV \<union> UNIV \<triangleright> p) \<iinter> (rely (r \<inter> (- p \<triangleleft> UNIV \<union> UNIV \<triangleright> p)) \<iinter> guar\<^sub>\<pi> g \<iinter> c))"
      using inv_alt_def3 seq_conj.assert_op_sync' seq_conj.assert_op_sync_right by auto
    then show ?thesis
      using evolve_def seq_conj.sync_assoc by auto
  qed

  have "inv p \<iinter> (rely r \<iinter> guar\<^sub>\<pi> g \<iinter> c) = \<lbrace>p\<rbrace> ; (rely ?R \<iinter> guar\<^sub>\<pi> ?R \<iinter> rely r \<iinter> guar\<^sub>\<pi> g \<iinter> c)"
      by (rule lhs_normal)
  also have "\<dots> = inv p \<iinter> (rely (r \<inter> ?R) \<iinter> guar\<^sub>\<pi> g \<iinter> (\<lbrace>p\<rbrace> ; c))"
  proof -
    have "rely (- p \<triangleleft> UNIV \<union> UNIV \<triangleright> p) \<iinter> guar\<^sub>\<pi> (- p \<triangleleft> UNIV \<union> UNIV \<triangleright> p) \<iinter> rely (r \<inter> (- p \<triangleleft> UNIV \<union> UNIV \<triangleright> p)) = rely (- p \<triangleleft> UNIV \<union> UNIV \<triangleright> p) \<iinter> (guar\<^sub>\<pi> (- p \<triangleleft> UNIV \<union> UNIV \<triangleright> p) \<iinter> rely r)"
      by (simp add: combine_relies local.conj.conj_conj)
    then show ?thesis
      using rhs_normal seq_conj.sync_assoc by auto
  qed
  finally show ?thesis by simp
qed


(* Original lines 328-335. *)
text \<open>The Hoare-triple form of \<open>inv_extract_context\<close>.\<close>
lemma inv_extract_context_triple:
  "{. p0 .} inv p \<iinter> (rely r \<iinter> guar\<^sub>\<pi> g \<iinter> c) {. q .}
   \<longleftrightarrow>
   {. p0 .} inv p \<iinter>
      (rely (r \<inter> (-(p \<triangleleft> UNIV) \<union> (UNIV \<triangleright> p))) \<iinter>
        guar\<^sub>\<pi> g \<iinter> (\<lbrace>p\<rbrace> ; c)) {. q .}"
  using inv_extract_context by simp


(* Original lines 337-353. *)
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


(* Original lines 355-366. *)
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


(* Original lines 368-399. *)
text \<open>An invariant can be introduced provided it holds initially and a sufficient rely is present.\<close>
lemma inv_introduce_eq:
  assumes stable_r: "stable p r"
  shows "rely r \<iinter> guar\<^sub>\<pi> (UNIV \<triangleright> p) \<iinter> \<lbrace>p\<rbrace> ; c = rely r \<iinter> inv p \<iinter> c"
proof -
  have image_of_p_in_p: "p \<triangleleft> r = p \<triangleleft> r \<triangleright> p"
    by (meson assms stable_maintains_invariant)
  have split_r: "p \<triangleleft> r \<triangleright> p = r \<inter> (p \<triangleleft> (UNIV \<triangleright> p))"
    by (metis domain_restrict_inter range_restrict_inter seq.inf_quantale.right_neutral 
        seq.sup_inf_biq.op2.left_commute)
  have split_rely: "rely (p \<triangleleft> r \<triangleright> p) = rely r \<iinter> rely (p \<triangleleft> (UNIV \<triangleright> p))"
    by (simp add: rely_conj_rely split_r)
  have stable_domain_constrain: "stable p (UNIV \<triangleright> p)"
    by (simp add: range_restrict_image)
  have with_guar_eq: "rely r \<iinter> guar\<^sub>\<pi> (UNIV \<triangleright> p) \<iinter> \<lbrace>p\<rbrace> ; c = rely r \<iinter> inv p \<iinter> c"
  proof-
    have "rely r \<iinter> guar\<^sub>\<pi> (UNIV \<triangleright> p) \<iinter> \<lbrace>p\<rbrace> ; c =  (\<lbrace>p\<rbrace> ; rely r \<iinter> guar\<^sub>\<pi> (UNIV \<triangleright> p)) \<iinter> c"
      by (simp add: seq_conj.assert_op_sync_left seq_conj.assert_op_sync_right)
    also have "\<dots> = ((\<lbrace>p\<rbrace> ; \<tau> p) ; rely r \<iinter> guar\<^sub>\<pi> (UNIV \<triangleright> p)) \<iinter> c"
      by (simp add: seq.assert_op_test_idem)
    also have "\<dots> = ((\<lbrace>p\<rbrace> ; \<tau> p) ; rely (p \<triangleleft> r) \<iinter> guar\<^sub>\<pi> (p \<triangleleft> (UNIV \<triangleright> p))) \<iinter> c"
      by (simp add: assms seq_conj.assert_op_sync_left seq_par.seq_assoc stable_domain_constrain test_rely_guar_contrain_domain)
    also have "\<dots> = (\<lbrace>p\<rbrace> ; rely (p \<triangleleft> r \<triangleright> p) \<iinter> guar\<^sub>\<pi> (p \<triangleleft> (UNIV \<triangleright> p))) \<iinter> c"
      using image_of_p_in_p seq.assert_op_test_idem by auto
    also have "\<dots> = (\<lbrace>p\<rbrace> ; (rely r \<iinter> rely (p \<triangleleft> (UNIV \<triangleright> p))) \<iinter> guar\<^sub>\<pi> (p \<triangleleft> (UNIV \<triangleright> p))) \<iinter> c"
      by (simp add: split_rely)
    also have "\<dots> = rely r \<iinter> inv p \<iinter> c"
      by (simp add: evolve_def inv_alt_def2 local.conj.commute local.conj.left_commute seq_conj.assert_op_sync_right)
    finally show ?thesis .
  qed
  then show ?thesis .
qed


(* Original lines 401-411. *)
lemma inv_introduce: 
  assumes "stable p r"
  shows "rely r \<iinter> \<lbrace>p\<rbrace> ; c \<ge> rely r \<iinter> inv p \<iinter> c"
proof -
  have "rely r \<iinter> \<lbrace>p\<rbrace> ; c \<ge> rely r \<iinter> guar\<^sub>\<pi> (UNIV \<triangleright> p) \<iinter> \<lbrace>p\<rbrace> ; c " (is "_ \<ge> ?rhs")
    by (metis local.conj.commute pgm_guar_introduce seq_conj.sync_mono_left)
  also have "?rhs = rely r \<iinter> inv p \<iinter> c"
    using inv_introduce_eq assms by simp
  finally show ?thesis
    using evolve_extract_guar local.conj.commute local.conj.left_commute local.inv_def seq_conj.assert_op_sync_left by auto
qed


(* Original lines 413-423. *)
lemma inv_introduce_alt: "rely (UNIV \<triangleright> p) \<iinter> \<lbrace>p\<rbrace> ; c \<ge> inv p \<iinter> c"
proof -
  have stable_domain_constrain: "stable p (UNIV \<triangleright> p)"
    by (simp add: range_restrict_image)

  have "inv p \<iinter> c = rely (UNIV \<triangleright> p) \<iinter> inv p \<iinter> c"
    using inv_extract_rely local.conj.commute by auto

  then show ?thesis
    by (simp add: inv_introduce stable_domain_constrain)
qed


(* Original lines 425-433. *)
lemma inv_introduce_from_pre:
  assumes "p \<subseteq> pi"
  shows "rely (UNIV \<triangleright> pi) \<iinter> \<lbrace>p\<rbrace> ; c \<ge> inv pi \<iinter> \<lbrace>p\<rbrace> ; c"
proof -
  have "\<lbrace>pi\<rbrace> ; \<lbrace>p\<rbrace> = \<lbrace>p\<rbrace>"
    by (simp add: assms seq.assert_op_commute seq.assert_seq_implied_assert)
  then show ?thesis
    by (metis inv_introduce_alt seq_par.seq_assoc)
qed


(* Original lines 435-453. *)
lemma inv_inv: "(rely (UNIV \<triangleright> p) \<iinter> \<lbrace>p\<rbrace> ; c \<ge> inv p \<iinter> d) \<longleftrightarrow> (inv p \<iinter> c \<ge> inv p \<iinter> d)" 
proof (rule iffI)
  show "(rely (UNIV \<triangleright> p) \<iinter> \<lbrace>p\<rbrace> ; c \<ge> inv p \<iinter> d) \<Longrightarrow> (inv p \<iinter> c \<ge> inv p \<iinter> d)" 
  proof -
    assume assm: "rely (UNIV \<triangleright> p) \<iinter> \<lbrace>p\<rbrace> ; c \<ge> inv p \<iinter> d"
    have "inv p \<iinter> c = inv p \<iinter> rely (UNIV \<triangleright> p) \<iinter> \<lbrace>p\<rbrace> ; c"
      using inv_extract_rely_assert by blast
    also have "\<dots> \<ge> inv p \<iinter> d"
    proof -
      have "inv p \<iinter> (inv p \<iinter> d) \<le> inv p \<iinter> (\<lbrace>p\<rbrace> ; c \<iinter> rely (UNIV \<triangleright> p))"
        by (metis assm local.conj.commute seq_conj.sync_mono_right)
      then show ?thesis
        using seq_conj.sync_assoc seq_conj.sync_commute by fastforce
    qed
    finally show ?thesis .
  qed
  show "inv p \<iinter> c \<ge> inv p \<iinter> d \<Longrightarrow> rely (UNIV \<triangleright> p) \<iinter> \<lbrace>p\<rbrace> ; c \<ge> inv p \<iinter> d"
    using inv_introduce_alt order_trans by blast
qed


(* Original lines 455-514. *)
text \<open>An evolve invariant of \<open>p\<^sub>1\<close> can be strengthened to an invariant of \<open>p\<^sub>2\<close> provided \<open>p\<^sub>2\<close> 
      holds initially and the rely for \<open>p2\<close> is introduced\<close>
lemma inv_strengthen:
  assumes "p\<^sub>1 \<supseteq> p\<^sub>2"
  assumes "p\<^sub>2 \<triangleleft> (r \<triangleright> p\<^sub>1) \<subseteq> UNIV \<triangleright> p\<^sub>2"
  shows "\<lbrace>p\<^sub>2\<rbrace> ; (inv p\<^sub>1 \<iinter> rely r) \<ge> inv p\<^sub>2"
proof -
  have r2_le_r1: "UNIV \<triangleright> p\<^sub>2 \<subseteq> UNIV \<triangleright> p\<^sub>1"
    using assms(1)
    by (rule range_restrict_p_mono)

  have rely_absorb: "rely r \<iinter> rely (UNIV \<triangleright> p\<^sub>1) = rely (r \<triangleright> p\<^sub>1)"
  proof-
    have "r \<inter> (UNIV \<triangleright> p\<^sub>1) = r \<triangleright> p\<^sub>1"
      by (metis Int_commute boolean_algebra.conj_one_right range_restrict_inter)
    then show ?thesis
      by (simp add: rely_conj_rely)
  qed

  have stable_p2_range_restrict: "stable p\<^sub>2 (UNIV \<triangleright> p\<^sub>2)"
    by (simp add: range_restrict_image)

  have stable_p2_r: "stable p\<^sub>2 (r \<triangleright> p\<^sub>1)"
    by (metis assms(2) domain_restrict_remove inf.absorb_iff2 range_restrict_inter stable_def2 top_greatest)

  have restrict_guar: "\<lbrace>p\<^sub>2\<rbrace> ; (inv p\<^sub>1 \<iinter> rely r) \<ge> \<lbrace>p\<^sub>2\<rbrace> ; (rely (UNIV \<triangleright> p\<^sub>1) \<iinter> guar\<^sub>\<pi> (UNIV \<triangleright> p\<^sub>2) \<iinter> rely r)"
  proof-
     have "\<lbrace>p\<^sub>2\<rbrace> ; (inv p\<^sub>1 \<iinter> rely r) = \<lbrace>p\<^sub>2\<rbrace> ; ((\<lbrace>p\<^sub>1\<rbrace> ; rely (UNIV \<triangleright> p\<^sub>1) \<iinter> guar\<^sub>\<pi> (UNIV \<triangleright> p\<^sub>1)) \<iinter> rely r)"
      by (simp add: evolve_def local.inv_def seq_conj.assert_op_sync_left)
    also have "\<dots> = \<lbrace>p\<^sub>2\<rbrace> ; \<lbrace>p\<^sub>1\<rbrace> ;  (rely (UNIV \<triangleright> p\<^sub>1) \<iinter> guar\<^sub>\<pi> (UNIV \<triangleright> p\<^sub>1) \<iinter> rely r)"
      by (simp add: seq_conj.assert_op_sync_left seq_par.seq_assoc)
    also have "\<dots> = \<lbrace>p\<^sub>2\<rbrace> ; (rely (UNIV \<triangleright> p\<^sub>1) \<iinter> guar\<^sub>\<pi> (UNIV \<triangleright> p\<^sub>1) \<iinter> rely r)"
      by (simp add: assms(1) seq.assert_seq_implied_assert)
    also have "\<dots> \<ge> \<lbrace>p\<^sub>2\<rbrace> ; (rely (UNIV \<triangleright> p\<^sub>1) \<iinter> guar\<^sub>\<pi> (UNIV \<triangleright> p\<^sub>2) \<iinter> rely r)"
      by (simp add: pgm_guar_strengthen r2_le_r1 seq_conj.sync_mono_left seq_conj.sync_mono_right seq_par.seq_mono_right)
    finally show ?thesis .
  qed

  have expand_rely: "\<lbrace>p\<^sub>2\<rbrace> ; (rely (UNIV \<triangleright> p\<^sub>1) \<iinter> guar\<^sub>\<pi> (UNIV \<triangleright> p\<^sub>2) \<iinter> rely r) \<ge> \<lbrace>p\<^sub>2\<rbrace> ; rely (UNIV \<triangleright> p\<^sub>2) \<iinter> guar\<^sub>\<pi> (UNIV \<triangleright> p\<^sub>2)"
  proof-
    have "\<lbrace>p\<^sub>2\<rbrace> ; (rely (UNIV \<triangleright> p\<^sub>1) \<iinter> guar\<^sub>\<pi> (UNIV \<triangleright> p\<^sub>2) \<iinter> rely r) = \<lbrace>p\<^sub>2\<rbrace> ;  (rely r \<iinter> guar\<^sub>\<pi> (UNIV \<triangleright> p\<^sub>2) \<iinter> rely (UNIV \<triangleright> p\<^sub>1))"
      using local.conj.commute seq_conj.sync_assoc by auto
    also have "\<dots> = \<lbrace>p\<^sub>2\<rbrace> ; (rely r \<iinter> rely (UNIV \<triangleright> p\<^sub>1) \<iinter> guar\<^sub>\<pi> (UNIV \<triangleright> p\<^sub>2))"
      using local.conj.commute seq_conj.sync_assoc by auto
    also have "\<dots> = \<lbrace>p\<^sub>2\<rbrace> ; (rely (r \<triangleright> p\<^sub>1) \<iinter> guar\<^sub>\<pi> (UNIV \<triangleright> p\<^sub>2))"
      by (simp add: rely_absorb)
    also have "\<dots> =  (\<lbrace>p\<^sub>2\<rbrace> ; rely (r \<triangleright> p\<^sub>1) \<iinter> guar\<^sub>\<pi> (UNIV \<triangleright> p\<^sub>2))"
      by (simp add: seq_conj.assert_op_sync_left)
    also have "\<dots> =  (\<lbrace>p\<^sub>2\<rbrace> ; rely (p\<^sub>2 \<triangleleft> (r \<triangleright> p\<^sub>1)) \<iinter> guar\<^sub>\<pi> (UNIV \<triangleright> p\<^sub>2))"
      by (simp add: assert_rely_guar_contrain_rely_domain stable_p2_r stable_p2_range_restrict)
    also have "... \<ge> (\<lbrace>p\<^sub>2\<rbrace> ; rely (UNIV \<triangleright> p\<^sub>2) \<iinter> guar\<^sub>\<pi> (UNIV \<triangleright> p\<^sub>2))"
      by (simp add: assms(2) rely_weaken seq_conj.sync_mono_left seq_par.seq_mono_right)
    finally show ?thesis .
  qed

  have "\<lbrace>p\<^sub>2\<rbrace> ; rely (UNIV \<triangleright> p\<^sub>2) \<iinter> guar\<^sub>\<pi> (UNIV \<triangleright> p\<^sub>2) = inv p\<^sub>2"
    by (simp add: evolve_def local.inv_def seq_conj.assert_op_sync_left)
  then show ?thesis 
    using expand_rely restrict_guar by auto
qed


(* Original lines 516-524. *)
lemma inv_strengthen_alt:
  assumes "p\<^sub>1 \<supseteq> p\<^sub>2"
  shows "\<lbrace>p\<^sub>2\<rbrace> ; (inv p\<^sub>1 \<iinter> rely (UNIV \<triangleright> p\<^sub>2)) \<ge> inv p\<^sub>2"
proof -
  have "p\<^sub>2 \<triangleleft> ((UNIV \<triangleright> p\<^sub>2) \<triangleright> p\<^sub>1) \<subseteq> (UNIV \<triangleright> p\<^sub>2)"
    using domain_range_restrict_remove restrict_domain_range_assoc by blast
  then show ?thesis
    by (simp add: assms inv_strengthen) 
qed


(* Original lines 526-535. *)
lemma inv_pgm: "inv p \<iinter> \<pi> r = \<lbrace>p\<rbrace> ; \<pi>(r \<triangleright> p)" 
proof - 
  have "inv p \<iinter> \<pi> r = \<lbrace>p\<rbrace> ; (evolve (UNIV \<triangleright> p) \<iinter> \<pi> r)"
    by (simp add: local.inv_def seq_conj.assert_op_sync_left) 
  also have "\<dots> = \<lbrace>p\<rbrace> ; \<pi>(UNIV \<triangleright> p \<inter> r)" 
    by (simp only: evolve_conj_pgm)   
  also have "\<dots> = \<lbrace>p\<rbrace> ; \<pi>(r \<triangleright> p)" 
    by (simp add: inf_commute restrict_range_def)
  finally show ?thesis .
qed


(* Original lines 537-549. *)
lemma inv_pgm_alt: "inv p \<iinter> \<pi> r = inv p \<iinter> \<pi>(p \<triangleleft> r \<triangleright> p)" 
proof -
  have "inv p \<iinter> \<pi> r = \<lbrace>p\<rbrace> ; \<tau> p ; \<pi>(r \<triangleright> p)" 
    using inv_pgm by (simp add: seq.assert_op_test) 
  also have "\<dots> = \<lbrace>p\<rbrace> ; \<pi>(p \<triangleleft> r \<triangleright> p)" 
    by (metis pgm_test_pre restrict_domain_range_assoc seq_par.seq_assoc)
  also have "\<dots> = \<lbrace>p\<rbrace> ; \<pi>((p \<triangleleft> r \<triangleright> p) \<triangleright> p)"
    by (metis (no_types, lifting) inv_pgm local.conj.conj_idem seq_conj.assert_op_sync_left
        seq_conj.assert_op_sync_right seq_conj.sync_assoc)
  also have "\<dots> = inv p \<iinter> \<pi>(p \<triangleleft> r \<triangleright> p)"
    by (simp only: inv_pgm)
  finally show ?thesis .
qed


(* Original lines 551-575. *)
lemma inv_env: "inv p \<iinter> \<epsilon> r = \<lbrace>p\<rbrace> ; (\<epsilon> r \<squnion> \<epsilon>(r \<triangleright> (-p)) ; \<top>)" 
proof - 
  have range_restriction_complement: "\<And>r p. -range_restriction p = range_restriction (-p)"
    by auto
  have restrict_range_complement: "\<And>r p. -(r \<triangleright> p) = (-r) \<union> range_restriction (-p)"
    by (simp only: range_restriction_complement restrict_range_def compl_inf)
  have univ_restrict_range_complement: "-(UNIV \<triangleright> p) = UNIV \<triangleright> (-p)"
  proof-
    have "-(UNIV \<triangleright> p) = (-UNIV) \<union> range_restriction(-p)"
      by (rule restrict_range_complement)
    also have "\<dots> = UNIV \<triangleright> (-p)"
      by (simp add: restrict_range_def)
    finally show ?thesis .
  qed 

  have "inv p \<iinter> \<epsilon> r = \<lbrace>p\<rbrace> ; (evolve (UNIV \<triangleright> p) \<iinter> \<epsilon> r)"
    by (simp add: local.inv_def seq_conj.assert_op_sync_left) 
  also have "\<dots> = \<lbrace>p\<rbrace> ; (\<epsilon> r \<squnion> \<epsilon>(-(UNIV \<triangleright> p) \<inter> r); \<top>)" 
    by (simp only: evolve_conj_env)
  also have "\<dots> = \<lbrace>p\<rbrace> ; (\<epsilon> r \<squnion> \<epsilon>(UNIV \<triangleright> (-p) \<inter> r); \<top>)" 
    by (simp only: univ_restrict_range_complement)
  also have "\<dots> = \<lbrace>p\<rbrace> ; (\<epsilon> r \<squnion> \<epsilon>(r \<triangleright> (-p)); \<top>)" 
    by (simp add: inf_commute restrict_range_def)
  finally show ?thesis .
qed


(* Original lines 577-578. *)
lemma inv_env_alt: "inv p \<iinter> \<epsilon> r = inv p \<iinter> \<epsilon>(p \<triangleleft> r)"
  by (metis env_test_pre inv_distrib_seq inv_conj_extract_assert seq.assert_op_test_idem)


(* Original lines 580-597. *)
lemma inv_test_rel: "inv p \<iinter> \<tau>{\<sigma>. (\<sigma>,\<sigma>) \<in> q} = inv p \<iinter> \<tau>{\<sigma>. (\<sigma>,\<sigma>) \<in> p \<triangleleft> q \<triangleright> p}" 
proof -
  have z0: "\<And>r. {\<sigma>. \<sigma> \<in> p \<and> (\<sigma>,\<sigma>) \<in> r} = p \<inter> {\<sigma>. (\<sigma>,\<sigma>) \<in> r}" 
    by blast
  have "inv p \<iinter> \<tau>{\<sigma>. (\<sigma>,\<sigma>) \<in> q} = \<lbrace>p\<rbrace> ; \<tau>(p \<inter> {\<sigma>. (\<sigma>,\<sigma>) \<in> q})" 
    using inv_test_alt by blast
  also have "\<dots> = \<lbrace>p\<rbrace> ; \<tau>{\<sigma>. \<sigma> \<in> p \<and> (\<sigma>,\<sigma>) \<in> q}" 
    by (simp add: Collect_conj_eq) 
  also have "\<dots> = \<lbrace>p\<rbrace> ; \<tau>{\<sigma>. \<sigma> \<in> p \<and> (\<sigma>,\<sigma>) \<in> domain_restriction p \<inter> q \<inter> range_restriction p}" 
    by (simp add: Collect_conj_eq inf_sup_aci(1)) 
  also have "\<dots> = \<lbrace>p\<rbrace> ; \<tau>{\<sigma>. \<sigma> \<in> p \<and> (\<sigma>,\<sigma>) \<in> p \<triangleleft> q \<triangleright> p}" 
    by (simp add: restrict_domain_def restrict_range_def) 
  also have "\<dots> = \<lbrace>p\<rbrace> ; \<tau>(p \<inter> {\<sigma>. (\<sigma>,\<sigma>) \<in> p \<triangleleft> q \<triangleright> p})" 
    using z0 by simp 
  also have "\<dots> = inv p \<iinter> \<tau>{\<sigma>. (\<sigma>,\<sigma>) \<in> p \<triangleleft> q \<triangleright> p}" 
    using inv_test_alt by presburger
  finally show ?thesis .
qed


(* Original lines 599-610. *)
lemma inv_opt_equiv: "inv p \<iinter> opt q = inv p \<iinter> opt(p \<triangleleft> q \<triangleright> p)"
proof -
  have "inv p \<iinter> opt q = inv p \<iinter> \<pi> q \<squnion> inv p \<iinter> \<tau>{\<sigma>. (\<sigma>,\<sigma>) \<in> q}" 
    by (simp add: opt_def seq_conj.sync_sup) 
  also have "\<dots> = inv p \<iinter> \<pi>(p \<triangleleft> q \<triangleright> p) \<squnion> inv p \<iinter> \<tau>{\<sigma>. (\<sigma>,\<sigma>) \<in> q}" 
    using inv_pgm_alt by force 
  also have "\<dots> = inv p \<iinter> \<pi>(p \<triangleleft> q \<triangleright> p) \<squnion> inv p \<iinter> \<tau>{\<sigma>. (\<sigma>,\<sigma>) \<in> p \<triangleleft> q \<triangleright> p}" 
    using inv_test_rel by presburger
  also have "\<dots> = inv p \<iinter> opt(p \<triangleleft> q \<triangleright> p)" 
    by (simp add: opt_def seq_conj.sync_sup) 
  finally show ?thesis .
qed


(* Original lines 618-632. *)
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


(* Original lines 634-640. *)
lemma inv_atomic_pre: "inv I \<iinter> \<langle>p, q\<rangle> = inv I \<iinter> \<langle>I \<inter> p, q\<rangle>"
proof-
  have "inv I \<iinter> \<langle>p, q\<rangle> = inv I \<iinter> (idle ; (inv I \<iinter> \<lbrace>p\<rbrace>) ; opt q ; idle)"
    by (simp add: atomic_spec_def inv_distrib_seq)
  then show ?thesis
    by (simp add: atomic_spec_def inv_assert) 
qed


(* Original lines 642-643. *)
lemma inv_atomic_post: "inv I \<iinter> \<langle>p, q\<rangle> = inv I \<iinter> \<langle>p, I \<triangleleft> q \<triangleright> I\<rangle>"
  using inv_atomic_spec_equiv inv_atomic_pre by simp


(* Original lines 645-646. *)
lemma inv_rely_atomic_spec_equiv: "inv I \<iinter> rely r \<iinter> \<langle>p,q\<rangle> = inv I \<iinter> rely r \<iinter> \<langle>I \<inter> p,I \<triangleleft> q \<triangleright> I\<rangle>"
  using inv_atomic_spec_equiv local.conj.left_commute seq_conj.sync_assoc by auto


(* Original lines 648-651. *)
lemma inv_rely_atomic_spec_seq_equiv:
  "inv I \<iinter> rely r \<iinter> (\<langle>p,q\<rangle> ; c) =
    inv I \<iinter> rely r \<iinter> (\<langle>I \<inter> p,I \<triangleleft> q \<triangleright> I\<rangle> ; c)"
  using inv_atomic_spec_equiv inv_distrib_seq local.conj.left_commute seq_conj.sync_assoc by fastforce


(* Original lines 653-657. *)
lemma inv_rely_assert_atomic_spec_into_pre:
  assumes stable_a: "stable a (I \<triangleleft> r \<triangleright> I)"
  shows "inv I \<iinter> rely r \<iinter> (\<lbrace>a\<rbrace> ; \<langle>p,q\<rangle>) = inv I \<iinter> rely r \<iinter> (\<lbrace>a\<rbrace> ; \<langle>a \<inter> p,q\<rangle>)"
  by (rule inv_rely_restrict_cong
      [OF assert_atomic_spec_into_pre[OF stable_a]])


(* Original lines 659-686. *)
text \<open>Under an invariant, an atomic specification may establish an
assertion using the invariant-restricted atomic relation and rely.\<close>
lemma atomic_spec_extract_post_assert_under_invariant:
  assumes q_establishes_a_under_I: "(I \<inter> p) \<triangleleft> q \<triangleright> I \<subseteq> UNIV \<triangleright> a"
  assumes stable_a: "stable a (I \<triangleleft> r \<triangleright> I)"
  shows "inv I \<iinter> rely r \<iinter> \<langle>p,q\<rangle> = inv I \<iinter> rely r \<iinter> (\<langle>p,q\<rangle> ; \<lbrace>a\<rbrace>)"
proof -
  let ?p = "I \<inter> p"
  let ?q = "I \<triangleleft> q \<triangleright> I"
  let ?r = "I \<triangleleft> r \<triangleright> I"
  have establish_a: "?p \<triangleleft> ?q \<subseteq> UNIV \<triangleright> a"
  proof -
    have "?p \<triangleleft> ?q = (I \<inter> p) \<triangleleft> q \<triangleright> I"
      unfolding restrict_domain_def restrict_range_def by blast
    then show ?thesis
      using q_establishes_a_under_I by simp
  qed
  have extract_a: "rely ?r \<iinter> \<langle>?p,?q\<rangle> = rely ?r \<iinter> (\<langle>?p,?q\<rangle> ; \<lbrace>a\<rbrace>)"
    by (rule atomic_spec_extract_post_assert[OF establish_a stable_a])
  have extracted:
    "inv I \<iinter> rely r \<iinter> \<langle>?p,?q\<rangle> = inv I \<iinter> rely r \<iinter> (\<langle>?p,?q\<rangle> ; \<lbrace>a\<rbrace>)"
    by (rule inv_rely_restrict_cong[OF extract_a])
  have "inv I \<iinter> rely r \<iinter> \<langle>p,q\<rangle> = inv I \<iinter> rely r \<iinter> \<langle>?p,?q\<rangle>"
    by (rule inv_rely_atomic_spec_equiv)
  also have "\<dots> = inv I \<iinter> rely r \<iinter> (\<langle>p,q\<rangle> ; \<lbrace>a\<rbrace>)"
    using extracted inv_rely_atomic_spec_seq_equiv by auto
  finally show ?thesis .
qed


(* Original lines 688-721. *)
lemma atomic_spec_extract_post_assert_under_inv_rely_guar_ctx:
  assumes refl_g: "refl g"
  assumes q_establishes_a_under_ctx: "(I \<inter> p \<inter> p0) \<triangleleft> (q \<inter> g) \<triangleright> I \<subseteq> UNIV \<triangleright> a"
  assumes stable_a: "stable a (I \<triangleleft> r \<triangleright> I)"
  assumes stable_p0: "stable p0 (I \<triangleleft> r \<triangleright> I)"
  shows "inv I \<iinter> rely r \<iinter> guar\<^sub>\<pi> g \<iinter> \<lbrace>p0\<rbrace> ; \<langle>p,q\<rangle> = inv I \<iinter> rely r \<iinter> guar\<^sub>\<pi> g \<iinter> \<lbrace>p0\<rbrace> ; \<langle>p,q\<rangle> ; \<lbrace>a\<rbrace>"
proof -
  have guar_normal: "guar\<^sub>\<pi> g \<iinter> (\<lbrace>p0\<rbrace> ; \<langle>p,q\<rangle>) = \<lbrace>p0\<rbrace> ; \<langle>p,g \<inter> q\<rangle>"
    by (simp add: atomic_guar refl_g seq_conj.assert_op_sync_right)
  have guar_post_normal: "guar\<^sub>\<pi> g \<iinter> (\<lbrace>p0\<rbrace> ; \<langle>p,q\<rangle> ; \<lbrace>a\<rbrace>) = \<lbrace>p0\<rbrace> ; \<langle>p,g \<inter> q\<rangle> ; \<lbrace>a\<rbrace>"
    by (metis guar_normal local.conj.commute pgm_guar_conj_assert pgm_guar_conj_seq)
  have establish_a: "(I \<inter> (p0 \<inter> p)) \<triangleleft> (g \<inter> q) \<triangleright> I \<subseteq> UNIV \<triangleright> a"
    using q_establishes_a_under_ctx
    by (simp add: Int_assoc Int_left_commute Int_commute)
  have extract_a:
    "inv I \<iinter> rely r \<iinter> \<langle>p0 \<inter> p,g \<inter> q\<rangle> =  inv I \<iinter> rely r \<iinter> (\<langle>p0 \<inter> p,g \<inter> q\<rangle> ; \<lbrace>a\<rbrace>)"
    by (rule atomic_spec_extract_post_assert_under_invariant[OF establish_a stable_a])
  have into_pre:
    "inv I \<iinter> rely r \<iinter> (\<lbrace>p0\<rbrace> ; \<langle>p,g \<inter> q\<rangle>) = inv I \<iinter> rely r \<iinter> (\<lbrace>p0\<rbrace> ; \<langle>p0 \<inter> p,g \<inter> q\<rangle>)"
    by (rule inv_rely_assert_atomic_spec_into_pre[OF stable_p0])
  have into_pre_post:
    "inv I \<iinter> rely r \<iinter> (\<lbrace>p0\<rbrace> ; \<langle>p,g \<inter> q\<rangle> ; \<lbrace>a\<rbrace>) = inv I \<iinter> rely r \<iinter> (\<lbrace>p0\<rbrace> ; \<langle>p0 \<inter> p,g \<inter> q\<rangle> ; \<lbrace>a\<rbrace>)"
    by (rule inv_rely_restrict_cong
        [OF equal_within_rely_left[OF assert_atomic_spec_into_pre[OF stable_p0]]])
  have absorb_pre: "\<lbrace>p0\<rbrace> ; \<langle>p0 \<inter> p,g \<inter> q\<rangle> = \<langle>p0 \<inter> p,g \<inter> q\<rangle>"
    by (metis atomic_extract_pre_left seq.assert_inter_to_assert_left seq.assert_to_eq seq_par.seq_mono_left)
  have "inv I \<iinter> rely r \<iinter> guar\<^sub>\<pi> g \<iinter> \<lbrace>p0\<rbrace> ; \<langle>p,q\<rangle> = inv I \<iinter> rely r \<iinter> (\<lbrace>p0\<rbrace> ; \<langle>p,g \<inter> q\<rangle>)"
    using guar_normal by (simp add: seq_conj.sync_assoc)
  also have "\<dots> = inv I \<iinter> rely r \<iinter> (\<lbrace>p0\<rbrace> ; \<langle>p,g \<inter> q\<rangle> ; \<lbrace>a\<rbrace>)"
    by (simp add: absorb_pre extract_a into_pre into_pre_post)
  also have "\<dots> = inv I \<iinter> rely r \<iinter> guar\<^sub>\<pi> g \<iinter> \<lbrace>p0\<rbrace> ; \<langle>p,q\<rangle> ; \<lbrace>a\<rbrace>"
    using guar_post_normal by (simp add: seq_conj.sync_assoc)
  finally show ?thesis .
qed


(* Original lines 723-749. *)
lemma framed_atomic_spec_extract_post_assert_under_invariant:
  assumes q_establishes_a_under_I: "(I \<inter> p) \<triangleleft> q \<triangleright> I \<subseteq> UNIV \<triangleright> a"
  assumes stable_a: "stable a (I \<triangleleft> r \<triangleright> I)"
  shows "inv I \<iinter> rely r \<iinter> vars:\<^sub>s\<langle>p,q\<rangle> = inv I \<iinter> rely r \<iinter> (vars:\<^sub>s\<langle>p,q\<rangle> ; \<lbrace>a\<rbrace>)"
proof -
  have frame_atomic: "vars:\<^sub>s\<langle>p,q\<rangle> = \<langle>p, id_bar vars \<inter> q\<rangle>"
    by (rule atomic_frame)
  have establish_a:
    "(I \<inter> p) \<triangleleft> (id_bar vars \<inter> q) \<triangleright> I \<subseteq> UNIV \<triangleright> a"
  proof -
    have "(I \<inter> p) \<triangleleft> (id_bar vars \<inter> q) \<triangleright> I \<subseteq> (I \<inter> p) \<triangleleft> q \<triangleright> I"
      unfolding restrict_domain_def restrict_range_def by blast
    then show ?thesis
      using q_establishes_a_under_I by blast
  qed
  have extract_a:
    "inv I \<iinter> rely r \<iinter> \<langle>p, id_bar vars \<inter> q\<rangle> = inv I \<iinter> rely r \<iinter> (\<langle>p, id_bar vars \<inter> q\<rangle> ; \<lbrace>a\<rbrace>)"
    by (rule atomic_spec_extract_post_assert_under_invariant
        [OF establish_a stable_a])
  have "inv I \<iinter> rely r \<iinter> vars:\<^sub>s\<langle>p,q\<rangle> = inv I \<iinter> rely r \<iinter> \<langle>p, id_bar vars \<inter> q\<rangle>"
    using frame_atomic by simp
  also have "\<dots> = inv I \<iinter> rely r \<iinter>(\<langle>p, id_bar vars \<inter> q\<rangle> ; \<lbrace>a\<rbrace>)"
    by (rule extract_a)
  also have "\<dots> = inv I \<iinter> rely r \<iinter> (vars:\<^sub>s\<langle>p,q\<rangle> ; \<lbrace>a\<rbrace>)"
    using frame_atomic by simp
  finally show ?thesis .
qed


(* Original lines 751-764. *)
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


(* Original lines 766-774. *)
lemma inv_full_spec_equiv: "inv I \<iinter> \<lbrace>p\<rbrace> ; \<lparr>q\<rparr> = inv I \<iinter> \<lbrace>I \<inter> p\<rbrace> ; \<lparr>I \<triangleleft> q \<triangleright> I\<rparr>"
proof -
  have "inv I \<iinter> \<lbrace>p\<rbrace> ; \<lparr>q\<rparr> = (inv I \<iinter> \<lbrace>p\<rbrace>) ; (inv I \<iinter> \<lparr>q\<rparr>)"
    by (simp add: inv_distrib_seq)
  also have "\<dots> = (inv I \<iinter> \<lbrace>I \<inter> p\<rbrace>) ; (inv I \<iinter> \<lparr>I \<triangleleft> q \<triangleright> I\<rparr>)"
    using inv_assert inv_spec_equiv by force
  finally show ?thesis
    by (simp add: inv_distrib_seq)
qed
