(* Extracts from isabelle/new_rg_algebra/Commands/Data_Refinement.thy. *)
(* These are source excerpts, not a standalone buildable theory. *)

(* Original lines 11-13. *)
text \<open>Refinement in the context of an invariant.\<close>
definition data_refine :: "'a \<Rightarrow> 'state set \<Rightarrow> 'a \<Rightarrow> bool" ("_ \<ge>\<^sub>_ _" [35,1000,35] 36) where
  "data_refine c I d \<equiv> inv I \<iinter> c \<ge> inv I \<iinter> d"


(* Original lines 15-16. *)
lemma data_refine_refl: "c \<ge>\<^sub>I c" 
  by (simp add: data_refine_def) 


(* Original lines 18-22. *)
lemma data_refine_trans:
  assumes "c1 \<ge>\<^sub>I c2"
  assumes "c2 \<ge>\<^sub>I c3"
  shows "c1 \<ge>\<^sub>I c3" 
  using assms(1,2) data_refine_def by fastforce 


(* Original lines 26-29. *)
lemma refsto_implies_data_refine:
  assumes "c1 \<ge> c2"
  shows "c1 \<ge>\<^sub>I c2" 
  using assms data_refine_def seq_conj.sync_mono_right by blast 


(* Original lines 31-38. *)
text \<open>Invariant-aware extraction of an atomic postcondition\<close>
lemma data_refine_atomic_spec_extract_post_assert_under_invariant:
  assumes q_establishes_q'_under_I: "(I \<inter> p) \<triangleleft> q \<triangleright> I \<subseteq> UNIV \<triangleright> q'"
  assumes stable_q': "stable q' (I \<triangleleft> r \<triangleright> I)"
  shows "rely r \<iinter> \<langle>p,q\<rangle> \<ge>\<^sub>I  rely r \<iinter> (\<langle>p,q\<rangle> ; \<lbrace>q'\<rbrace>)"
  unfolding data_refine_def
  using atomic_spec_extract_post_assert_under_invariant
    [OF q_establishes_q'_under_I stable_q'] by (simp add: seq_conj.sync_assoc)


(* Original lines 40-46. *)
lemma data_refine_framed_atomic_spec_extract_post_assert_under_invariant:
  assumes q_establishes_q'_under_I: "(I \<inter> p) \<triangleleft> q \<triangleright> I \<subseteq> UNIV \<triangleright> q'"
  assumes stable_q': "stable q' (I \<triangleleft> r \<triangleright> I)"
  shows "rely r \<iinter> vars:\<^sub>s\<langle>p,q\<rangle> \<ge>\<^sub>I rely r \<iinter> (vars:\<^sub>s\<langle>p,q\<rangle> ; \<lbrace>q'\<rbrace>)"
  unfolding data_refine_def
  using framed_atomic_spec_extract_post_assert_under_invariant
    [OF q_establishes_q'_under_I stable_q'] by (simp add: seq_conj.sync_assoc)


(* Original lines 48-62. *)
text \<open>Monotonicity properties for data refinement.\<close>
lemma data_refine_Sup:
  assumes "\<forall>d \<in> D. \<exists>c \<in> C. c \<ge>\<^sub>I d"
  shows "\<Squnion>C \<ge>\<^sub>I \<Squnion>D" 
proof -
  have asm: "\<forall>d \<in> D. \<exists>c \<in> C. inv I \<iinter> c \<ge> inv I \<iinter> d" 
    using assms data_refine_def by blast 
  have "inv I \<iinter> \<Squnion>C = \<lbrace>I\<rbrace> ; (\<Squnion>c \<in> C. inv I \<iinter> c)" 
    by (simp add: inv_distrib_Sup) 
  also have "\<dots> \<ge> \<lbrace>I\<rbrace> ; (\<Squnion>d \<in> D. inv I \<iinter> d)" (is "_ \<ge> ?rhs") 
    by (meson SUP_mono asm seq.seq_mono_right)
  also have "?rhs = inv I \<iinter> (\<Squnion>d \<in> D. d)" 
    by (simp add: inv_distrib_Sup) 
  finally show ?thesis by (simp add: data_refine_def) 
qed


(* Original lines 64-73. *)
lemma data_refine_SUP:
  assumes "\<forall>j \<in> J. c j \<ge>\<^sub>I d j"
  shows "(\<Squnion>j \<in> J. c j) \<ge>\<^sub>I (\<Squnion>j \<in> J. d j)"
proof -
  have "\<forall>d \<in> {d j |j. j \<in> J}. \<exists>c \<in> {c j|j. j \<in> J}. c \<ge>\<^sub>I d" 
    using assms by blast 
  then have "\<Squnion>{c j|j. j \<in> J} \<ge>\<^sub>I \<Squnion>{d j |j. j \<in> J}" 
    using data_refine_Sup by presburger  
  then show ?thesis by (simp add: setcompr_eq_image)
qed


(* Original lines 75-79. *)
lemma data_refine_sup:
  assumes c1: "c1 \<ge>\<^sub>I d1"
  assumes c2: "c2 \<ge>\<^sub>I d2"
  shows "c1 \<squnion> c2 \<ge>\<^sub>I d1 \<squnion> d2" 
  using c1 c2 data_refine_def seq.sup_quantale.op_mono seq_conj.sync_sup by fastforce  


(* Original lines 81-91. *)
lemma data_refine_seq:
  assumes c1: "c1 \<ge>\<^sub>I d1"
  assumes c2: "c2 \<ge>\<^sub>I d2"
  shows "c1 ; c2 \<ge>\<^sub>I d1 ; d2" 
proof -
  have "inv I \<iinter> c1 ; c2 = (inv I \<iinter> c1) ; (inv I \<iinter> c2)" 
    by (simp add: inv_distrib_seq) 
  also have "\<dots> \<ge> (inv I \<iinter> d1) ; (inv I \<iinter> d2)" 
    using c1 c2 data_refine_def seq.seq_mono by force
  finally show ?thesis by (simp add: data_refine_def inv_distrib_seq)
qed


(* Original lines 93-103. *)
lemma data_refine_conj:
  assumes c1: "c1 \<ge>\<^sub>I d1"
  assumes c2: "c2 \<ge>\<^sub>I d2"
  shows "c1 \<iinter> c2 \<ge>\<^sub>I d1 \<iinter> d2"
proof -
  have "inv I \<iinter> (c1 \<iinter> c2) = (inv I \<iinter> c1) \<iinter> (inv I \<iinter> c2)" 
    using conj.conj_conj by presburger
  also have "\<dots> \<ge> (inv I \<iinter> d1) \<iinter> (inv I \<iinter> d2)" (is "_ \<ge> ?rhs") 
    using c1 c2 data_refine_def seq_conj.sync_mono by blast 
  finally show ?thesis using data_refine_def conj.conj_conj by force 
qed


(* Original lines 105-108. *)
lemma data_refine_add_conj:
  assumes "c1 \<ge>\<^sub>I c2"
  shows "x \<iinter> c1 \<ge>\<^sub>I x \<iinter> c2"
  by (simp add: assms data_refine_conj data_refine_refl)


(* Original lines 110-120. *)
lemma data_refine_par:
  assumes c1: "c1 \<ge>\<^sub>I d1"
  assumes c2: "c2 \<ge>\<^sub>I d2"
  shows "c1 \<parallel> c2 \<ge>\<^sub>I d1 \<parallel> d2"
proof - 
  have "inv I \<iinter> (c1 \<parallel> c2) = (inv I \<iinter> c1) \<parallel> (inv I \<iinter> c2)" 
    by (simp add: inv_distrib_par) 
  also have "\<dots> \<ge> (inv I \<iinter> d1) \<parallel> (inv I \<iinter> d2)" 
    using c1 c2 data_refine_def seq_par.sync_mono by force  
  finally show ?thesis using data_refine_def inv_distrib_par by force 
qed


(* Original lines 122-126. *)
lemma data_refine_power:
  assumes c: "c \<ge>\<^sub>I d"
  shows "c^i \<ge>\<^sub>I d^i"
  unfolding data_refine_def 
  using c data_refine_def inv_distrib_power seq.power_mono seq_par.seq_mono by auto


(* Original lines 128-132. *)
lemma data_refine_fiter:
  assumes c: "c \<ge>\<^sub>I d"
  shows "c* \<ge>\<^sub>I d*" 
  unfolding data_refine_def 
  using c data_refine_def inv_distrib_fiter seq.finite_iter_mono by force


(* Original lines 134-151. *)
lemma data_refine_iter:
  assumes c: "c \<ge>\<^sub>I d"
  shows "c\<^sup>\<omega> \<ge>\<^sub>I d\<^sup>\<omega>" 
proof -
  have ex_c: "inv I \<iinter> c \<ge> inv I \<iinter> d" 
    using c
    by (simp only: data_refine_def)
    
  have inside: "(inv I \<iinter> c)\<^sup>\<omega> \<ge> (inv I \<iinter> d)\<^sup>\<omega>"
    using ex_c
    by (simp only: seq.iter_mono)

  have outside: "inv I \<iinter> c\<^sup>\<omega> \<ge> inv I \<iinter> d\<^sup>\<omega>"
    using inside
    by (simp only: inv_distrib_iter)

  then show ?thesis using data_refine_def outside by auto
qed


(* Original lines 153-158. *)
lemma data_refine_infiter:
  assumes c: "c \<ge>\<^sub>I d"
  shows "c\<^sup>\<infinity> \<ge>\<^sub>I d\<^sup>\<infinity>" 
  unfolding data_refine_def  
  using assms data_refine_def inv_distrib_infiter seq.infinite_iter_mono
  by force


(* Original lines 160-170. *)
text \<open>Data refinement of primitive commands.\<close>
lemma data_refine_test:
  assumes "p1 \<supseteq> I \<inter> p2"
  shows "\<tau> p1 \<ge>\<^sub>I \<tau> p2" 
proof -
  have "inv I \<iinter> \<tau> p1 = \<lbrace>I\<rbrace> ; \<tau> p1" 
    by (simp add: inv_test) 
  also have "\<dots> \<ge> \<lbrace>I\<rbrace> ; \<tau>(I \<inter> p2)" (is "_ \<ge> ?rhs") 
    using assms seq.seq_mono_right seq.test_mono by blast 
  finally show ?thesis by (simp add: inv_test_alt data_refine_def inv_test)
qed


(* Original lines 172-183. *)
lemma data_refine_assert:
  assumes "I \<inter> p1 \<subseteq> p2"
  shows "\<lbrace>p1\<rbrace> \<ge>\<^sub>I \<lbrace>p2\<rbrace>" 
proof -
  have "inv I \<iinter> \<lbrace>p1\<rbrace> = \<lbrace>I \<inter> p1\<rbrace>" 
    using inv_assert by blast 
  also have "\<dots> \<ge> \<lbrace>I \<inter> p2\<rbrace>" (is "_ \<ge> ?rhs") 
    using assms seq.assert_to_assert by auto
  also have "?rhs = inv I \<iinter> \<lbrace>p2\<rbrace>" 
    using inv_assert by presburger
  finally show ?thesis by (simp add: data_refine_def) 
qed


(* Original lines 185-194. *)
lemma data_refine_pgm:
  assumes "r1 \<supseteq> I \<triangleleft> r2 \<triangleright> I"
  shows "\<pi> r1 \<ge>\<^sub>I \<pi> r2" 
proof -
  have "inv I \<iinter> \<pi> r1 \<ge> inv I \<iinter> \<pi>(I \<triangleleft> r2 \<triangleright> I)" (is "_ >= ?rhs")
    using assms pgm_mono seq_conj.sync_mono_right by auto 
  also have "?rhs = inv I \<iinter> \<pi> r2" 
    using inv_pgm_alt by simp
  finally show ?thesis by (simp add: data_refine_def) 
qed


(* Original lines 196-204. *)
lemma data_refine_env: (* Changed with new invariant *)
  assumes "r1 \<supseteq> I \<triangleleft> r2"
  shows "\<epsilon> r1 \<ge>\<^sub>I \<epsilon> r2" 
proof -
  have "inv I \<iinter> \<epsilon> r1 \<ge> inv I \<iinter> \<epsilon> (I \<triangleleft> r2)" (is "_ >= ?rhs")
    using assms env_mono seq_conj.sync_mono_right by auto
  then show ?thesis
    using data_refine_def inv_env_alt by auto
qed


(* Original lines 206-207. *)
lemma restrict_range_domain: "p \<triangleleft> (UNIV \<triangleright> p) \<inter> r = p \<triangleleft> r \<triangleright> p"
  by (metis domain_restrict_inter range_restrict_inter restrict_domain_range_assoc seq.inf_quantale.left_neutral)


(* Original lines 209-239. *)
lemma data_refine_env_assump:
  assumes "I \<triangleleft> r1 \<triangleright> I \<subseteq> r2"
  shows "env_assump r1 \<ge>\<^sub>I env_assump r2" 
proof -
  let ?r = "I \<triangleleft> (UNIV \<triangleright> I)"
  have refine_with_rely: "rely ?r \<iinter> env_assump r1 \<ge> env_assump r2"
  proof-
    have lhs: "rely ?r \<iinter> env_assump r1 = env_assump (I \<triangleleft> r1 \<triangleright> I)"
      using rely_conj_env_assump 
      by (simp only: restrict_range_domain)

    show ?thesis
      using assms env_assump_weaken lhs by auto
  qed

  have refine_with_inv_rely: "inv I \<iinter> rely ?r \<iinter> env_assump r1 \<ge> inv I \<iinter> env_assump r2"
  proof-
    have "inv I \<iinter> rely ?r \<iinter> env_assump r1 = inv I \<iinter> (rely ?r \<iinter> env_assump r1)"
      by (simp only: conj.assoc)
    also have "\<dots> \<ge> inv I \<iinter> env_assump r2"
      by (simp only: refine_with_rely seq_conj.sync_mono_right)
    finally show ?thesis .
  qed

  have expanded_data_refine: "inv I \<iinter> env_assump r1 \<ge> inv I \<iinter> env_assump r2"
    using refine_with_inv_rely inv_extract_rely2 by auto

  show ?thesis using expanded_data_refine data_refine_def by auto
qed

(* Changed since new invariant *)


(* Original lines 240-262. *)
text \<open>Data refinement of relies and guarantees.\<close>
lemma data_refine_guar:
  assumes "g1 \<supseteq> I \<triangleleft> g2 \<triangleright> I"
  assumes "r1 \<supseteq> I \<triangleleft> r2"
  shows "guar(g1,r1) \<ge>\<^sub>I guar(g2,r2)"
proof-
  let ?c1 = "\<pi> g1 \<squnion> \<epsilon> r1"
  let ?c2 = "\<pi> g2 \<squnion> \<epsilon> r2"

  have refine_basis: "\<pi> g1 \<squnion> \<epsilon> r1 \<ge>\<^sub>I \<pi> g2 \<squnion> \<epsilon> r2"
    using assms(1,2) data_refine_env data_refine_pgm data_refine_sup by force

  have non_test1: "nil \<iinter> ?c1 = seq.pre ?c1 ; \<bottom>"
    using guar_basis_conj_nil seq_conj.pre_seq_magic seq_conj.sync_magic_of_sync_neut by auto

  have non_test2: "nil \<iinter> ?c2 = seq.pre ?c2 ; \<bottom>"
    using guar_basis_conj_nil seq_conj.pre_seq_magic seq_conj.sync_magic_of_sync_neut by auto

  show ?thesis  
    using data_refine_iter guar_alt non_test1 non_test2 refine_basis by presburger
qed

(* Changed since new invariant *)


(* Original lines 263-291. *)
lemma data_refine_rely:
  assumes "I \<triangleleft> r1 \<triangleright> I \<subseteq> r2"
  shows "rely r1 \<ge>\<^sub>I rely r2"
proof -
  let ?r = "I \<triangleleft> (UNIV \<triangleright> I)"
  have refine_with_rely: "rely ?r \<iinter> rely r1 \<ge> rely r2"
  proof-
    have lhs: "rely ?r \<iinter> rely r1 = rely (I \<triangleleft> r1 \<triangleright> I)"
      using rely_conj_rely 
      by (simp only: restrict_range_domain)

    show ?thesis
      using assms rely_weaken lhs by auto
  qed

  have refine_with_inv_rely: "inv I \<iinter> rely ?r \<iinter> rely r1 \<ge> inv I \<iinter> rely r2"
  proof-
    have "inv I \<iinter> rely ?r \<iinter> rely r1 = inv I \<iinter> (rely ?r \<iinter> rely r1)"
      by (simp only: conj.assoc)
    also have "\<dots> \<ge> inv I \<iinter> rely r2"
      by (simp only: refine_with_rely seq_conj.sync_mono_right)
    finally show ?thesis .
  qed

  have expanded_data_refine: "inv I \<iinter> rely r1 \<ge> inv I \<iinter> rely r2"
    using refine_with_inv_rely inv_extract_rely2 by auto

  show ?thesis using expanded_data_refine data_refine_def by auto
qed


(* Original lines 293-302. *)
lemma data_refine_opt:
  assumes "q1 \<supseteq> I \<triangleleft> q2 \<triangleright> I"
  shows "opt q1 \<ge>\<^sub>I opt q2" 
proof -
  have "inv I \<iinter> opt q1 \<ge> inv I \<iinter> opt(I \<triangleleft> q2 \<triangleright> I)" (is "_ \<ge> ?rhs")
    by (simp add: assms opt_strengthen seq_conj.sync_mono_right) 
  also have "?rhs = inv I \<iinter> opt q2"
    using inv_opt_equiv by simp
  finally show ?thesis by (simp add: data_refine_def) 
qed


(* Original lines 304-307. *)
lemma data_refine_frame_mono:
  assumes "c1 \<ge>\<^sub>I c2"
  shows "v:\<^sub>sc1 \<ge>\<^sub>I v:\<^sub>sc2"
  by (simp add: assms data_refine_add_conj var_frame_set_def)


(* Original lines 309-335. *)
lemma data_refine_frame:
  assumes "I \<triangleleft> (id_bar vars2) \<triangleright> I \<subseteq> id_bar vars1"
  shows "vars1:\<^sub>sc \<ge>\<^sub>I vars2:\<^sub>sc"
proof-
  have r_inter: "I \<triangleleft> (UNIV \<triangleright> I) \<inter> (id_bar vars2) = I \<triangleleft> (id_bar vars2) \<triangleright> I "
    by (simp add: restrict_range_domain)

  have lhs: "vars1:\<^sub>sc = guar\<^sub>\<pi> (id_bar vars1) \<iinter> c"
    by (simp add: var_frame_set_def)

  have rhs: "vars2:\<^sub>sc = guar\<^sub>\<pi> (id_bar vars2) \<iinter> c"
    by (simp add: var_frame_set_def)

  have "vars2:\<^sub>sc \<iinter> inv I = inv I \<iinter> guar\<^sub>\<pi> (id_bar vars2) \<iinter> c"
    using rhs local.conj.commute seq_conj.sync_assoc by auto
  also have "\<dots> = inv I \<iinter> guar\<^sub>\<pi> (I \<triangleleft> (UNIV \<triangleright> I)) \<iinter> guar\<^sub>\<pi> (id_bar vars2) \<iinter> c"
    by (simp add: evolve_def inv_alt_def2 seq_conj.assert_op_sync_left)
  also have z: "\<dots> = inv I \<iinter> guar\<^sub>\<pi> (I \<triangleleft> (id_bar vars2) \<triangleright> I) \<iinter> c"
    by (simp add: pgm_guar_conj_pgm_guar r_inter seq_conj.sync_assoc)

  have "inv I \<iinter> guar\<^sub>\<pi> (id_bar vars1) \<iinter> c \<ge>\<^sub>I inv I \<iinter> guar\<^sub>\<pi> (I \<triangleleft> (id_bar vars2) \<triangleright> I) \<iinter> c"
    using assms pgm_guar_strengthen refsto_implies_data_refine
      seq_conj.sync_mono_left seq_conj.sync_mono_right by auto
  then show ?thesis
    using calculation data_refine_def lhs local.conj.commute seq_conj.sync_assoc
      z by force 
qed


(* Original lines 338-339. *)
lemma bind_inv_alt: "inv I \<iinter> bind e in body = inv I \<iinter> (\<Squnion>k. \<lblot>e\<rblot>k ; (inv I \<iinter> body k))"
  by (simp add: bind_command_def conj.op_Sup_UNIV inv_distrib_seq)


(* Original lines 341-342. *)
lemma bind_inv_alt2: "inv I \<iinter> bind e in body = (\<Squnion>k. inv I \<iinter> (\<lblot>e\<rblot>k ; body k))"
  by (simp add: bind_command_def conj.op_Sup_UNIV)


(* Original lines 344-345. *)
lemma bind_inv: "inv I \<iinter> bind e in body = inv I \<iinter> bind e in (\<lambda>k. inv I \<iinter> body k)"
  using bind_inv_alt bind_command_def by auto


(* Original lines 347-351. *)
lemma data_refine_bind:
  assumes step: "\<And>k2. \<exists>k1. \<lblot>e1\<rblot>k1 ; c1 k1 \<ge>\<^sub>I \<lblot>e2\<rblot>k2 ; c2 k2"
  shows "bind e1 in c1 \<ge>\<^sub>I bind e2 in c2"
  unfolding data_refine_def bind_inv_alt2
  by (rule SUP_mono) (use step data_refine_def in simp)


(* Original lines 353-364. *)
lemma data_refine_bind_mono':
  assumes step: "\<And>k. c k \<ge>\<^sub>I d k"
  shows "bind e in c \<ge>\<^sub>I bind e in d"
proof-
  have "bind e in (\<lambda>k. inv I \<iinter> c k) \<ge> bind e in (\<lambda>k. inv I \<iinter> d k)"
    using bind_ref_mono' data_refine_def step by auto
  then have "inv I \<iinter> bind e in (\<lambda>k. inv I \<iinter> c k) \<ge> inv I \<iinter> bind e in (\<lambda>k. inv I \<iinter> d k)"
    by (simp add: seq_conj.sync_mono_right)
  then have "inv I \<iinter> bind e in c \<ge> inv I \<iinter> bind e in d"
    using bind_inv_alt bind_command_def by auto
  then show ?thesis unfolding data_refine_def .
qed 


(* Original lines 366-370. *)
text \<open>A framed terminating command can always be reduced to one atomic
step satisfying the same frame.\<close>
lemma data_refine_framed_terminate_atomic:
  "vars:\<^sub>sterminate \<ge>\<^sub>I \<langle>UNIV, id_bar vars\<rangle>"
  by (rule refsto_implies_data_refine[OF framed_terminate_ref_atomic])


(* Original lines 372-375. *)
lemma data_refine_local_atomic_extract_framed_spec_left:
  "\<langle>p,q,vars\<rangle> \<ge>\<^sub>I vars:\<^sub>s\<lparr>q0\<rparr> ; \<langle>p,q,vars\<rangle>"
  by (rule refsto_implies_data_refine
      [OF local_atomic_extract_framed_spec_left])


(* Original lines 377-386. *)
lemma refine_local_atomic_from_atomic:
  assumes "rely rel \<iinter> guar\<^sub>\<pi> g \<iinter> \<lbrace>p0\<rbrace> ; v:\<^sub>s\<langle>p,post_rel\<rangle> \<ge>\<^sub>I c"
  shows "rely rel \<iinter> guar\<^sub>\<pi> g \<iinter> \<lbrace>p0\<rbrace> ; v:\<^sub>s\<langle>p,post_rel,L\<rangle> \<ge>\<^sub>I c"
proof -
  have "\<langle>p,post_rel,L\<rangle> \<ge>\<^sub>I \<langle>p,post_rel\<rangle>"
    by (simp add: atomic_ref_local_atomic refsto_implies_data_refine)
  then show ?thesis using assms
    by (meson data_refine_conj data_refine_frame_mono data_refine_refl
        data_refine_seq data_refine_trans)
qed


(* Original lines 388-460. *)
text \<open>Data refine atomics/local atomics to assign.
An invariant-aware form of \<open>chain_atomic_spec_ref_assign_op\<close>.

This is quite useful as often I want to establish some assertion necessary for the next spec
refinement.\<close>
lemma chain_data_refine_atomic_spec_to_assign_op:
  assumes refl_r: "refl r"
  assumes refl_g: "refl g"
  assumes stable_a: "stable p1 (r \<inter> (-(I \<triangleleft> UNIV) \<union> (UNIV \<triangleright> I)))"
  assumes establish_P1: "\<And>lv. {. I \<inter> p0 .} rely (r \<inter> (-(I \<triangleleft> UNIV) \<union> (UNIV \<triangleright> I))) \<iinter> \<ltort>lve\<rtort>lv {. P1 lv .}"
  assumes establish_P2: "\<And>k. {. I \<inter> p0 .} rely (r \<inter> (-(I \<triangleleft> UNIV) \<union> (UNIV \<triangleright> I))) \<iinter> \<lblot>e\<rblot>k {. P2 k .}"
  assumes establish_g_q_p1: "\<And>k lv. (I \<inter> p \<inter> P1 lv \<inter> P2 k) \<triangleleft> assign_op lv k \<triangleright> I \<subseteq> (g \<inter> q) \<triangleright> p1"
  shows "rely r \<iinter> guar\<^sub>\<pi> g \<iinter> (\<lbrace>p0\<rbrace> ; \<langle>p,q\<rangle>)
      \<ge>\<^sub>I (\<Squnion>lv k. (\<ltort>lve\<rtort>lv \<parallel> \<lblot>e\<rblot>k) ; opt (assign_op lv k) ; idle) ; \<lbrace>p1\<rbrace>"
proof -
  let ?R = "-(I \<triangleleft> UNIV) \<union> (UNIV \<triangleright> I)"
  have refl_R: "refl ?R" by (rule inv_rely_refl)
  have refl_rI: "refl (r \<inter> ?R)"
    using refl_R refl_on_Int refl_r by fastforce
  have establish_restricted:
    "\<And>k lv. (I \<inter> p \<inter> P1 lv \<inter> P2 k) \<triangleleft>
        (I \<triangleleft> assign_op lv k \<triangleright> I) \<subseteq> (g \<inter> q) \<triangleright> p1"
  proof -
    fix k lv
    show "(I \<inter> p \<inter> P1 lv \<inter> P2 k) \<triangleleft> (I \<triangleleft> assign_op lv k \<triangleright> I) \<subseteq> (g \<inter> q) \<triangleright> p1"
      by (metis Int_lower1 domain_restrict_twice establish_g_q_p1 inf.orderE
          restrict_domain_range_assoc)
  qed
  have op_ref: "guar\<^sub>\<pi> g \<iinter> rely (r \<inter> ?R) \<iinter> (\<lbrace>I \<inter> p0\<rbrace> ; \<langle>I \<inter> p,q\<rangle>)
             \<ge> (\<Squnion>lv k. (\<ltort>lve\<rtort>lv \<parallel> \<lblot>e\<rblot>k) ; opt (I \<triangleleft> assign_op lv k \<triangleright> I) ; idle) ; \<lbrace>p1\<rbrace>"
    using chain_atomic_spec_ref_assign_op[where assign_op = "\<lambda>lv k. I \<triangleleft> assign_op lv k \<triangleright> I"]
          assms refl_rI establish_restricted by presburger

  have inv_branch_equiv:
    "\<And>lv k. inv I \<iinter> ((\<ltort>lve\<rtort>lv \<parallel> \<lblot>e\<rblot>k) ; opt (assign_op lv k) ; idle)
     = inv I \<iinter> ((\<ltort>lve\<rtort>lv \<parallel> \<lblot>e\<rblot>k) ; opt (I \<triangleleft> assign_op lv k \<triangleright> I) ; idle)"
  proof -
    fix lv k
    have "inv I \<iinter> opt (assign_op lv k) = inv I \<iinter> opt (I \<triangleleft> assign_op lv k \<triangleright> I)"
      by (rule inv_opt_equiv)
    then show "inv I \<iinter> ((\<ltort>lve\<rtort>lv \<parallel> \<lblot>e\<rblot>k) ; opt (assign_op lv k) ; idle)
            =  inv I \<iinter> ((\<ltort>lve\<rtort>lv \<parallel> \<lblot>e\<rblot>k) ; opt (I \<triangleleft> assign_op lv k \<triangleright> I) ; idle)"
      by (simp add: inv_distrib_seq)
  qed
  have inv_op_equiv:
    "inv I \<iinter> ((\<Squnion>lv k. (\<ltort>lve\<rtort>lv \<parallel> \<lblot>e\<rblot>k) ; opt (assign_op lv k) ; idle) ; \<lbrace>p1\<rbrace>)
   = inv I \<iinter> ((\<Squnion>lv k. (\<ltort>lve\<rtort>lv \<parallel> \<lblot>e\<rblot>k) ; opt (I \<triangleleft> assign_op lv k \<triangleright> I) ; idle) ; \<lbrace>p1\<rbrace>)"
  proof -
    have "inv I \<iinter> (\<Squnion>lv k. (\<ltort>lve\<rtort>lv \<parallel> \<lblot>e\<rblot>k) ; opt (assign_op lv k) ; idle)
        = inv I \<iinter> (\<Squnion>lv k. (\<ltort>lve\<rtort>lv \<parallel> \<lblot>e\<rblot>k) ; opt (I \<triangleleft> assign_op lv k \<triangleright> I) ; idle)"
      by (simp add: conj.op_Sup_UNIV inv_branch_equiv)
    then show ?thesis
      by (simp add: inv_distrib_seq)
  qed

  have combine_asserts: "\<lbrace>I\<rbrace> ; \<lbrace>p0\<rbrace> = \<lbrace>I \<inter> p0\<rbrace>"
    by (simp add: seq.assert_op_assert)

  have ctx: "rely r \<iinter> guar\<^sub>\<pi> g \<iinter> (\<lbrace>p0\<rbrace> ; \<langle>I \<inter> p,q\<rangle>) \<ge>\<^sub>I rely (r \<inter> ?R) \<iinter> guar\<^sub>\<pi> g \<iinter> (\<lbrace>I\<rbrace> ; (\<lbrace>p0\<rbrace> ; \<langle>I \<inter> p,q\<rangle>))" (is "_ \<ge>\<^sub>I ?rhs")
    using data_refine_def inv_extract_context by auto
  have "inv I \<iinter> (rely r \<iinter> guar\<^sub>\<pi> g \<iinter> (\<lbrace>p0\<rbrace> ; \<langle>p,q\<rangle>)) = inv I \<iinter> (rely r \<iinter> guar\<^sub>\<pi> g \<iinter> (\<lbrace>p0\<rbrace> ; \<langle>I \<inter> p,q\<rangle>))"
    by (metis inv_atomic_pre conj.conj_conj inv_distrib_seq)
  also have "\<dots> \<ge> inv I \<iinter> (guar\<^sub>\<pi> g \<iinter> rely (r \<inter> ?R) \<iinter> (\<lbrace>I\<rbrace> ; (\<lbrace>p0\<rbrace> ; \<langle>I \<inter> p,q\<rangle>)))" (is "_ \<ge> ?rhs")
    using ctx by (simp add: data_refine_def local.conj.commute local.conj.left_commute)
  also have "?rhs = inv I \<iinter> (guar\<^sub>\<pi> g \<iinter> rely (r \<inter> ?R) \<iinter> (\<lbrace>I \<inter> p0\<rbrace> ; \<langle>I \<inter> p,q\<rangle>))"
    using combine_asserts by (metis seq_par.seq_assoc) 
  also have "\<dots> \<ge> inv I \<iinter> ((\<Squnion>lv k. (\<ltort>lve\<rtort>lv \<parallel> \<lblot>e\<rblot>k) ; opt (I \<triangleleft> assign_op lv k \<triangleright> I) ; idle) ; \<lbrace>p1\<rbrace>)" (is "_ \<ge> ?rhs")
    using op_ref seq_conj.sync_mono_right by blast
  also have "?rhs = inv I \<iinter> ((\<Squnion>lv k. (\<ltort>lve\<rtort>lv \<parallel> \<lblot>e\<rblot>k) ; opt (assign_op lv k) ; idle) ; \<lbrace>p1\<rbrace>)"
    using inv_op_equiv by simp
  finally show ?thesis
    by (simp add: data_refine_def)
qed


(* Original lines 462-486. *)
text \<open>The framed counterpart to \<open>chain_data_refine_atomic_spec_to_assign_op\<close>.\<close>
lemma chain_data_refine_framed_atomic_spec_to_assign_op:
  assumes refl_r: "refl r"
  assumes refl_g: "refl g"
  assumes stable_a: "stable p1 (r \<inter> (-(I \<triangleleft> UNIV) \<union> (UNIV \<triangleright> I)))"
  assumes establish_P1: "\<And>lv. {. I \<inter> p0 .} rely (r \<inter> (-(I \<triangleleft> UNIV) \<union> (UNIV \<triangleright> I))) \<iinter> \<ltort>lve\<rtort>lv {. P1 lv .}"
  assumes establish_P2: "\<And>k. {. I \<inter> p0 .} rely (r \<inter> (-(I \<triangleleft> UNIV) \<union> (UNIV \<triangleright> I))) \<iinter> \<lblot>e\<rblot>k {. P2 k .}"
  assumes establish_g_q_p1: "\<And>k lv. (I \<inter> p \<inter> P1 lv \<inter> P2 k) \<triangleleft> assign_op lv k \<triangleright> I
                                  \<subseteq> (id_bar vars \<inter> g \<inter> q) \<triangleright> p1"
  shows "rely r \<iinter> guar\<^sub>\<pi> g \<iinter> (\<lbrace>p0\<rbrace> ; vars:\<^sub>s\<langle>p,q\<rangle>)
      \<ge>\<^sub>I (\<Squnion>lv k. (\<ltort>lve\<rtort>lv \<parallel> \<lblot>e\<rblot>k) ; opt (assign_op lv k) ; idle) ; \<lbrace>p1\<rbrace>"
proof -
  have refl_frame_g: "refl (id_bar vars \<inter> g)"
    using id_bar_refl refl_g refl_on_Int by fastforce
  have general_ref: "rely r \<iinter> guar\<^sub>\<pi> (id_bar vars \<inter> g) \<iinter> (\<lbrace>p0\<rbrace> ; \<langle>p,q\<rangle>)
                  \<ge>\<^sub>I (\<Squnion>lv k. (\<ltort>lve\<rtort>lv \<parallel> \<lblot>e\<rblot>k) ; opt (assign_op lv k) ; idle) ; \<lbrace>p1\<rbrace>"
   using chain_data_refine_atomic_spec_to_assign_op assms refl_frame_g by presburger

  have frame_guar:
    "guar\<^sub>\<pi> (id_bar vars \<inter> g) = guar\<^sub>\<pi> g \<iinter> guar\<^sub>\<pi> (id_bar vars)"
    by (metis local.conj.commute pgm_guar_conj_pgm_guar)
  show ?thesis
    using general_ref frame_guar
    by (simp add: seq_conj.assert_op_sync_right seq_conj.sync_assoc var_frame_set_def)
qed


(* Original lines 488-498. *)
lemma chain_data_refine_framed_atomic_spec_to_open_assign:
  assumes refl_r: "refl r"
  assumes refl_g: "refl g"
  assumes stable_a: "stable p1 (r \<inter> (-(I \<triangleleft> UNIV) \<union> (UNIV \<triangleright> I)))"
  assumes establish_P1: "\<And>lv. {. I \<inter> p0 .} rely (r \<inter> (-(I \<triangleleft> UNIV) \<union> (UNIV \<triangleright> I))) \<iinter> \<ltort>lve\<rtort>lv {. P1 lv .}"
  assumes establish_P2: "\<And>k. {. I \<inter> p0 .} rely (r \<inter> (-(I \<triangleleft> UNIV) \<union> (UNIV \<triangleright> I))) \<iinter> \<lblot>e\<rblot>k {. P2 k .}"
  assumes establish_g_q_p1: "\<And>k lv. (I \<inter> p \<inter> P1 lv \<inter> P2 k) \<triangleleft> open_update lv k G \<triangleright> I
                                  \<subseteq> (id_bar vars \<inter> g \<inter> q) \<triangleright> p1"
  shows "rely r \<iinter> guar\<^sub>\<pi> g \<iinter> (\<lbrace>p0\<rbrace> ; vars:\<^sub>s\<langle>p,q\<rangle>) \<ge>\<^sub>I (lve := e open[G]) ; \<lbrace>p1\<rbrace>"
  using assms chain_data_refine_framed_atomic_spec_to_assign_op
      [where assign_op = "\<lambda>lv k. open_update lv k G"] open_assign_def by presburger


(* Original lines 500-515. *)
lemma chain_data_refine_framed_atomic_spec_to_open_assign_no_pre:
  assumes refl_r: "refl r"
  assumes refl_g: "refl g"
  assumes stable_a: "stable p1 (r \<inter> (-(I \<triangleleft> UNIV) \<union> (UNIV \<triangleright> I)))"
  assumes establish_P1: "\<And>lv. {. I .} rely (r \<inter> (-(I \<triangleleft> UNIV) \<union> (UNIV \<triangleright> I))) \<iinter> \<ltort>lve\<rtort>lv {. P1 lv .}"
  assumes establish_P2: "\<And>k. {. I .} rely (r \<inter> (-(I \<triangleleft> UNIV) \<union> (UNIV \<triangleright> I))) \<iinter> \<lblot>e\<rblot>k {. P2 k .}"
  assumes establish_g_q_p1: "\<And>k lv. (I \<inter> p \<inter> P1 lv \<inter> P2 k) \<triangleleft> open_update lv k G \<triangleright> I
                                  \<subseteq> (id_bar vars \<inter> g \<inter> q) \<triangleright> p1"
  shows "rely r \<iinter> guar\<^sub>\<pi> g \<iinter> vars:\<^sub>s\<langle>p,q\<rangle> \<ge>\<^sub>I (lve := e open[G]) ; \<lbrace>p1\<rbrace>"
proof-
  have "I \<inter> UNIV = I" by simp
  then have "rely r \<iinter> guar\<^sub>\<pi> g \<iinter> \<lbrace>UNIV\<rbrace> ; vars:\<^sub>s\<langle>p,q\<rangle> \<ge>\<^sub>I (lve := e open[G]) ; \<lbrace>p1\<rbrace>"
    using assms chain_data_refine_framed_atomic_spec_to_open_assign by presburger
  then show ?thesis
    by (simp add: seq.assert_neut)
qed


(* Original lines 517-535. *)
lemma chain_data_refine_framed_atomic_spec_to_open_assign_no_post:
  assumes refl_r: "refl r"
  assumes refl_g: "refl g"
  assumes establish_P1: "\<And>lv. {. I \<inter> p0 .} rely (r \<inter> (-(I \<triangleleft> UNIV) \<union> (UNIV \<triangleright> I))) \<iinter> \<ltort>lve\<rtort>lv {. P1 lv .}"
  assumes establish_P2: "\<And>k. {. I \<inter> p0 .} rely (r \<inter> (-(I \<triangleleft> UNIV) \<union> (UNIV \<triangleright> I))) \<iinter> \<lblot>e\<rblot>k {. P2 k .}"
  assumes establish_g_q: "\<And>k lv. (I \<inter> p \<inter> P1 lv \<inter> P2 k) \<triangleleft> open_update lv k G \<triangleright> I
                               \<subseteq> id_bar vars \<inter> g \<inter> q"
  shows "rely r \<iinter> guar\<^sub>\<pi> g \<iinter> (\<lbrace>p0\<rbrace> ; vars:\<^sub>s\<langle>p,q\<rangle>) \<ge>\<^sub>I lve := e open[G]"
proof -
  have univ_stable: "stable UNIV (r \<inter> (-(I \<triangleleft> UNIV) \<union> (UNIV \<triangleright> I)))"
    by simp
  have "\<And>k lv. (I \<inter> p \<inter> P1 lv \<inter> P2 k) \<triangleleft> open_update lv k G \<triangleright> I \<subseteq> (id_bar vars \<inter> g \<inter> q) \<triangleright> UNIV"
    using establish_g_q by (simp add: range_restrict_univ)
  then have general_ref: "rely r \<iinter> guar\<^sub>\<pi> g \<iinter> (\<lbrace>p0\<rbrace> ; vars:\<^sub>s\<langle>p,q\<rangle>) \<ge>\<^sub>I (lve := e open[G]) ; \<lbrace>UNIV\<rbrace>"
    using chain_data_refine_framed_atomic_spec_to_open_assign
      refl_r refl_g univ_stable establish_P1 establish_P2 by presburger
  then show ?thesis
    by (simp add: seq.assert_neut)
qed


(* Original lines 537-569. *)
lemma data_refine_intro_local_atomic_open_assign_left:
  assumes refl_r: "refl r"
  assumes refl_g: "refl g"
  assumes stable_a: "stable p1 (r \<inter> (-(I \<triangleleft> UNIV) \<union> (UNIV \<triangleright> I)))"
  assumes local_var_subset: "local_v |\<subseteq>| v"
  assumes establish_P1: "\<And>lv. {. I \<inter> p0 .} rely (r \<inter> (-(I \<triangleleft> UNIV) \<union> (UNIV \<triangleright> I))) \<iinter> \<ltort>lve\<rtort>lv {. P1 lv .}"
  assumes establish_P2: "\<And>k. {. I \<inter> p0 .} rely (r \<inter> (-(I \<triangleleft> UNIV) \<union> (UNIV \<triangleright> I))) \<iinter> \<lblot>e\<rblot>k {. P2 k .}"
  assumes establish_g_p1: "\<And>k lv. (I \<inter> P1 lv \<inter> P2 k) \<triangleleft> open_update lv k G \<triangleright> I 
                                \<subseteq> (id_bar local_v \<inter> g) \<triangleright> p1"
  shows "rely r \<iinter> guar\<^sub>\<pi> g \<iinter> \<lbrace>p0\<rbrace> ; v:\<^sub>s\<langle>p,q,local_v\<rangle>
     \<ge>\<^sub>I (lve := e open[G]) ; (rely r \<iinter> guar\<^sub>\<pi> g \<iinter> \<lbrace>p1\<rbrace> ; v:\<^sub>s\<langle>p,q,local_v\<rangle>)"
proof -
  have "\<And>k lv. (I \<inter> \<top> \<inter> P1 lv \<inter> P2 k) \<triangleleft> open_update lv k G \<triangleright> I 
             \<subseteq> (id_bar local_v \<inter> g \<inter> UNIV) \<triangleright> p1"
    using establish_g_p1 by simp
  then have local_open_assign:
    "rely r \<iinter> guar\<^sub>\<pi> g \<iinter> \<lbrace>p0\<rbrace> ; local_v:\<^sub>s\<langle>\<top>,UNIV\<rangle> \<ge>\<^sub>I (lve := e open[G]) ; \<lbrace>p1\<rbrace>"
    using chain_data_refine_framed_atomic_spec_to_open_assign assms by presburger
  have local_atomic_split: "\<lbrace>p0\<rbrace> ; v:\<^sub>s\<langle>p,q,local_v\<rangle> \<ge> \<lbrace>p0\<rbrace> ; local_v:\<^sub>s\<langle>\<top>,UNIV\<rangle> ; v:\<^sub>s\<langle>p,q,local_v\<rangle>"
    using framed_local_atomic_extract_framed_atomic_left_var_subset local_var_subset
    by (simp add: seq_par.seq_assoc seq_par.seq_mono_right)
  then have "rely r \<iinter> guar\<^sub>\<pi> g \<iinter> (\<lbrace>p0\<rbrace> ; v:\<^sub>s\<langle>p,q,local_v\<rangle>)
          \<ge>\<^sub>I rely r \<iinter> guar\<^sub>\<pi> g \<iinter> (\<lbrace>p0\<rbrace> ; local_v:\<^sub>s\<langle>\<top>,UNIV\<rangle> ; v:\<^sub>s\<langle>p,q,local_v\<rangle>)"
     by (meson data_refine_add_conj refsto_implies_data_refine)
  also have "\<dots> =
      (rely r \<iinter> guar\<^sub>\<pi> g \<iinter> (\<lbrace>p0\<rbrace> ; local_v:\<^sub>s\<langle>\<top>,UNIV\<rangle>)) ; (rely r \<iinter> guar\<^sub>\<pi> g \<iinter> v:\<^sub>s\<langle>p,q,local_v\<rangle>)"
    by (simp add: rely_conj_seq pgm_guar_conj_seq seq_conj.sync_assoc seq_par.seq_assoc)
  also have "\<dots> \<ge>\<^sub>I ((lve := e open[G]) ; \<lbrace>p1\<rbrace>) ; (rely r \<iinter> guar\<^sub>\<pi> g \<iinter> v:\<^sub>s\<langle>p,q,local_v\<rangle>)"
    by (rule data_refine_seq[OF local_open_assign data_refine_refl])
  also have "\<dots> = (lve := e open[G]) ; (rely r \<iinter> guar\<^sub>\<pi> g \<iinter> (\<lbrace>p1\<rbrace> ; v:\<^sub>s\<langle>p,q,local_v\<rangle>))"
    by (simp add: seq_conj.assert_op_sync_right seq_par.seq_assoc)
  finally show ?thesis .
qed


(* Original lines 571-591. *)
lemma data_refine_intro_local_atomic_open_assign_left_no_pre:
  assumes refl_r: "refl r"
  assumes refl_g: "refl g"
  assumes stable_a: "stable p1 (r \<inter> (-(I \<triangleleft> UNIV) \<union> (UNIV \<triangleright> I)))"
  assumes local_var_subset: "local_v |\<subseteq>| v"
  assumes establish_P1: "\<And>lv. {. I .} rely (r \<inter> (-(I \<triangleleft> UNIV) \<union> (UNIV \<triangleright> I))) \<iinter> \<ltort>lve\<rtort>lv {. P1 lv .}"
  assumes establish_P2: "\<And>k. {. I .} rely (r \<inter> (-(I \<triangleleft> UNIV) \<union> (UNIV \<triangleright> I))) \<iinter> \<lblot>e\<rblot>k {. P2 k .}"
  assumes establish_g_p1:
    "\<And>k lv. (I \<inter> P1 lv \<inter> P2 k) \<triangleleft> open_update lv k G \<triangleright> I
      \<subseteq> (id_bar local_v \<inter> g) \<triangleright> p1"
  shows "rely r \<iinter> guar\<^sub>\<pi> g \<iinter> v:\<^sub>s\<langle>p,q,local_v\<rangle>
      \<ge>\<^sub>I lve := e open[G] ; (rely r \<iinter> guar\<^sub>\<pi> g \<iinter> \<lbrace>p1\<rbrace> ; v:\<^sub>s\<langle>p,q,local_v\<rangle>)"
proof -
  have "I \<inter> UNIV = I" by simp
  then have "rely r \<iinter> guar\<^sub>\<pi> g \<iinter> \<lbrace>UNIV\<rbrace> ; v:\<^sub>s\<langle>p,q,local_v\<rangle>
          \<ge>\<^sub>I lve := e open[G] ; (rely r \<iinter> guar\<^sub>\<pi> g \<iinter> \<lbrace>p1\<rbrace> ; v:\<^sub>s\<langle>p,q,local_v\<rangle>)"
    using data_refine_intro_local_atomic_open_assign_left assms
    by presburger
  then show ?thesis
    by (simp add: seq.assert_neut)
qed


(* Original lines 593-599. *)
lemma data_refine_constant:
  assumes "\<kappa>2 = k2 \<Longrightarrow> \<kappa>1 = k1"
  shows "\<lblot>Constant \<kappa>1\<rblot>k1 \<ge>\<^sub>I \<lblot>Constant \<kappa>2\<rblot>k2" 
  by (simp add: assms refsto_implies_data_refine) 

(* TODO what about different k *)
(* TODO unary to e2, requires thinking about types *)


(* Original lines 600-613. *)
lemma data_refine_unary:
  assumes "\<forall>k1'. (\<exists>k1. unop k1 = unop k1' \<and> (\<lblot>e1\<rblot>k1 \<ge>\<^sub>I \<lblot>e1'\<rblot>k1'))" 
  shows "\<lblot>Unary unop e1\<rblot>k \<ge>\<^sub>I \<lblot>Unary unop e1'\<rblot>k" 
proof -
  have assm: "\<forall>d \<in> {\<lblot>e1'\<rblot>k1' |k1'. unop k1' = k}. \<exists>c \<in> {\<lblot>e1\<rblot>k1 |k1. unop k1 = k}. c \<ge>\<^sub>I d" 
    using assms by auto
  have "\<lblot>Unary unop e1\<rblot>k = \<Squnion>{\<lblot>e1\<rblot>k1 |k1. unop k1 = k}" 
    by (simp add: setcompr_eq_image)  
  also have z1: "\<dots> \<ge>\<^sub>I \<Squnion>{\<lblot>e1'\<rblot>k1' |k1'. unop k1' = k}" 
    using assm data_refine_Sup data_refine_refl data_refine_seq by presburger
  have z2: "\<Squnion>{\<lblot>e1'\<rblot>k1' |k1'. unop k1' = k} = \<lblot>Unary unop e1'\<rblot>k" 
    by (simp add: setcompr_eq_image)
  show ?thesis using z1 z2 using calculation by argo 
qed


(* Original lines 615-630. *)
lemma data_refine_binary:
  assumes "\<forall>k1' k2'. (\<exists>k1 k2. binop k1 k2 = binop2 k1' k2' \<and> (\<lblot>e1\<rblot>k1 \<ge>\<^sub>I \<lblot>e1'\<rblot>k1') \<and> (\<lblot>e2\<rblot>k2 \<ge>\<^sub>I \<lblot>e2'\<rblot>k2'))" 
  shows "\<lblot>Binary binop e1 e2\<rblot>k \<ge>\<^sub>I \<lblot>Binary binop2 e1' e2'\<rblot>k" 
proof -
  have asm: "\<forall>k1' k2'. (\<exists>k1 k2. binop k1 k2 = binop2 k1' k2' \<and> (\<lblot>e1\<rblot>k1 \<parallel> \<lblot>e2\<rblot>k2 \<ge>\<^sub>I \<lblot>e1'\<rblot>k1' \<parallel> \<lblot>e2'\<rblot>k2'))"
    using assms data_refine_par by blast
  have both: "\<forall>d \<in> {\<lblot>e1'\<rblot>k1' \<parallel> \<lblot>e2'\<rblot>k2' |k1' k2'. binop2 k1' k2' = k}. \<exists>c \<in> {\<lblot>e1\<rblot>k1 \<parallel> \<lblot>e2\<rblot>k2 |k1 k2. binop k1 k2 = k}. c \<ge>\<^sub>I d" 
    using asm by fastforce
  have "\<lblot>Binary binop e1 e2\<rblot>k = (\<Squnion>{\<lblot>e1\<rblot>k1 \<parallel> \<lblot>e2\<rblot>k2 |k1 k2. binop k1 k2 = k})" 
    using binary_alt by force
  also have z1: "\<dots> \<ge>\<^sub>I \<Squnion>{\<lblot>e1'\<rblot>k1' \<parallel> \<lblot>e2'\<rblot>k2' |k1' k2'. binop2 k1' k2' = k}" 
    using both data_refine_Sup data_refine_refl data_refine_seq by presburger
  have z2: "\<Squnion>{\<lblot>e1'\<rblot>k1' \<parallel> \<lblot>e2'\<rblot>k2' |k1' k2'. binop2 k1' k2' = k} = \<lblot>Binary binop2 e1' e2'\<rblot>k" 
    by simp 
  show ?thesis using z1 z2 calculation by argo
qed


(* Original lines 632-652. *)
lemma data_refine_while:
  assumes bt: "\<lblot>b1\<rblot>true \<ge>\<^sub>I \<lblot>b2\<rblot>true"
  assumes bf: "\<lblot>b1\<rblot>false \<ge>\<^sub>I \<lblot>b2\<rblot>false"
  assumes c: "c1 \<ge>\<^sub>I c2"
  assumes bk: "\<And>k. k \<in> -boolean \<Longrightarrow> \<lblot>b1\<rblot>k \<ge>\<^sub>I \<lblot>b2\<rblot>k"
  shows "while b1 do c1 od \<ge>\<^sub>I while b2 do c2 od"
proof -
  have t: "\<lblot>b1\<rblot>true ; c1 \<ge>\<^sub>I \<lblot>b2\<rblot>true ; c2" 
    by (simp add: bt c data_refine_seq) 
  have "\<And>k. k \<in> -boolean \<Longrightarrow> \<lblot>b1\<rblot>k ; \<top> \<ge>\<^sub>I \<lblot>b2\<rblot>k ; \<top>" 
    by (simp add: bk data_refine_refl data_refine_seq) 
  then have bk: "(\<Squnion>k \<in> -boolean. \<lblot>b1\<rblot>k ; \<top>) \<ge>\<^sub>I (\<Squnion>k \<in> -boolean. \<lblot>b2\<rblot>k ; \<top>)" 
    by (simp add: data_refine_SUP)
  have "while b1 do c1 od = (\<lblot>b1\<rblot>true ; c1)\<^sup>\<omega> ; (\<lblot>b1\<rblot>false \<squnion> (\<Squnion>k\<in>-boolean. \<lblot>b1\<rblot>k ; \<top>))"
    by (simp add: while_command_def)
  also have z: "\<dots> \<ge>\<^sub>I (\<lblot>b2\<rblot>true ; c2)\<^sup>\<omega> ; (\<lblot>b2\<rblot>false \<squnion> (\<Squnion>k\<in>-boolean. \<lblot>b2\<rblot>k ; \<top>))" (is "_ \<ge>\<^sub>I ?rhs")
    using data_refine_iter data_refine_sup data_refine_seq t bk bf data_refine_refl by presburger
  have "?rhs =  while b2 do c2 od" 
    by (simp add: while_command_def) 
  then show ?thesis using calculation z by argo
qed


(* Original lines 654-659. *)
lemma data_refine_while_alt:
  assumes b: "\<And>k. \<lblot>b1\<rblot>k \<ge>\<^sub>I \<lblot>b2\<rblot>k"
  assumes c: "c1 \<ge>\<^sub>I c2"
  shows "while b1 do c1 od \<ge>\<^sub>I while b2 do c2 od"
  using data_refine_while
  by (simp add: b c)


(* Original lines 661-684. *)
lemma data_refine_conditional:
  assumes bt: "\<lblot>b1\<rblot>true \<ge>\<^sub>I \<lblot>b2\<rblot>true"
  assumes bf: "\<lblot>b1\<rblot>false \<ge>\<^sub>I \<lblot>b2\<rblot>false"
  assumes c: "c1 \<ge>\<^sub>I c2"
  assumes d: "d1 \<ge>\<^sub>I d2"
  assumes bk: "\<And>k. k \<in> -boolean \<Longrightarrow> \<lblot>b1\<rblot>k \<ge>\<^sub>I \<lblot>b2\<rblot>k"
  shows "if b1 then c1 else d1 fi \<ge>\<^sub>I if b2 then c2 else d2 fi"
proof -
  have t: "\<lblot>b1\<rblot>true ; c1 \<ge>\<^sub>I \<lblot>b2\<rblot>true ; c2" 
    by (simp add: bt c data_refine_seq) 
  have f: "\<lblot>b1\<rblot>false ; d1 \<ge>\<^sub>I \<lblot>b2\<rblot>false ; d2" 
    by (simp add: bf d data_refine_seq)
  have "\<And>k. k \<in> -boolean \<Longrightarrow> \<lblot>b1\<rblot>k ; \<top> \<ge>\<^sub>I \<lblot>b2\<rblot>k ; \<top>" 
    by (simp add: bk data_refine_refl data_refine_seq) 
  then have bk: "(\<Squnion>k \<in> -boolean. \<lblot>b1\<rblot>k ; \<top>) \<ge>\<^sub>I (\<Squnion>k \<in> -boolean. \<lblot>b2\<rblot>k ; \<top>)" 
    by (simp add: data_refine_SUP)
  have "if b1 then c1 else d1 fi = \<lblot>b1\<rblot>true ; c1 \<squnion> \<lblot>b1\<rblot>false ; d1 \<squnion> (\<Squnion>k \<in> -boolean. \<lblot>b1\<rblot>k ; \<top>)"
    unfolding if_command_def by blast
  also have z: "\<dots> \<ge>\<^sub>I \<lblot>b2\<rblot>true ; c2 \<squnion> \<lblot>b2\<rblot>false ; d2 \<squnion> (\<Squnion>k \<in> -boolean. \<lblot>b2\<rblot>k ; \<top>)" (is "_ \<ge>\<^sub>I ?rhs")
    using data_refine_sup data_refine_seq t f bk data_refine_refl by presburger
  have "?rhs = if b2 then c2 else d2 fi" 
    by (simp add: if_command_def) 
  then show ?thesis using calculation z by argo
qed


(* Original lines 686-697. *)
lemma data_refine_gfp:
  assumes "inv I \<iinter> gfp f1 = gfp(\<lambda>x. inv I \<iinter> f1 x)" 
  assumes "inv I \<iinter> gfp f2 = gfp(\<lambda>x. inv I \<iinter> f2 x)" 
  assumes "\<And>x. f1 x \<ge>\<^sub>I f2 x"
  shows "gfp f1 \<ge>\<^sub>I gfp f2" 
proof -
  have "inv I \<iinter> gfp f1 \<ge> gfp(\<lambda>x. inv I \<iinter> f2 x)" (is "_ \<ge> ?rhs") 
    by (metis assms(1,3) data_refine_def gfp_mono) 
  also have "?rhs = inv I \<iinter> gfp f2" 
    by (simp add: assms(2)) 
  finally show ?thesis by (simp add: data_refine_def) 
qed


(* Original lines 699-755. *)
lemma data_refine_atomic_spec:
  assumes "I \<inter> p1 \<subseteq> p2"
  assumes "(I \<inter> p1) \<triangleleft> q2 \<triangleright> I \<subseteq> q1"
  shows "\<langle>p1,q1\<rangle> \<ge>\<^sub>I \<langle>p2,q2\<rangle>" 
proof -
  have "(I \<inter> p1) \<triangleleft> q1 \<triangleright> I \<supseteq>  (I \<inter> p1) \<triangleleft> ((I \<inter> p1) \<triangleleft> q2 \<triangleright> I) \<triangleright> I"
    by (simp add: assms(2) domain_restrict_q_mono
        range_restrict_q_mono)
  also have stengthen_post: "\<langle>I \<inter> p1, (I \<inter> p1) \<triangleleft> q1 \<triangleright> I\<rangle> \<ge> \<langle>I \<inter> p1,  (I \<inter> p1) \<triangleleft> ((I \<inter> p1) \<triangleleft> q2 \<triangleright> I) \<triangleright> I\<rangle>"
    by (simp add: atomic_spec_strengthen_post calculation)

  have remove_double_restrict: "(I \<inter> p1) \<triangleleft> ((I \<inter> p1) \<triangleleft> q2 \<triangleright> I) \<triangleright> I =  (I \<inter> p1) \<triangleleft> q2 \<triangleright> I"
    by (simp add: domain_restrict_twice range_restrict_twice
        restrict_domain_range_assoc)

  have assoc_range_restrict: "(I \<inter> p1) \<triangleleft> (q2 \<triangleright> I) = (I \<inter> p1) \<triangleleft> q2 \<triangleright> I"
    by (simp add: restrict_domain_range_assoc)

  have "\<langle>I \<inter> p1, (I \<inter> p1) \<triangleleft> (q2 \<triangleright> I)\<rangle> = \<langle>I \<inter> p1, q2 \<triangleright> I\<rangle>"
    using atomic_spec_pre_internalise by auto
  then have remove_left_restrict: "\<langle>I \<inter> p1, (I \<inter> p1) \<triangleleft> q2 \<triangleright> I\<rangle> = \<langle>I \<inter> p1, q2 \<triangleright> I\<rangle>"
    by (simp add: assoc_range_restrict)

  have refinement:
    "inv I \<iinter> \<langle>p1,q1\<rangle> \<ge> inv I \<iinter> \<langle>p2,q2\<rangle>"
  proof -
    have "inv I \<iinter> \<langle>p1,q1\<rangle> = inv I \<iinter> \<langle>p1,p1 \<triangleleft> q1\<rangle>"
      using atomic_spec_pre_internalise by auto
    also have "\<dots> = inv I \<iinter> \<langle>I \<inter> p1, I \<triangleleft> (p1 \<triangleleft> q1) \<triangleright> I\<rangle>"
      using inv_atomic_spec_equiv by auto
    also have "\<dots> = inv I \<iinter> \<langle>I \<inter> p1, (I \<inter> p1) \<triangleleft> q1 \<triangleright> I\<rangle>"
      by (simp add: domain_restrict_twice)
    also have "\<dots> \<ge> inv I \<iinter> \<langle>I \<inter> p1,
        (I \<inter> p1) \<triangleleft> ((I \<inter> p1) \<triangleleft> q2 \<triangleright> I) \<triangleright> I\<rangle>"
      (is "_ \<ge> ?rhs")
      by (simp add: stengthen_post seq_conj.sync_mono_right)
    also have "?rhs = inv I \<iinter> \<langle>I \<inter> p1, q2 \<triangleright> I\<rangle>"
      using remove_left_restrict remove_double_restrict by simp
    also have "\<dots> \<ge> inv I \<iinter> \<langle>p2, q2 \<triangleright> I\<rangle>" (is "_ \<ge> ?rhs")
      by (simp add: assms(1) atomic_spec_weaken_pre seq_conj.sync_mono_right)
    also have "?rhs = inv I \<iinter> \<langle>I \<inter> p2,
        I \<triangleleft> (q2 \<triangleright> I) \<triangleright> I\<rangle>"
      using inv_atomic_spec_equiv by auto
    also have "\<dots> = inv I \<iinter> \<langle>I \<inter> p2, I \<triangleleft> q2 \<triangleright> I\<rangle>"
    proof -
      have "I \<triangleleft> q2 \<triangleright> I = I \<triangleleft> (q2 \<triangleright> I) \<triangleright> I"
        by (simp add: range_restrict_twice restrict_domain_range_assoc)
      then show ?thesis by simp
    qed
    also have "\<dots> = inv I \<iinter> \<langle>p2,q2\<rangle>"
      using inv_atomic_spec_equiv by auto
    finally show ?thesis .
  qed
  show ?thesis
    unfolding data_refine_def
    using refinement .
qed


(* Original lines 757-768. *)
lemma data_refine_local_atomic_spec:
  assumes "I \<inter> p1 \<subseteq> p2"
  assumes "(I \<inter> p1) \<triangleleft> q2 \<triangleright> I \<subseteq> q1"
  shows "\<langle>p1,q1,v\<rangle> \<ge>\<^sub>I \<langle>p2,q2,v\<rangle>" 
proof -
  have "\<langle>p1,q1\<rangle> \<ge>\<^sub>I \<langle>p2,q2\<rangle>"
    by (simp add: assms(1,2) data_refine_atomic_spec)
  also have "\<And>c. c ; \<langle>p1,q1\<rangle> ; c \<ge>\<^sub>I c ; \<langle>p2,q2\<rangle> ; c"
    by (simp add: calculation data_refine_refl data_refine_seq)
  then show ?thesis
    by (simp add: local_atomic_spec_def)
qed


(* Original lines 770-804. *)
lemma data_refine_spec:
  assumes "I \<inter> p1 \<subseteq> p2"
  assumes "(I \<inter> p1) \<triangleleft> q2 \<triangleright> I \<subseteq> q1"
  shows "\<lbrace>p1\<rbrace> ; \<lparr>q1\<rparr> \<ge>\<^sub>I \<lbrace>p2\<rbrace> ; \<lparr>q2\<rparr>" 
proof -
  have strengthen_post:
    "\<lbrace>I \<inter> p1\<rbrace> ; \<lparr>I \<triangleleft> q1 \<triangleright> I\<rparr> \<ge>
     \<lbrace>I \<inter> p1\<rbrace> ; \<lparr>q2 \<triangleright> I\<rparr>"
  proof (rule spec_strengthen_under_pre)
    show "(I \<inter> p1) \<triangleleft> (q2 \<triangleright> I) \<subseteq> I \<triangleleft> q1 \<triangleright> I"
    proof-
      have "(I \<inter> p1) \<triangleleft> (q2 \<triangleright> I) = I \<triangleleft> ((I \<inter> p1) \<triangleleft> (q2 \<triangleright> I)) \<triangleright> I"
        by (simp add: domain_restrict_twice range_restrict_twice
            restrict_domain_range_assoc)
      then show ?thesis
        using assms(2) restrict_domain_range_assoc restrict_range_domain
        by blast
    qed
  qed

  have "inv I \<iinter> \<lbrace>p1\<rbrace> ; \<lparr>q1\<rparr> = inv I \<iinter> \<lbrace>I \<inter> p1\<rbrace> ; \<lparr>I \<triangleleft> q1 \<triangleright> I\<rparr>"
    using inv_full_spec_equiv by auto
  also have "\<dots> \<ge> inv I \<iinter> \<lbrace>I \<inter> p1\<rbrace> ; \<lparr>q2 \<triangleright> I\<rparr>" (is "_ \<ge> ?rhs")
    by (simp add: seq_conj.sync_mono_right strengthen_post)
  also have "?rhs \<ge> inv I \<iinter> \<lbrace>p2\<rbrace> ; \<lparr>q2 \<triangleright> I\<rparr>" (is "_ \<ge> ?rhs")
    by (simp add: assms(1) seq.assert_to_assert seq_conj.sync_mono_right seq_par.seq_mono_left)
  also have "?rhs = inv I \<iinter> \<lbrace>I \<inter> p2\<rbrace> ; \<lparr>I \<triangleleft> (q2 \<triangleright> I) \<triangleright> I\<rparr>"
    using inv_full_spec_equiv by auto
  also have "\<dots> = inv I \<iinter> \<lbrace>I \<inter> p2\<rbrace> ; \<lparr>I \<triangleleft> q2 \<triangleright> I\<rparr>"
    by (simp add: range_restrict_twice restrict_domain_range_assoc)
  also have "\<dots> = inv I \<iinter> \<lbrace>p2\<rbrace> ; \<lparr>q2\<rparr>"
    using inv_full_spec_equiv by auto
  finally show ?thesis
    by (simp add: data_refine_def) 
qed


(* Original lines 806-810. *)
lemma var_deref_eval_inner_alternate: 
  "(if lv = (Base v) then idle else \<bottom>) ; \<tau>({\<sigma>. get lv \<sigma> = k}) ; idle =
   (if lv = (Base v) then (idle  ; \<tau>({\<sigma>. get lv \<sigma> = k}) ; idle) else \<bottom>)"
  by (simp add: seq.bot_annihilates_left)
(* TODO move to better place *)


(* Original lines 812-845. *)
lemma var_deref_eval_alternate: "\<lblot>Deref (Var v)\<rblot>k = idle ; \<tau>({\<sigma>. get (Base v) \<sigma> = k}) ; idle"
proof-
  have "\<lblot>Deref (Var v)\<rblot>k = (\<Squnion>lv. (if lv = (Base v) then idle else \<bottom>) ; \<tau>({\<sigma>. get lv \<sigma> = k}) ; idle)"
    using expr_cmd_def by simp
  also have "\<dots> = (\<Squnion>lv. (if lv = (Base v) then (idle  ; \<tau>({\<sigma>. get lv \<sigma> = k}) ; idle) else \<bottom>))"
    by (simp add: var_deref_eval_inner_alternate)
  also have "\<dots> =
      idle ; \<tau>({\<sigma>. get (Base v) \<sigma> = k}) ; idle"
  proof (rule antisym)
    show "(\<Squnion>lv.
        if lv = Base v
        then idle ; \<tau>({\<sigma>. get lv \<sigma> = k}) ; idle
        else \<bottom>)
      \<le> idle ; \<tau>({\<sigma>. get (Base v) \<sigma> = k}) ; idle"
      by (simp add: SUP_le_iff)

    have "(if Base v = Base v
           then idle ; \<tau>({\<sigma>. get (Base v) \<sigma> = k}) ; idle
           else \<bottom>)
        \<le> (\<Squnion>lv.
          if lv = Base v
          then idle ; \<tau>({\<sigma>. get lv \<sigma> = k}) ; idle
          else \<bottom>)"
      using Sup_upper rangeI by force

    then show "idle ; \<tau>({\<sigma>. get (Base v) \<sigma> = k}) ; idle
        \<le> (\<Squnion>lv.
          if lv = Base v
          then idle ; \<tau>({\<sigma>. get lv \<sigma> = k}) ; idle
          else \<bottom>)"
      by simp
  qed
  finally show ?thesis .
qed


(* Original lines 847-850. *)
lemma restrict_test_in_variable_refine: 
  "inv I \<iinter> (idle ; \<tau>({\<sigma>. get (Base v) \<sigma> = k}) ; idle) = 
   inv I \<iinter> (idle ; \<tau>(I \<inter> {\<sigma>. get (Base v) \<sigma> = k}) ; idle)"
  using inv_distrib_seq inv_test_alt by auto


(* Original lines 852-870. *)
lemma data_refine_variable:
  assumes "expr_eq (Deref (Var v1)) k1 \<supseteq> I \<inter> expr_eq (Deref (Var v2)) k2"
  shows "\<lblot>Deref (Var v1)\<rblot>k1 \<ge>\<^sub>I \<lblot>Deref (Var v2)\<rblot>k2"
proof-
  have assm_alt: "I \<inter> {\<sigma>. get (Base v1) \<sigma> = k1} \<supseteq> I \<inter> {\<sigma>. get (Base v2) \<sigma> = k2}"
    using assms expr_eq_def by auto

  have lhs: "inv I \<iinter> \<lblot>Deref (Var v1)\<rblot>k1 = inv I \<iinter> (idle ; \<tau>(I \<inter> {\<sigma>. get (Base v1) \<sigma> = k1}) ; idle)"
    using restrict_test_in_variable_refine var_deref_eval_alternate by fastforce

  have rhs: "inv I \<iinter> \<lblot>Deref (Var v2)\<rblot>k2 = inv I \<iinter> (idle ; \<tau>(I \<inter> {\<sigma>. get (Base v2) \<sigma> = k2}) ; idle)"
    using restrict_test_in_variable_refine var_deref_eval_alternate by fastforce

  have rhs_refines_lhs: "inv I \<iinter> (idle ; \<tau>(I \<inter> {\<sigma>. get (Base v1) \<sigma> = k1}) ; idle) \<ge> inv I \<iinter> (idle ; \<tau>(I \<inter> {\<sigma>. get (Base v2) \<sigma> = k2}) ; idle)"
    using assm_alt seq.test_mono seq_conj.sync_mono_right seq_par.seq_mono_left seq_par.seq_mono_right by auto

  then show ?thesis
    using data_refine_def lhs rhs by presburger
qed


(* Original lines 872-908. *)
lemma data_refine_assignment:
  assumes q_tolerates_r: "tolerates_interference p q (-(I \<triangleleft> UNIV) \<union> (UNIV \<triangleright> I))"
  assumes establish_P1: "\<And>lv. {. p .} rely (-(I \<triangleleft> UNIV) \<union> (UNIV \<triangleright> I)) \<iinter> \<ltort>lve\<rtort>lv {. P1 lv .}"
  assumes establish_P2: "\<And>k. {. p .} rely (-(I \<triangleleft> UNIV) \<union> (UNIV \<triangleright> I)) \<iinter> \<lblot>e\<rblot>k {. P2 k .}"
  assumes establish_g_q: "\<And>k lv. (P1 lv \<inter> P2 k) \<triangleleft> update lv k \<subseteq> (-(I \<triangleleft> UNIV) \<union> (UNIV \<triangleright> I)) \<inter> q"
  shows "\<lbrace>p\<rbrace> ; \<lparr>q\<rparr> \<ge>\<^sub>I lve := e"
proof-
  let ?R = "-(I \<triangleleft> UNIV) \<union> (UNIV \<triangleright> I)"

  have refl_R: "refl ?R" by (rule inv_rely_refl)

  have assign_ref:
    "guar\<^sub>\<pi> ?R \<iinter> rely ?R \<iinter> \<lbrace>p\<rbrace> ; \<lparr>q\<rparr> \<ge> lve := e"
  proof (rule rely_guar_assign)
    show "refl ?R" using refl_R .
    show "refl ?R" using refl_R .
    show "tolerates_interference p q ?R"
      using q_tolerates_r by simp
    show "\<And>lv. {. p .} rely ?R \<iinter> \<ltort>lve\<rtort>lv {. P1 lv .}"
      using establish_P1 by simp
    show "\<And>k. {. p .} rely ?R \<iinter> \<lblot>e\<rblot>k {. P2 k .}"
      using establish_P2 by simp
    show "\<And>k lv. (P1 lv \<inter> P2 k) \<triangleleft> update lv k \<subseteq> ?R \<inter> q"
      using establish_g_q by simp
  qed

  have "inv I \<iinter> (\<lbrace>p\<rbrace> ; \<lparr>q\<rparr>) = (inv I \<iinter> inv I) \<iinter> \<lbrace>p\<rbrace> ; \<lparr>q\<rparr>"
    by simp
  also have "\<dots> = (inv I \<iinter> rely (-(I \<triangleleft> UNIV) \<union> (UNIV \<triangleright> I)) \<iinter> guar\<^sub>\<pi> (-(I \<triangleleft> UNIV) \<union> (UNIV \<triangleright> I))) \<iinter> \<lbrace>p\<rbrace> ; \<lparr>q\<rparr>"
    using evolve_def inv_alt_def3 inv_conj_extract_assert seq_conj.sync_assoc by presburger
  also have "\<dots> = inv I \<iinter> (guar\<^sub>\<pi> (-(I \<triangleleft> UNIV) \<union> (UNIV \<triangleright> I)) \<iinter> rely (-(I \<triangleleft> UNIV) \<union> (UNIV \<triangleright> I)) \<iinter> \<lbrace>p\<rbrace> ; \<lparr>q\<rparr>)"
    by (simp add: local.conj.commute local.conj.left_commute)
  also have "\<dots> \<ge> inv I \<iinter> (lve := e)"
    by (simp add: assign_ref seq_conj.sync_mono_right)
  then show ?thesis
    by (simp add: calculation data_refine_def) 
qed
