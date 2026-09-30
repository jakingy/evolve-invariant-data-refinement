(* Extracts from isabelle/new_rg_algebra/Rely_Guarantee/Atomic_Specification.thy. *)
(* These are source excerpts, not a standalone buildable theory. *)

(* Original lines 23-27. *)
text \<open>In the context of the precondition \<open>p\<close> the postcondition \<open>q\<close>
may have its domain constrained to \<open>p\<close>.\<close>
lemma atomic_spec_pre_internalise:
  shows "\<langle>p,q\<rangle> = \<langle>p,p \<triangleleft> q\<rangle>"
 unfolding atomic_spec_def using opt_assert_internalise seq.seq_assoc by simp 


(* Original lines 66-78. *)
lemma atomic_guar: 
  assumes refl: "refl g"
  shows "guar\<^sub>\<pi> g \<iinter> \<langle>p, q\<rangle> = \<langle>p, g \<inter> q\<rangle>"
proof -
  have "guar\<^sub>\<pi> g \<iinter> \<langle>p, q\<rangle> = guar\<^sub>\<pi> g \<iinter> (idle ; \<lbrace>p\<rbrace> ; opt q ; idle)"
    by (simp add: atomic_spec_def)
  also have "\<dots> = (guar\<^sub>\<pi> g \<iinter> idle) ; (guar\<^sub>\<pi> g \<iinter> \<lbrace>p\<rbrace>) ; (guar\<^sub>\<pi> g \<iinter> opt q) ; (guar\<^sub>\<pi> g \<iinter> idle)"
    by (simp add: pgm_guar_conj_seq)
  also have "\<dots> = idle ; \<lbrace>p\<rbrace> ; opt(g \<inter> q) ; idle"
    using guar_opt guar_idle refl local.conj.commute pgm_guar_conj_assert by force
  finally show ?thesis
    by (simp add: atomic_spec_def) 
qed


(* Original lines 80-81. *)
lemma atomic_frame: "v:\<^sub>s\<langle>p, q\<rangle> = \<langle>p, id_bar v \<inter> q\<rangle>"
  by (simp add: atomic_guar id_bar_refl var_frame_set_def)


(* Original lines 83-86. *)
lemma atomic_add_frame:
  assumes "q \<subseteq> id_bar v"
  shows "v:\<^sub>s\<langle>p, q\<rangle> = \<langle>p, q\<rangle>"
  by (metis atomic_frame assms inf.absorb_iff2)


(* Original lines 136-141. *)
text \<open>When introducing a local variable to an atomic, the finite stuttering steps
are relaxed to allow program steps that modify the new local variables.\<close>
definition local_atomic_spec :: "'state set \<Rightarrow> 'state rel \<Rightarrow> ('v LValue) fset \<Rightarrow> 'a" ("\<langle>_,_,_\<rangle>" [30,30])
  where "local_atomic_spec p q vars \<equiv> vars:\<^sub>sterminate ; \<langle>p, q\<rangle> ; vars:\<^sub>sterminate"

(*TODO move these elsewhere, maybe split out into Local_Atomic.thy and Framed_Terminate.thy*)


(* Original lines 142-148. *)
lemma local_term_ref_idle: "vars:\<^sub>sterminate \<ge> idle"
proof -
  have "guar\<^sub>\<pi> (id_bar vars) \<ge> guar\<^sub>\<pi> Id"
    using id_bar_ge_Id by (rule pgm_guar_strengthen)
  then show ?thesis
    by (simp add: var_frame_set_def idle_def seq_conj.sync_mono_left)
qed


(* Original lines 150-159. *)
lemma local_term_seq_idem:
  "vars:\<^sub>sterminate ; vars:\<^sub>sterminate = vars:\<^sub>sterminate"
proof -
  have "(guar\<^sub>\<pi> (id_bar vars) \<iinter> terminate) ;
        (guar\<^sub>\<pi> (id_bar vars) \<iinter> terminate) =
        guar\<^sub>\<pi> (id_bar vars) \<iinter> terminate"
    by (metis pgm_guar_conj_seq seq_terminate_terminate)
  then show ?thesis
    by (simp add: var_frame_set_def)
qed


(* Original lines 161-168. *)
lemma local_term_seq_idle: "vars:\<^sub>sterminate ; idle = vars:\<^sub>sterminate"
proof (rule antisym)
  show "vars:\<^sub>sterminate ; idle \<le> vars:\<^sub>sterminate"
    using local_term_ref_idle local_term_seq_idem
    by (metis seq.seq_mono_right)
  show "vars:\<^sub>sterminate ; idle \<ge> vars:\<^sub>sterminate"
    using idle_ref_nil seq_par.seq_mono_right by fastforce
qed


(* Original lines 170-177. *)
lemma idle_seq_local_term: "idle ; vars:\<^sub>sterminate = vars:\<^sub>sterminate"
proof (rule antisym)
  show "idle ; vars:\<^sub>sterminate \<le> vars:\<^sub>sterminate"
    using local_term_ref_idle local_term_seq_idem
    by (metis seq.seq_mono_left)
  show "idle ; vars:\<^sub>sterminate \<ge> vars:\<^sub>sterminate"
    using idle_ref_nil seq_par.seq_mono by fastforce
qed


(* Original lines 179-187. *)
lemma local_atomic_spec_expand:
  "local_atomic_spec p q vars =
    vars:\<^sub>sterminate ; \<lbrace>p\<rbrace> ; opt q ; vars:\<^sub>sterminate"
proof -
  have "local_atomic_spec p q vars = vars:\<^sub>sterminate ; idle ; \<lbrace>p\<rbrace> ; opt q ; idle ; vars:\<^sub>sterminate"
    by (simp add: atomic_spec_def local_atomic_spec_def seq_par.seq_assoc)
  then show ?thesis
    by (simp add: idle_seq_local_term local_term_seq_idle seq_par.seq_assoc)
qed


(* Original lines 189-194. *)
lemma atomic_ref_local_atomic: "\<langle>p,q,v\<rangle> \<ge> \<langle>p,q\<rangle>"
proof-
  have "v:\<^sub>sterminate \<ge> idle"
    by (simp add: local_term_ref_idle)
  then show ?thesis using local_atomic_spec_expand atomic_spec_def seq_par.seq_mono by force
qed


(* Original lines 196-204. *)
lemma local_atomic_extract_framed_term_left: "\<langle>p,q,v\<rangle> =  v:\<^sub>sterminate ; \<langle>p,q,v\<rangle>"
proof-
  have "\<langle>p,q,v\<rangle> = v:\<^sub>sterminate ; v:\<^sub>sterminate ; \<langle>p,q\<rangle> ; v:\<^sub>sterminate"
    by (simp add: local_atomic_spec_def local_term_seq_idem)
  also have "\<dots> = v:\<^sub>sterminate ; (v:\<^sub>sterminate ; \<langle>p,q\<rangle> ; v:\<^sub>sterminate)"
    by (simp add: seq_par.seq_assoc)
  finally show ?thesis
    by (simp add: local_atomic_spec_def)  
qed


(* Original lines 206-207. *)
lemma local_atomic_extract_framed_term_right: "\<langle>p,q,v\<rangle> = \<langle>p,q,v\<rangle> ; v:\<^sub>sterminate"
  by (simp add: local_atomic_spec_def local_term_seq_idem seq_par.seq_assoc)


(* Original lines 209-212. *)
lemma local_atomic_ref:
  assumes "\<langle>p1,q1\<rangle> \<ge> \<langle>p2,q2\<rangle>"
  shows "\<langle>p1,q1,v\<rangle> \<ge> \<langle>p2,q2,v\<rangle>"
  by (simp add: assms local_atomic_spec_def seq_par.seq_mono_left seq_par.seq_mono_right)


(* Original lines 214-218. *)
lemma local_atomic_ref_var: 
  assumes "v1 \<ge> v2"
  assumes "\<langle>p1,q1\<rangle> \<ge> \<langle>p2,q2\<rangle>"
  shows "\<langle>p1,q1,v1\<rangle> \<ge> \<langle>p2,q2,v2\<rangle>"
  by (simp add: assms(1,2) id_bar_narrow local_atomic_spec_def pgm_guar_strengthen seq_conj.sync_mono_left seq_par.seq_mono var_frame_set_def)


(* Original lines 220-222. *)
lemma opt_terminates: "opt q \<le> terminate"
 using opt_def pgm_terminates test_terminates sup_mono_right sup_mono_left
          Lattices.semilattice_sup_class.sup.idem by force


(* Original lines 224-226. *)
lemma atomic_post_terminates: "\<langle>\<top>,q\<rangle> \<le> terminate"
  using opt_terminates terminate_seq terminate_ref_idle atomic_spec_def
  by (simp add: seq.assert_neut)


(* Original lines 228-229. *)
lemma framed_terminate_ref_framed_atomic: "vars:\<^sub>sterminate \<ge> vars:\<^sub>s\<langle>\<top>,q\<rangle>"
  by (simp add: atomic_post_terminates seq_conj.sync_mono_right var_frame_set_def)


(* Original lines 231-242. *)
lemma framed_local_atomic_restrict_local_frame:
  "vars:\<^sub>s\<langle>p,q1,vars_local\<rangle> = vars:\<^sub>s\<langle>p,q1,vars |\<inter>| vars_local\<rangle>"
proof -
  have frame_inter_subset: "(vars |\<inter>| vars_local) |\<subseteq>| vars"
    by auto
  have frame_inter_idem:
    "vars |\<inter>| (vars |\<inter>| vars_local) = vars |\<inter>| vars_local"
    by (simp add: frame_inter_subset finter_absorb1)
  show ?thesis
    unfolding local_atomic_spec_def
    by (simp add: var_frame_set_seq var_frame_set_merge frame_inter_idem)
qed


(* Original lines 244-257. *)
lemma framed_local_atomic_extract_framed_term_left:
  "vars:\<^sub>s\<langle>p,q,vars_local\<rangle> = (vars_local |\<inter>| vars):\<^sub>sterminate ; vars:\<^sub>s\<langle>p,q,vars_local\<rangle>"
proof -
  have local_extract:
    "\<langle>p,q,vars_local\<rangle> = vars_local:\<^sub>sterminate ; \<langle>p,q,vars_local\<rangle>"
    by (rule local_atomic_extract_framed_term_left)
  have "vars:\<^sub>s\<langle>p,q,vars_local\<rangle> = vars:\<^sub>s(vars_local:\<^sub>sterminate ; \<langle>p,q,vars_local\<rangle>)"
    by (rule arg_cong[OF local_extract])
  also have "\<dots> = vars:\<^sub>s(vars_local:\<^sub>sterminate) ; vars:\<^sub>s\<langle>p,q,vars_local\<rangle>"
    by (simp add: var_frame_set_seq)
  also have "\<dots> = (vars_local |\<inter>| vars):\<^sub>sterminate ; vars:\<^sub>s\<langle>p,q,vars_local\<rangle>"
    by (simp add: var_frame_set_merge finter_commute)
  finally show ?thesis .
qed


(* Original lines 259-272. *)
lemma framed_local_atomic_extract_framed_term_right:
  "vars:\<^sub>s\<langle>p,q,vars_local\<rangle> = vars:\<^sub>s\<langle>p,q,vars_local\<rangle> ; (vars_local |\<inter>| vars):\<^sub>sterminate"
proof -
  have local_extract:
    "\<langle>p,q,vars_local\<rangle> = \<langle>p,q,vars_local\<rangle> ; vars_local:\<^sub>sterminate"
    by (rule local_atomic_extract_framed_term_right)
  have "vars:\<^sub>s\<langle>p,q,vars_local\<rangle> = vars:\<^sub>s(\<langle>p,q,vars_local\<rangle> ; vars_local:\<^sub>sterminate)"
    by (rule arg_cong[OF local_extract])
  also have "\<dots> = vars:\<^sub>s\<langle>p,q,vars_local\<rangle> ; vars:\<^sub>s(vars_local:\<^sub>sterminate)"
    by (simp add: var_frame_set_seq)
  also have "\<dots> = vars:\<^sub>s\<langle>p,q,vars_local\<rangle> ; (vars_local |\<inter>| vars):\<^sub>sterminate"
    by (simp add: var_frame_set_merge finter_commute)
  finally show ?thesis .
qed


(* Original lines 274-282. *)
lemma framed_local_atomic_extract_framed_term_left_var_subset:
  assumes "vars_local |\<subseteq>| vars"
  shows "vars:\<^sub>s\<langle>p,q,vars_local\<rangle> = vars_local:\<^sub>sterminate ; vars:\<^sub>s\<langle>p,q,vars_local\<rangle>"
proof -
  have local_inter: "vars_local |\<inter>| vars = vars_local"
    using assms finter_absorb1 by auto
  then show ?thesis
    using framed_local_atomic_extract_framed_term_left by metis
qed


(* Original lines 284-292. *)
lemma framed_local_atomic_extract_framed_term_right_var_subset:
  assumes "vars_local |\<subseteq>| vars"
  shows "vars:\<^sub>s\<langle>p,q,vars_local\<rangle> = vars:\<^sub>s\<langle>p,q,vars_local\<rangle> ; vars_local:\<^sub>sterminate"
proof -
  have local_inter: "vars_local |\<inter>| vars = vars_local"
    using assms finter_absorb1 by auto
  then show ?thesis
    using framed_local_atomic_extract_framed_term_right by metis
qed


(* Original lines 294-303. *)
lemma local_atomic_extract_framed_atomic_left: "\<langle>p,q1,vars_local\<rangle> \<ge> vars_local:\<^sub>s\<langle>\<top>,q2\<rangle> ; \<langle>p,q1\<rangle>"
proof -
  have "\<langle>p,q1,vars_local\<rangle> = vars_local:\<^sub>sterminate ; \<langle>p,q1,vars_local\<rangle>"
    by (rule local_atomic_extract_framed_term_left)
  also have "\<dots> \<ge> vars_local:\<^sub>s\<langle>\<top>,q2\<rangle> ; \<langle>p,q1,vars_local\<rangle>" (is "_ \<ge> ?rhs")
    by (rule seq_par.seq_mono_left, rule framed_terminate_ref_framed_atomic)
  also have "?rhs \<ge> vars_local:\<^sub>s\<langle>\<top>,q2\<rangle> ; \<langle>p,q1\<rangle>"
    by (rule seq_par.seq_mono_right, rule atomic_ref_local_atomic)
  finally show ?thesis .
qed


(* Original lines 305-314. *)
lemma local_atomic_extract_framed_atomic_right: "\<langle>p,q1,vars_local\<rangle> \<ge> \<langle>p,q1\<rangle> ; vars_local:\<^sub>s\<langle>\<top>,q2\<rangle>"
proof -
  have "\<langle>p,q1,vars_local\<rangle> = \<langle>p,q1,vars_local\<rangle> ; vars_local:\<^sub>sterminate"
    by (rule local_atomic_extract_framed_term_right)
  also have "\<dots> \<ge> \<langle>p,q1,vars_local\<rangle> ; vars_local:\<^sub>s\<langle>\<top>,q2\<rangle>" (is "_ \<ge> ?rhs")
    by (rule seq_par.seq_mono_right, rule framed_terminate_ref_framed_atomic)
  also have "?rhs \<ge> \<langle>p,q1\<rangle> ; vars_local:\<^sub>s\<langle>\<top>,q2\<rangle>"
    by (rule seq_par.seq_mono_left, rule atomic_ref_local_atomic)
  finally show ?thesis .
qed


(* Original lines 316-325. *)
lemma framed_local_atomic_extract_framed_atomic_left_var_subset:
  assumes "vars_local |\<subseteq>| vars"
  shows "vars:\<^sub>s\<langle>p,q,vars_local\<rangle> \<ge> vars_local:\<^sub>s\<langle>\<top>,q2\<rangle> ; vars:\<^sub>s\<langle>p,q,vars_local\<rangle>"
proof -
  have "vars:\<^sub>s\<langle>p,q,vars_local\<rangle> = vars_local:\<^sub>sterminate ; vars:\<^sub>s\<langle>p,q,vars_local\<rangle>"
    using assms by (rule framed_local_atomic_extract_framed_term_left_var_subset)
  also have "\<dots> \<ge> vars_local:\<^sub>s\<langle>\<top>,q2\<rangle> ; vars:\<^sub>s\<langle>p,q,vars_local\<rangle>"
    by (rule seq_par.seq_mono_left, rule framed_terminate_ref_framed_atomic)
  finally show ?thesis .
qed


(* Original lines 327-336. *)
lemma framed_local_atomic_extract_framed_atomic_right_var_subset:
  assumes "vars_local |\<subseteq>| vars"
  shows "vars:\<^sub>s\<langle>p,q,vars_local\<rangle> \<ge> vars:\<^sub>s\<langle>p,q,vars_local\<rangle> ; vars_local:\<^sub>s\<langle>\<top>,q2\<rangle>"
proof -
  have "vars:\<^sub>s\<langle>p,q,vars_local\<rangle> = vars:\<^sub>s\<langle>p,q,vars_local\<rangle> ; vars_local:\<^sub>sterminate"
    using assms by (rule framed_local_atomic_extract_framed_term_right_var_subset)
  also have "\<dots> \<ge> vars:\<^sub>s\<langle>p,q,vars_local\<rangle> ; vars_local:\<^sub>s\<langle>\<top>,q2\<rangle>"
    by (rule seq_par.seq_mono_right, rule framed_terminate_ref_framed_atomic)
  finally show ?thesis .
qed


(* Original lines 338-353. *)
lemma framed_local_atomic_extract_framed_atomic_left_var_subset_once:
  assumes "vars_local |\<subseteq>| vars"
  shows "vars:\<^sub>s\<langle>p,q,vars_local\<rangle> \<ge> vars_local:\<^sub>s\<langle>\<top>,q2\<rangle> ; vars:\<^sub>s\<langle>p,q\<rangle>"
proof -
  have framed_local_ref_atomic:
    "vars:\<^sub>s\<langle>p,q,vars_local\<rangle> \<ge> vars:\<^sub>s\<langle>p,q\<rangle>"
    unfolding var_frame_set_def
    by (rule seq_conj.sync_mono_right, rule atomic_ref_local_atomic)
  have "vars:\<^sub>s\<langle>p,q,vars_local\<rangle> = vars_local:\<^sub>sterminate ; vars:\<^sub>s\<langle>p,q,vars_local\<rangle>"
    using assms by (rule framed_local_atomic_extract_framed_term_left_var_subset)
  also have "\<dots> \<ge> vars_local:\<^sub>sterminate ; vars:\<^sub>s\<langle>p,q\<rangle>" (is "_ \<ge> ?rhs")
    by (rule seq_par.seq_mono_right, rule framed_local_ref_atomic)
  also have "?rhs \<ge> vars_local:\<^sub>s\<langle>\<top>,q2\<rangle> ; vars:\<^sub>s\<langle>p,q\<rangle>"
    by (rule seq_par.seq_mono_left, rule framed_terminate_ref_framed_atomic)
  finally show ?thesis .
qed


(* Original lines 355-371. *)
lemma framed_local_atomic_extract_framed_atomic_right_var_subset_once:
  assumes "vars_local |\<subseteq>| vars"
  shows "vars:\<^sub>s\<langle>p,q,vars_local\<rangle> \<ge> vars:\<^sub>s\<langle>p,q\<rangle> ; vars_local:\<^sub>s\<langle>\<top>,q2\<rangle>"
proof -
  have framed_local_ref_atomic:
    "vars:\<^sub>s\<langle>p,q,vars_local\<rangle> \<ge> vars:\<^sub>s\<langle>p,q\<rangle>"
    unfolding var_frame_set_def
    by (rule seq_conj.sync_mono_right, rule atomic_ref_local_atomic)
  have "vars:\<^sub>s\<langle>p,q,vars_local\<rangle> =
      vars:\<^sub>s\<langle>p,q,vars_local\<rangle> ; vars_local:\<^sub>sterminate"
    using assms by (rule framed_local_atomic_extract_framed_term_right_var_subset)
  also have "\<dots> \<ge> vars:\<^sub>s\<langle>p,q\<rangle> ; vars_local:\<^sub>sterminate" (is "_ \<ge> ?rhs")
    by (rule seq_par.seq_mono_left, rule framed_local_ref_atomic)
  also have "?rhs \<ge> vars:\<^sub>s\<langle>p,q\<rangle> ; vars_local:\<^sub>s\<langle>\<top>,q2\<rangle>"
    by (rule seq_par.seq_mono_right, rule framed_terminate_ref_framed_atomic)
  finally show ?thesis .
qed


(* Original lines 373-382. *)
text \<open>A framed terminating command can be refined to an atomic step only modifying vars in the frame.\<close>
lemma framed_terminate_ref_atomic:
  "vars:\<^sub>sterminate \<ge> \<langle>UNIV, id_bar vars\<rangle>"
proof -
  have "vars:\<^sub>sterminate \<ge> vars:\<^sub>s\<langle>\<top>, id_bar vars\<rangle>" (is "_ \<ge> ?rhs")
    by (simp add: framed_terminate_ref_framed_atomic)
  also have "?rhs = \<langle>UNIV, id_bar vars\<rangle>"
      using atomic_frame by auto
  finally show ?thesis .
qed


(* Original lines 384-387. *)
text \<open>A framed terminating command can also be refined to a framed specification.\<close>
lemma framed_terminate_ref_framed_spec:
  "vars:\<^sub>sterminate \<ge> vars:\<^sub>s\<lparr>q\<rparr>"
  by (simp add: spec_term seq_conj.sync_mono_right var_frame_set_def)


(* Original lines 389-390. *)
lemma framed_terminate_ref_local_atomic: "vars:\<^sub>sterminate \<ge> \<langle>UNIV, id_bar vars, vars\<rangle>"
  by (simp add: framed_terminate_ref_atomic local_atomic_spec_def local_term_seq_idem seq.op_idem_mono) 


(* Original lines 392-401. *)
lemma local_atomic_extract_framed_spec_left:
  "\<langle>p,q,vars\<rangle> \<ge> vars:\<^sub>s\<lparr>q0\<rparr> ; \<langle>p,q,vars\<rangle>"
proof -
  have "\<langle>p,q,vars\<rangle> = vars:\<^sub>sterminate ; \<langle>p,q,vars\<rangle>"
    by (rule local_atomic_extract_framed_term_left)
  also have "\<dots> \<ge> vars:\<^sub>s\<lparr>q0\<rparr> ; \<langle>p,q,vars\<rangle>"
    apply (rule seq_par.seq_mono_left)
    by (rule framed_terminate_ref_framed_spec)
  finally show ?thesis .
qed


(* Original lines 403-411. *)
lemma local_atomic_extract_local_atomic_left: "\<langle>p,q,v\<rangle> \<ge> \<langle>UNIV,id_bar v,v\<rangle> ; \<langle>p,q,v\<rangle>"
proof-
  have "\<langle>p,q,v\<rangle> = v:\<^sub>sterminate ; \<langle>p,q,v\<rangle>"
    using local_atomic_extract_framed_term_left by auto
  also have "\<dots> \<ge> \<langle>UNIV,id_bar v,v\<rangle> ; \<langle>p,q,v\<rangle>"
    apply (rule seq_par.seq_mono_left)
    by (simp add: framed_terminate_ref_local_atomic)
  finally show ?thesis .
qed


(* Original lines 413-421. *)
lemma local_atomic_extract_local_atomic_right: "\<langle>p,q,v\<rangle> \<ge> \<langle>p,q,v\<rangle> ; \<langle>UNIV,id_bar v,v\<rangle>"
proof-
  have "\<langle>p,q,v\<rangle> = \<langle>p,q,v\<rangle> ;  v:\<^sub>sterminate"
    using local_atomic_extract_framed_term_right by auto
  also have "\<dots> \<ge> \<langle>p,q,v\<rangle> ; \<langle>UNIV,id_bar v,v\<rangle> "
    apply (rule seq_par.seq_mono_right)
    by (simp add: framed_terminate_ref_local_atomic)
  finally show ?thesis .
qed


(* Original lines 423-444. *)
lemma idle_bring_right_assert_left: "\<lbrace>p\<rbrace> ; idle ; \<lbrace>p\<rbrace> = idle ; \<lbrace>p\<rbrace>"
proof(rule seq.assert_case_eq[where p="p"])
  show "\<lbrace>p\<rbrace> ; (\<lbrace>p\<rbrace> ; idle ; \<lbrace>p\<rbrace>) = \<lbrace>p\<rbrace> ; (idle ; \<lbrace>p\<rbrace>)"
    using seq_par.seq_assoc seq.assert_op_assert_idem by metis
  show "\<lbrace>-p\<rbrace> ; (\<lbrace>p\<rbrace> ; idle ; \<lbrace>p\<rbrace>) = \<lbrace>-p\<rbrace> ; (idle ; \<lbrace>p\<rbrace>)"
  proof-
    have "\<lbrace>-p\<rbrace> ; (\<lbrace>p\<rbrace> ; idle ; \<lbrace>p\<rbrace>) = \<top>"
      by (metis seq.assert_op_commute seq.assert_seq_assert_not seq_par.seq_assoc seq_par.top_seq)
    also have "\<dots> = \<lbrace>-p\<rbrace> ; (idle ; \<lbrace>p\<rbrace>)"
    proof-
      have "idle = nil \<squnion> idle"
        by (metis idle_ref_nil sup.absorb_iff2)
      then have "\<lbrace>-p\<rbrace> ; (idle ; \<lbrace>p\<rbrace>) = \<lbrace>-p\<rbrace> ; (nil ; \<lbrace>p\<rbrace> \<squnion> idle ; \<lbrace>p\<rbrace>)"
        by (metis seq_par.sup_seq)
      also have "\<dots> = (\<lbrace>-p\<rbrace> ; nil ; \<lbrace>p\<rbrace>) \<squnion> (\<lbrace>-p\<rbrace> ; idle ; \<lbrace>p\<rbrace>)"
        by (simp add: seq_par.seq_assoc seq_par.seq_sup)
      finally show ?thesis
        by (simp add: seq.assert_op_commute seq.assert_seq_assert_not) 
    qed
    finally show ?thesis .
  qed
qed


(* Original lines 446-447. *)
lemma atomic_extract_pre_left: "\<lbrace>p\<rbrace> ; \<langle>p,q\<rangle> = \<langle>p,q\<rangle>"
  by (metis atomic_spec_def idle_bring_right_assert_left seq_par.seq_assoc)


(* Original lines 449-459. *)
lemma assert_atomic_spec_into_pre:
  assumes stable_a: "stable a r"
  shows "rely r \<iinter> (\<lbrace>a\<rbrace> ; \<langle>p,q\<rangle>) = rely r \<iinter> (\<lbrace>a\<rbrace> ; \<langle>a \<inter> p, q\<rangle>)"
proof-
  have "rely r \<iinter> (\<lbrace>a\<rbrace> ; \<langle>p,q\<rangle>) = rely r \<iinter> (rely r \<iinter> (\<lbrace>a\<rbrace> ; idle) ; \<lbrace>p\<rbrace> ; opt q; idle)"
    by (simp add: atomic_spec_def seq_par.seq_assoc)
  also have "\<dots> = rely r \<iinter> (\<lbrace>a\<rbrace> ; idle ; \<lbrace>a\<rbrace> ; \<lbrace>p\<rbrace> ; opt q; idle)"
    using rely_conj_seq rely_idle_stable_assert_eq stable_a by fastforce
  then show ?thesis
    by (simp add: atomic_spec_def seq.assert_op_assert seq_par.seq_assoc)
qed


(* Original lines 461-485. *)
lemma atomic_spec_extract_post_test:
  assumes q_establishes_a: "p \<triangleleft> q \<subseteq> UNIV \<triangleright> a"
  assumes stable_a: "stable a r"
  shows "rely r \<iinter> \<langle>p,q\<rangle> = rely r \<iinter> (\<langle>p,q\<rangle> ; \<tau> a)"
proof-
  have intro_a: "opt (p \<triangleleft> q) = opt (p \<triangleleft> q) ; \<tau> a"
    by (simp add: opt_extract_test q_establishes_a)

  have "rely r \<iinter> \<langle>p,q\<rangle> = rely r \<iinter> (idle ; \<lbrace>p\<rbrace> ; opt q ; (rely r \<iinter> idle))"
    by (simp add: atomic_spec_def rely_conj_seq)
  also have "\<dots> = rely r \<iinter> (idle ; \<lbrace>p\<rbrace> ; opt (p \<triangleleft> q) ; (rely r \<iinter> idle))"
    using opt_assert_internalise seq_par.seq_assoc by auto
  also have "\<dots> = rely r \<iinter> (idle ; \<lbrace>p\<rbrace> ; opt (p \<triangleleft> q) ; \<tau> a ; (rely r \<iinter> idle))"
    using intro_a seq_par.seq_assoc by auto
  also have "\<dots> = rely r \<iinter> (idle ; \<lbrace>p\<rbrace> ; opt (p \<triangleleft> q) ; \<tau> a ; (rely r \<iinter> idle) ; \<tau> a)"
    using rely_conj_seq seq_par.seq_assoc stable_a stable_test by fastforce
  also have "\<dots> = rely r \<iinter> (idle ; \<lbrace>p\<rbrace> ; opt (p \<triangleleft> q) ; (rely r \<iinter> idle) ; \<tau> a)"
    using intro_a seq_par.seq_assoc by auto
  also have "\<dots> = rely r \<iinter> (idle ; \<lbrace>p\<rbrace> ; opt q ; (rely r \<iinter> idle) ; \<tau> a)"
    using opt_assert_internalise seq_par.seq_assoc by auto
  also have "\<dots> = rely r \<iinter> (idle ; \<lbrace>p\<rbrace> ; opt q ; idle ; \<tau> a)"
    by (simp add: rely_conj_seq)
  finally show ?thesis 
    by (simp add: atomic_spec_def)
qed


(* Original lines 487-513. *)
text \<open>A postcondition established by an optional atomic step can be retained after
the following idle segment, provided it is stable under the rely.\<close>
lemma rely_assert_opt_idle_extract_post_assert:
  assumes q_establishes_a: "p \<triangleleft> q \<subseteq> UNIV \<triangleright> a"
  assumes stable_a: "stable a r"
  shows "rely r \<iinter> (\<lbrace>p\<rbrace> ; opt q ; idle) = rely r \<iinter> (\<lbrace>p\<rbrace> ; opt q ; idle ; \<lbrace>a\<rbrace>)"
proof -
  have opt_post: "\<lbrace>p\<rbrace> ; opt q = \<lbrace>p\<rbrace> ; opt q ; \<lbrace>a\<rbrace>"
  proof -
    have "\<lbrace>p\<rbrace> ; opt q = \<lbrace>p\<rbrace> ; opt (p \<triangleleft> q)"
      by (rule opt_assert_internalise)
    also have "\<dots> = \<lbrace>p\<rbrace> ; opt (p \<triangleleft> q) ; \<lbrace>a\<rbrace>"
      using opt_extract_assert q_establishes_a seq_par.seq_assoc by auto
    also have "\<dots> = \<lbrace>p\<rbrace> ; opt q ; \<lbrace>a\<rbrace>"
      by (simp add: \<open>\<lbrace>p\<rbrace> ; opt q = \<lbrace>p\<rbrace> ; opt (p \<triangleleft> q)\<close>)
    finally show ?thesis .
  qed

  have "rely r \<iinter> (\<lbrace>p\<rbrace> ; opt q ; idle) = rely r \<iinter> (\<lbrace>p\<rbrace> ; opt q ; \<lbrace>a\<rbrace> ; idle)"
    using opt_post by auto
  also have "\<dots> = rely r \<iinter> (\<lbrace>p\<rbrace> ; opt q ; \<lbrace>a\<rbrace> ; idle ; \<lbrace>a\<rbrace>)"
    using rely_idle_stable_assert_eq[OF stable_a]
      by (simp add: rely_conj_seq seq_par.seq_assoc)
  also have "\<dots> = rely r \<iinter> (\<lbrace>p\<rbrace> ; opt q ; idle ; \<lbrace>a\<rbrace>)"
    using opt_post by auto
  finally show ?thesis .
qed


(* Original lines 515-530. *)
lemma atomic_spec_extract_post_assert:
  assumes q_establishes_a: "p \<triangleleft> q \<subseteq> UNIV \<triangleright> a"
  assumes stable_a: "stable a r"
  shows "rely r \<iinter> \<langle>p,q\<rangle> = rely r \<iinter> (\<langle>p,q\<rangle> ; \<lbrace>a\<rbrace>)"
proof -
  have "rely r \<iinter> \<langle>p,q\<rangle> =
      rely r \<iinter> (idle ; (\<lbrace>p\<rbrace> ; opt q ; idle))"
    by (simp add: atomic_spec_def rely_conj_seq seq_par.seq_assoc)
  also have "\<dots> = rely r \<iinter>
      (idle ; (\<lbrace>p\<rbrace> ; opt q ; idle ; \<lbrace>a\<rbrace>))"
    using rely_assert_opt_idle_extract_post_assert[OF q_establishes_a stable_a]
      by (simp add: rely_conj_seq seq_par.seq_assoc)
  also have "\<dots> = rely r \<iinter> (\<langle>p,q\<rangle> ; \<lbrace>a\<rbrace>)"
    by (simp add: atomic_spec_def rely_conj_seq seq_par.seq_assoc)
  finally show ?thesis .
qed


(* Original lines 532-552. *)
lemma framed_atomic_spec_extract_post_assert:
  assumes q_establishes_a: "p \<triangleleft> q \<subseteq> UNIV \<triangleright> a"
  assumes stable_a: "stable a r"
  shows "rely r \<iinter> vars:\<^sub>s\<langle>p,q\<rangle> =
    rely r \<iinter> (vars:\<^sub>s\<langle>p,q\<rangle> ; \<lbrace>a\<rbrace>)"
proof -
  have rely_assert: "rely r \<iinter> \<lbrace>a\<rbrace> = \<lbrace>a\<rbrace>"
    by (metis local.conj.commute rely_conj_assert)
  have "rely r \<iinter> vars:\<^sub>s\<langle>p,q\<rangle> =
      vars:\<^sub>s(rely r \<iinter> \<langle>p,q\<rangle>)"
    by (rule rely_conj_var_frame_set)
  also have "\<dots> = vars:\<^sub>s(rely r \<iinter> \<langle>p,q\<rangle> ; \<lbrace>a\<rbrace>)"
    by (rule arg_cong[OF atomic_spec_extract_post_assert[OF q_establishes_a stable_a]])
  also have "\<dots> = vars:\<^sub>s(rely r \<iinter> \<langle>p,q\<rangle>) ; \<lbrace>a\<rbrace>"
    by (simp add: rely_assert rely_conj_seq var_frame_set_extract_assert_right)
  also have "\<dots> = (rely r \<iinter> vars:\<^sub>s\<langle>p,q\<rangle>) ; \<lbrace>a\<rbrace>"
    by (simp add: rely_conj_var_frame_set)
  also have "\<dots> = rely r \<iinter> (vars:\<^sub>s\<langle>p,q\<rangle> ; \<lbrace>a\<rbrace>)"
    by (simp add: rely_conj_seq rely_assert)
  finally show ?thesis .
qed


(* Original lines 554-567. *)
lemma atomic_spec_stable_conditions:
  assumes q_establishes_a: "(a \<inter> p) \<triangleleft> q \<subseteq> UNIV \<triangleright> a"
  assumes stable_a: "stable a r"
  shows "rely r \<iinter> (\<lbrace>a\<rbrace> ; \<langle>p,q\<rangle>) = rely r \<iinter> (\<lbrace>a\<rbrace> ; \<langle>p,q\<rangle> ; \<lbrace>a\<rbrace>)"
proof-
  have a:"rely r \<iinter> (\<lbrace>a\<rbrace> ; \<langle>p,q\<rangle>) = rely r \<iinter> (\<lbrace>a\<rbrace> ; \<langle>a \<inter> p,q\<rangle>)"
    by (meson assert_atomic_spec_into_pre stable_a)
  also have "\<dots> = rely r \<iinter> (\<lbrace>a\<rbrace> ; \<langle>a \<inter> p,(a \<inter> p)\<triangleleft>q\<rangle>)"
    using atomic_spec_pre_internalise by auto
  also have "\<dots> = rely r \<iinter> (\<lbrace>a\<rbrace> ; \<langle>a \<inter> p,q\<rangle> ; \<lbrace>a\<rbrace>)"
    using atomic_spec_extract_post_assert atomic_spec_pre_internalise q_establishes_a seq_conj.assert_op_sync_right seq_par.seq_assoc stable_a by force
  finally show ?thesis
    using a rely_conj_seq by auto 
qed
