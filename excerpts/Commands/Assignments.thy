(* Extracts from isabelle/new_rg_algebra/Commands/Assignments.thy. *)
(* These are source excerpts, not a standalone buildable theory. *)

(* Original lines 24-33. *)
text\<open>Assign is equivalent to an atomic with no precondition and post condition that is the update.\<close>
lemma atomic_equiv: "(\<Squnion>lv k. (\<ltort>lve\<rtort>lv \<parallel> \<lblot>e\<rblot>k) ; opt(g lv k) ; idle) =
                     (\<Squnion>lv k. (\<ltort>lve\<rtort>lv \<parallel> \<lblot>e\<rblot>k) ; \<langle>\<top>,g lv k\<rangle>)"
proof -
  have branch_equiv:
    "\<And>lv k. (\<ltort>lve\<rtort>lv \<parallel> \<lblot>e\<rblot>k) ; opt (g lv k) ; idle = (\<ltort>lve\<rtort>lv \<parallel> \<lblot>e\<rblot>k) ; \<langle>\<top>, g lv k\<rangle>"
    unfolding atomic_spec_def
    using eval_pair_seq_idle seq_par.seq_assoc by (metis local.seq.seq_nil seq.assert_neut)
  then show ?thesis by simp
qed


(* Original lines 35-36. *)
lemma assign_alt: "lve := e = (\<Squnion>lv k. (\<ltort>lve\<rtort>lv \<parallel> \<lblot>e\<rblot>k) ; \<langle>\<top>,update lv k\<rangle>)"
  using atomic_equiv assign_def by simp


(* Original lines 38-93. *)
text \<open>The law for introducing an assignment command makes use of the Hoare-style inference rules
for reasoning about both its left and right side expressions.
The atomic update within an assignment command must satisfy both the post-condition and the guarantee.
To allow for interference before and after the atomic update, 
the post-condition \<open>q\<close> must tolerate interference satisfying the rely condition \<open>r\<close>
from initial states satisfying \<open>p\<close>.
The rely condition \<open>r\<close> must be reflexive to allow for the parallel expression evaluation
of the left and right side expressions.
The guarantee \<open>g\<close> must be reflexive to allow for idling transitions in the assignment commands.
Introducing an assignment requires that
evaluating its l-value expression \<open>lve\<close> to \<open>lv\<close> establishes \<open>P1 lv\<close> and
evaluating its right side expression \<open>e\<close> to \<open>k\<close> establishes \<open>P2 k\<close>.
These two conditions combined with updating \<open>lv\<close> to be \<open>k\<close> ensure 
both the guarantee \<open>g\<close> and the postcondition \<open>q\<close> are satisfied.\<close>
lemma rely_guar_assign:
  assumes refl_r: "refl r"
  assumes refl_g: "refl g"
  assumes q_tolerates_r: "tolerates_interference p q r"
  assumes establish_P1: "\<And>lv. {. p .} rely r \<iinter> \<ltort>lve\<rtort>lv {. P1 lv .}"
  assumes establish_P2: "\<And>k. {. p .} rely r \<iinter> \<lblot>e\<rblot>k {. P2 k .}"
  assumes establish_g_q: "\<And>k lv. (P1 lv \<inter> P2 k) \<triangleleft> update lv k \<subseteq> g \<inter> q"
  shows "guar\<^sub>\<pi> g \<iinter> rely r \<iinter> \<lbrace>p\<rbrace> ; \<lparr>q\<rparr> \<ge> lve := e"
proof -
  have assign_expressions: "\<And>lv k. {. p .} rely r \<iinter> (\<ltort>lve\<rtort>lv \<parallel> \<lblot>e\<rblot>k) {. P1 lv \<inter> P2 k .}" 
    using establish_P1 establish_P2 expr_guar lval_guar refl_r triple_par_with_rely by blast 
  have assign_update_guar: "\<And>lv k. \<lbrace>P1 lv \<inter> P2 k\<rbrace> ; (guar\<^sub>\<pi> g \<iinter> \<lparr>q\<rparr>) \<ge> opt(update lv k)" 
    using establish_g_q refl_g seq_conj.assert_op_sync_right spec_ref_opt_guar by presburger 
  have "\<And>lv k. guar\<^sub>\<pi> g \<iinter> rely r \<iinter> \<lbrace>p\<rbrace> ; \<lparr>q\<rparr> \<ge> (\<ltort>lve\<rtort>lv \<parallel> \<lblot>e\<rblot>k) ; opt(update lv k) ; idle" 
  proof -
    fix lv k
    have "guar\<^sub>\<pi> g \<iinter> rely r \<iinter> \<lbrace>p\<rbrace> ; \<lparr>q\<rparr> = guar\<^sub>\<pi> g \<iinter> rely r \<iinter> \<lbrace>p\<rbrace> ; idle ; \<lparr>q\<rparr> ; idle" 
      using q_tolerates_r seq_conj.sync_assoc spec_tolerates_interference tolerates_rely_def by force 
    also have "\<dots> = rely r \<iinter> (guar\<^sub>\<pi> g \<iinter> \<lbrace>p\<rbrace> ; idle ; \<lparr>q\<rparr> ; idle)" 
      by (simp add: conj.left_commute seq_conj.sync_assoc)
    also have "\<dots> = rely r \<iinter> \<lbrace>p\<rbrace> ; (guar\<^sub>\<pi> g \<iinter> idle) ; (guar\<^sub>\<pi> g \<iinter> \<lparr>q\<rparr>) ; (guar\<^sub>\<pi> g \<iinter> idle)" 
      using pgm_guar_conj_seq seq_conj.assert_op_sync_right by force
    also have "\<dots> = rely r \<iinter> \<lbrace>p\<rbrace> ; (idle \<parallel> idle) ; (guar\<^sub>\<pi> g \<iinter> \<lparr>q\<rparr>) ; idle" 
      using guar_idle idle_par_idle refl_g by presburger
    also have "\<dots> \<ge> rely r \<iinter> \<lbrace>p\<rbrace> ; (\<ltort>lve\<rtort>lv \<parallel> \<lblot>e\<rblot>k) ; (guar\<^sub>\<pi> g \<iinter> \<lparr>q\<rparr>) ; idle" (is "_ \<ge> ?rhs")
      using idle_eval(1,2) seq.seq_mono_left seq.seq_mono_right seq_par.sync_mono seq_conj.sync_mono_right 
      by presburger
    also have "?rhs \<ge> rely r \<iinter> (\<ltort>lve\<rtort>lv \<parallel> \<lblot>e\<rblot>k) ; \<lbrace>P1 lv \<inter> P2 k\<rbrace> ; (guar\<^sub>\<pi> g \<iinter> \<lparr>q\<rparr>) ; idle" (is "_ \<ge> ?rhs")
      using assign_expressions by (meson refine_within_rely_left triple_with_rely)
    also have "?rhs \<ge> (\<ltort>lve\<rtort>lv \<parallel> \<lblot>e\<rblot>k) ; (\<lbrace>P1 lv \<inter> P2 k\<rbrace> ; (guar\<^sub>\<pi> g \<iinter> \<lparr>q\<rparr>)) ; idle" (is "_ \<ge> ?rhs") 
      using rely_remove seq.seq_assoc by auto 
    also have "?rhs \<ge> (\<ltort>lve\<rtort>lv \<parallel> \<lblot>e\<rblot>k) ; opt(update lv k) ; idle" (is "_ \<ge> ?rhs") 
      using assign_update_guar seq.seq_mono_left seq.seq_mono_right by presburger 
    finally show "guar\<^sub>\<pi> g \<iinter> rely r \<iinter> \<lbrace>p\<rbrace> ; \<lparr>q\<rparr> \<ge> (\<ltort>lve\<rtort>lv \<parallel> \<lblot>e\<rblot>k) ; opt(update lv k) ; idle" .
  qed
  then have "guar\<^sub>\<pi> g \<iinter> rely r \<iinter> \<lbrace>p\<rbrace> ; \<lparr>q\<rparr> 
          \<ge> (\<Squnion>lv k. (\<ltort>lve\<rtort>lv \<parallel> \<lblot>e\<rblot>k) ; opt(update lv k) ; idle)" (is "_ \<ge> ?rhs") 
    by (simp add: SUP_le_iff) 
  also have "?rhs = lve := e" 
    using assign_def by presburger
  finally show ?thesis . 
qed


(* Original lines 95-200. *)
text\<open>If I refine a spec to an assignment, I often want to establish a post condition that can be
used as the precondition to the next refinement. The chain variant of \<open>rely_guar_assign\<close> is not
needed since the assertion can be extracted from the spec directly.\<close>
lemma chain_atomic_spec_ref_assign_op:
  assumes refl_r: "refl r"
  assumes refl_g: "refl g"
  assumes stable_a: "stable p1 r"
  assumes establish_P1: "\<And>lv. {. p0 .} rely r \<iinter> \<ltort>lve\<rtort>lv {. P1 lv .}"
  assumes establish_P2: "\<And>k. {. p0 .} rely r \<iinter> \<lblot>e\<rblot>k {. P2 k .}"
  assumes establish_g_q_p1: "\<And>k lv. (p \<inter> P1 lv \<inter> P2 k) \<triangleleft> assign_op lv k \<subseteq> (g \<inter> q) \<triangleright> p1"
  shows "guar\<^sub>\<pi> g \<iinter> rely r \<iinter> (\<lbrace>p0\<rbrace> ; \<langle>p,q\<rangle>)
      \<ge> (\<Squnion>lv k. (\<ltort>lve\<rtort>lv \<parallel> \<lblot>e\<rblot>k) ; opt (assign_op lv k) ; idle) ; \<lbrace>p1\<rbrace>"
proof -
  have assign_expressions:
    "\<And>lv k. {. p0 .} rely r \<iinter> (\<ltort>lve\<rtort>lv \<parallel> \<lblot>e\<rblot>k) {. P1 lv \<inter> P2 k .}"
    using establish_P1 establish_P2 expr_guar lval_guar refl_r
      triple_par_with_rely by blast

  have "\<And>lv k. guar\<^sub>\<pi> g \<iinter> rely r \<iinter> (\<lbrace>p0\<rbrace> ; \<langle>p,q\<rangle>) \<ge>
      (\<ltort>lve\<rtort>lv \<parallel> \<lblot>e\<rblot>k) ; opt(assign_op lv k) ; idle ; \<lbrace>p1\<rbrace>"
  proof -
    fix lv k
    have assign_op_post:
      "(p \<inter> P1 lv \<inter> P2 k) \<triangleleft> assign_op lv k \<subseteq> (g \<inter> q) \<triangleright> p1"
      by (simp add: establish_g_q_p1)
    have assign_op_allowed: "(p \<inter> P1 lv \<inter> P2 k) \<triangleleft> assign_op lv k \<subseteq> g \<inter> q"
      using range_restrict_remove assign_op_post by blast
    have "guar\<^sub>\<pi> g \<iinter> rely r \<iinter> (\<lbrace>p0\<rbrace> ; \<langle>p,q\<rangle>)
        = rely r \<iinter> (\<lbrace>p0\<rbrace> ; (guar\<^sub>\<pi> g \<iinter> idle) ; \<lbrace>p\<rbrace> ; (guar\<^sub>\<pi> g \<iinter> opt q) ; (guar\<^sub>\<pi> g \<iinter> idle))"
    proof -
      have f1: "\<lbrace>p0\<rbrace> = guar\<^sub>\<pi> g \<iinter> \<lbrace>p0\<rbrace>"
        using local.conj.commute pgm_guar_conj_assert by presburger
      have "\<lbrace>p\<rbrace> = guar\<^sub>\<pi> g \<iinter> \<lbrace>p\<rbrace>"
        using local.conj.commute pgm_guar_conj_assert by fastforce
      then have "\<lbrace>p0\<rbrace> ; (guar\<^sub>\<pi> g \<iinter> idle) ; \<lbrace>p\<rbrace> ; (guar\<^sub>\<pi> g \<iinter> opt q) ; (guar\<^sub>\<pi> g \<iinter> idle) 
               = guar\<^sub>\<pi> g \<iinter> \<lbrace>p0\<rbrace> ; (idle ; \<lbrace>p\<rbrace>) ; (opt q ; idle)"
        using f1 by (simp add: pgm_guar_conj_seq seq_par.seq_assoc)
      then show ?thesis
        by (simp add: atomic_spec_def local.conj.left_commute seq_conj.sync_assoc seq_par.seq_assoc)
    qed 
    also have "\<dots> = rely r \<iinter> (\<lbrace>p0\<rbrace> ; (idle \<parallel> idle) ; \<lbrace>p\<rbrace> ; (guar\<^sub>\<pi> g \<iinter> opt q) ; idle)"
      by (simp add: guar_idle idle_par_idle refl_g)
    also have "\<dots> \<ge> rely r \<iinter> (\<lbrace>p0\<rbrace> ; (\<ltort>lve\<rtort>lv \<parallel> \<lblot>e\<rblot>k) ; \<lbrace>p\<rbrace> ; (guar\<^sub>\<pi> g \<iinter> opt q) ; idle)" (is "_ \<ge> ?rhs")
    proof -
      have f1: "\<ltort>lve\<rtort>lv \<le> idle"
        using idle_eval(2) by blast
      have "\<lblot>e\<rblot>k \<le> idle"
        using idle_eval(1) by blast
      then have "\<ltort>lve\<rtort>lv \<le> idle \<and> \<lblot>e\<rblot>k \<le> idle"
        using f1 by blast
      then show ?thesis
        by (simp add: refine_within_rely_left seq_conj.sync_mono_right
                      seq_par.seq_mono_right seq_par.sync_mono)
    qed
    also have "?rhs \<ge> rely r \<iinter> ((\<ltort>lve\<rtort>lv \<parallel> \<lblot>e\<rblot>k) ; \<lbrace>P1 lv \<inter> P2 k\<rbrace> ; \<lbrace>p\<rbrace> 
                    ; (guar\<^sub>\<pi> g \<iinter> opt q) ; idle)" (is "_ \<ge> ?rhs")
      using assign_expressions[of lv k] triple_with_rely seq.seq_mono_right
      by (simp add: refine_within_rely_left) 
    also have "?rhs = rely r \<iinter> ((\<ltort>lve\<rtort>lv \<parallel> \<lblot>e\<rblot>k) ; \<lbrace>p \<inter> P1 lv \<inter> P2 k\<rbrace> ; opt (g \<inter> q) ; idle)"
    proof -
      have "\<lbrace>P1 lv \<inter> P2 k\<rbrace> ; \<lbrace>p\<rbrace> = \<lbrace>p \<inter> P1 lv \<inter> P2 k\<rbrace>"
        by (metis seq.assert_op_assert seq.assert_op_commute seq_par.seq_assoc)
      then show ?thesis
        by (simp add: pgm_guar_conj_opt refl_g seq_par.seq_assoc)
    qed
    also have "\<dots> \<ge> rely r \<iinter> ((\<ltort>lve\<rtort>lv \<parallel> \<lblot>e\<rblot>k) ;\<lbrace>p \<inter> P1 lv \<inter> P2 k\<rbrace> ;
          opt ((p \<inter> P1 lv \<inter> P2 k) \<triangleleft> assign_op lv k) ; idle)" (is "_ \<ge> ?rhs")
      using assign_op_allowed opt_strengthen refine_within_rely
        seq_conj.sync_mono_right by presburger
    also have "?rhs = rely r \<iinter> ((\<ltort>lve\<rtort>lv \<parallel> \<lblot>e\<rblot>k) ; \<lbrace>p \<inter> P1 lv \<inter> P2 k\<rbrace> ; opt (assign_op lv k) ; idle)"
    proof-
      have "\<lbrace>p \<inter> P1 lv \<inter> P2 k\<rbrace> ; opt ((p \<inter> P1 lv \<inter> P2 k) \<triangleleft> assign_op lv k)
          = \<lbrace>p \<inter> P1 lv \<inter> P2 k\<rbrace> ; \<tau> (p \<inter> P1 lv \<inter> P2 k) ; opt (assign_op lv k)"
        by (simp add: seq_par.seq_assoc test_seq_opt)
      also have "\<dots> = \<lbrace>p \<inter> P1 lv \<inter> P2 k\<rbrace> ;  opt (assign_op lv k)"
        by (simp add: seq.assert_op_test_idem)
      finally show ?thesis
        by (simp add: seq_par.seq_assoc) 
    qed
    also have "\<dots> = rely r \<iinter> ((\<ltort>lve\<rtort>lv \<parallel> \<lblot>e\<rblot>k) ;
                    \<lbrace>p \<inter> P1 lv \<inter> P2 k\<rbrace> ; opt (assign_op lv k) ; idle ; \<lbrace>p1\<rbrace>)"
    proof -
      have "(p \<inter> P1 lv \<inter> P2 k) \<triangleleft> assign_op lv k \<subseteq> UNIV \<triangleright> p1"
        using assign_op_post
        using range_restrict_inter by fastforce
      then show ?thesis
      using rely_assert_opt_idle_extract_post_assert[OF _ stable_a]
        by (simp add: rely_conj_seq seq_par.seq_assoc)
    qed
    also have "\<dots> \<ge> rely r \<iinter> ((\<ltort>lve\<rtort>lv \<parallel> \<lblot>e\<rblot>k) ; opt (assign_op lv k) ; idle ; \<lbrace>p1\<rbrace>)" (is "_ \<ge> ?rhs")
      using seq.op_assert_op_to seq_conj.sync_mono_right seq_par.seq_mono
      by fastforce
    also have "?rhs \<ge> (\<ltort>lve\<rtort>lv \<parallel> \<lblot>e\<rblot>k) ; opt(assign_op lv k) ; idle ; \<lbrace>p1\<rbrace>"
      by (simp add: rely_remove)
    finally show "guar\<^sub>\<pi> g \<iinter> rely r \<iinter> (\<lbrace>p0\<rbrace> ; \<langle>p,q\<rangle>)
               \<ge> (\<ltort>lve\<rtort>lv \<parallel> \<lblot>e\<rblot>k) ; opt(assign_op lv k) ; idle ; \<lbrace>p1\<rbrace>" .
  qed
  then have "guar\<^sub>\<pi> g \<iinter> rely r \<iinter> (\<lbrace>p0\<rbrace> ; \<langle>p,q\<rangle>) \<ge>
      (\<Squnion>lv k. (\<ltort>lve\<rtort>lv \<parallel> \<lblot>e\<rblot>k) ; opt (assign_op lv k) ; idle ; \<lbrace>p1\<rbrace>)" (is "_ \<ge> ?rhs")
    by (simp add: SUP_le_iff)
  also have "?rhs = (\<Squnion>lv. (\<Squnion>k. (\<ltort>lve\<rtort>lv \<parallel> \<lblot>e\<rblot>k) ; opt (assign_op lv k) ; idle) ; \<lbrace>p1\<rbrace>)"
    by (simp add: seq.Sup_UNIV_op)
  also have "\<dots> = (\<Squnion>lv k. (\<ltort>lve\<rtort>lv \<parallel> \<lblot>e\<rblot>k) ; opt (assign_op lv k) ; idle) ; \<lbrace>p1\<rbrace>"
    by (simp add: seq.Sup_UNIV_op)
  finally show ?thesis .
qed


(* Original lines 202-216. *)
lemma chain_assert_atomic_spec_ref_assign:
  assumes refl_r: "refl r"
  assumes refl_g: "refl g"
  assumes stable_a: "stable p1 r"
  assumes establish_P1: "\<And>lv. {. p0 .} rely r \<iinter> \<ltort>lve\<rtort>lv {. P1 lv .}"
  assumes establish_P2: "\<And>k. {. p0 .} rely r \<iinter> \<lblot>e\<rblot>k {. P2 k .}"
  assumes establish_g_q_p1: "\<And>k lv. (p \<inter> P1 lv \<inter> P2 k) \<triangleleft> update lv k \<subseteq> (g \<inter> q) \<triangleright> p1"
  shows "guar\<^sub>\<pi> g \<iinter> rely r \<iinter> (\<lbrace>p0\<rbrace> ; \<langle>p,q\<rangle>) \<ge> lve := e ; \<lbrace>p1\<rbrace>"
proof -
  have "guar\<^sub>\<pi> g \<iinter> rely r \<iinter> (\<lbrace>p0\<rbrace> ; \<langle>p,q\<rangle>)
      \<ge> (\<Squnion>lv k. (\<ltort>lve\<rtort>lv \<parallel> \<lblot>e\<rblot>k) ; opt (update lv k) ; idle) ; \<lbrace>p1\<rbrace>"
    using chain_atomic_spec_ref_assign_op[where assign_op="update"] assms by presburger
  then show ?thesis
    by (simp add: assign_def seq_par.SUP_seq)
qed


(* Original lines 218-233. *)
lemma assert_atomic_spec_ref_assign:
  assumes refl_r: "refl r"
  assumes refl_g: "refl g"
  assumes establish_P1: "\<And>lv. {. p0 .} rely r \<iinter> \<ltort>lve\<rtort>lv {. P1 lv .}"
  assumes establish_P2: "\<And>k. {. p0 .} rely r \<iinter> \<lblot>e\<rblot>k {. P2 k .}"
  assumes establish_g_q: "\<And>k lv. (p \<inter> P1 lv \<inter> P2 k) \<triangleleft> update lv k \<subseteq> g \<inter> q"
  shows "guar\<^sub>\<pi> g \<iinter> rely r \<iinter> (\<lbrace>p0\<rbrace> ; \<langle>p,q\<rangle>) \<ge> lve := e"
proof -
  have univ_stable: "stable UNIV r" by simp
  have "\<And>k lv. (p \<inter> P1 lv \<inter> P2 k) \<triangleleft> update lv k \<subseteq> (g \<inter> q) \<triangleright> UNIV" using establish_g_q
    by (simp add: range_restrict_univ)
  then have "guar\<^sub>\<pi> g \<iinter> rely r \<iinter> (\<lbrace>p0\<rbrace> ; \<langle>p,q\<rangle>) \<ge> lve := e ; \<lbrace>UNIV\<rbrace>"
    using chain_assert_atomic_spec_ref_assign univ_stable assms by presburger
  then show ?thesis
    by (simp add: seq.assert_neut) 
qed


(* Original lines 235-278. *)
text \<open>If an assignment is performed on an l-value expression that must evaluate to an l-value in
vars, then you can add a frame for free.\<close>
lemma assign_add_frame:
  assumes lval_in_frame: "\<And>lv. \<ltort>lve\<rtort>lv \<noteq> \<bottom> \<Longrightarrow> lv |\<in>| vars"
  shows "vars:\<^sub>s(lve := e) = lve := e"
proof -
  have frame_refl: "refl (id_bar vars)"
    by (rule id_bar_refl)
  have branch_framed:
    "guar\<^sub>\<pi> (id_bar vars) \<iinter>
       ((\<ltort>lve\<rtort>lv \<parallel> \<lblot>e\<rblot>k) ; opt(update lv k) ; idle) =
     (\<ltort>lve\<rtort>lv \<parallel> \<lblot>e\<rblot>k) ; opt(update lv k) ; idle"
    for lv k
  proof (cases "\<ltort>lve\<rtort>lv = \<bottom>")
    have non_abort: "\<lblot>e\<rblot>k \<le> chaos"
      by (metis idle_eval(1) idle_nonaborting sup.coboundedI2 sup.order_iff)
    case True
    then show ?thesis using non_abort
      by (simp add: local.conj.commute nonaborting_par_magic pgm_guar_conj_bot seq.bot_annihilates_left)
  next
    case False
    have target: "lv |\<in>| vars"
      by (rule lval_in_frame[OF False])
    have update_subset: "update lv k \<subseteq> id_bar vars"
      by (rule update_in_frame[OF target])
    have update_inter: "id_bar vars \<inter> update lv k = update lv k"
      using update_subset by blast
    have update_framed:
      "guar\<^sub>\<pi> (id_bar vars) \<iinter> opt(update lv k) = opt(update lv k)"
      by (simp add: pgm_guar_conj_opt frame_refl update_inter)
    have eval_framed:
      "guar\<^sub>\<pi> (id_bar vars) \<iinter> (\<ltort>lve\<rtort>lv \<parallel> \<lblot>e\<rblot>k) =
       (\<ltort>lve\<rtort>lv \<parallel> \<lblot>e\<rblot>k)"
      by (simp add: pgm_guar_distrib_par lval_guar expr_guar frame_refl)
    have idle_framed: "guar\<^sub>\<pi> (id_bar vars) \<iinter> idle = idle"
      by (rule guar_idle[OF frame_refl])
    show ?thesis
      by (simp add: pgm_guar_conj_seq eval_framed update_framed idle_framed)
  qed
  have "guar\<^sub>\<pi> (id_bar vars) \<iinter> (lve := e) = lve := e"
    by (simp add: assign_def pgm_guar_conj_Sup branch_framed)
  then show ?thesis
    by (simp add: var_frame_set_def)
qed


(* Original lines 280-305. *)
lemma assign_terminates: "terminate \<ge> lve := e"
  unfolding assign_def
proof (rule SUP_least)
  fix lv
  show "(\<Squnion>k. (\<ltort>lve\<rtort>lv \<parallel> \<lblot>e\<rblot>k) ; opt (update lv k) ; idle) \<le> terminate"
  proof (rule SUP_least)
    fix k

    have eval_terminates: "(\<ltort>lve\<rtort>lv \<parallel> \<lblot>e\<rblot>k) \<le> terminate"
    proof -
      have lval_idle: "\<ltort>lve\<rtort>lv \<le> idle"
        by (rule idle_eval(2))
      have expr_idle: "\<lblot>e\<rblot>k \<le> idle"
        by (rule idle_eval(1))
      have "(\<ltort>lve\<rtort>lv \<parallel> \<lblot>e\<rblot>k) \<le> idle"
        by (simp add: expr_idle idle_par_idle lval_idle par.op_idem_mono)
      also have "\<dots> \<le> terminate"
        by (rule terminate_ref_idle)
      finally show ?thesis .
    qed

    show "(\<ltort>lve\<rtort>lv \<parallel> \<lblot>e\<rblot>k) ; opt (update lv k) ; idle \<le> terminate"
      using eval_terminates opt_terminates terminate_ref_idle
            terminate_seq by auto
  qed
qed
