theory Bind
  imports Expressions_Mref
begin

context frame_state
begin

text\<open>Binds the evaluated value of an expression into a constant argument for body.\<close>

(*An alternative version that uses tests instead of expression evaluations can be
found in DEAD/Bind.thy for comparison. That version is less realistic
for an actual programming language however.*)
definition bind_command ::
  "('state, 'v) Expr \<Rightarrow>
   ('v \<Rightarrow> 'a::complete_distrib_lattice) \<Rightarrow> 'a"
  ("bind (_)/ in (_)" [1000, 91] 91)
where
  "bind_command e body \<equiv> (\<Squnion>k. \<lblot>e\<rblot>k ; body k)"

text \<open>Binds the evaluated l-value of an l-value expression into a constant argument for body.\<close>
definition bindlv_command ::
  "('state, 'v) LValueExpr \<Rightarrow>
   ('v LValue \<Rightarrow> 'a::complete_distrib_lattice) \<Rightarrow> 'a"
  ("bindlv (_)/ in (_)" [1000, 91] 91)
where
  "bindlv_command lve body \<equiv> (\<Squnion>lv. \<ltort>lve\<rtort>lv ; body lv)"

lemma idle_ref_bind: "idle ; body \<ge> bind e in (\<lambda>k. body)"
proof-
  have "bind e in (\<lambda>k. body) = (\<Squnion>k. \<lblot>e\<rblot>k ; body)" 
    by (simp add: bind_command_def)
  also have "\<dots> \<le> idle ; body"
  proof(rule Sup_least)
    fix x
    assume x_in: "x \<in> range (\<lambda>k. \<lblot>e\<rblot>k ; body)"
    obtain k where xk: "x = \<lblot>e\<rblot>k ; body" using x_in by auto
    then show "x \<le> idle ; body"
      by (simp add: idle_eval(1) seq_par.seq_mono_left)
  qed
  finally show ?thesis .
qed

lemma bind_ref_idle: "bind e in (\<lambda>k. body) \<ge> idle ; body"
proof-
  have "bind e in (\<lambda>k. body) = (\<Squnion>k. \<lblot>e\<rblot>k ; body)" 
    by (simp add: bind_command_def)
  also have "\<dots> = (\<Squnion>k. \<lblot>e\<rblot>k) ; body"
    using seq.Sup_UNIV_op[where c="expr_cmd e" and d="body"] by auto
  also have "\<dots> \<ge> idle ; body"
    by (simp add: eval_Sup_idle seq_par.seq_mono_left)
  finally show ?thesis .
qed

text \<open>A bind can be introduced provided there is a free idle to evaluate the expression\<close>
lemma bind_idle: "bind e in (\<lambda>k. body) = idle ; body"
  apply (rule antisym)
  subgoal using idle_ref_bind .
  subgoal using bind_ref_idle .
  done

lemma bind_rely_alt: "rely r \<iinter> bind e in body = (\<Squnion>k. (rely r \<iinter> \<lblot>e\<rblot>k) ; (rely r \<iinter> body k))"
  by (simp add: bind_command_def conj.op_Sup_UNIV rely_conj_seq)

lemma bind_rely_alt_2: "rely r \<iinter> bind e in body = rely r \<iinter> (\<Squnion>k. (rely r \<iinter> \<lblot>e\<rblot>k) ; body k)"
  by (simp add: bind_command_def conj.op_Sup_UNIV rely_conj_seq)

lemma bind_rely_alt_3: "rely r \<iinter> bind e in body = rely r \<iinter> (\<Squnion>k. \<lblot>e\<rblot>k ; (rely r \<iinter> body k))"
  by (simp add: bind_command_def conj.op_Sup_UNIV rely_conj_seq)

text \<open>If an expression is invariant under a reflexive rely, an assertion that
the bound expression equals the bound name can be introduced.\<close>
lemma bind_var_is_expr_eval:
  assumes r_refl: "refl r"
  assumes invar_e: "invar_expr e r"
  shows "rely r \<iinter> bind e in body = rely r \<iinter> bind e in (\<lambda>k. \<lbrace>expr_eq e k\<rbrace> ; body k)"
proof-
  have "rely r \<iinter> bind e in body = rely r \<iinter> (\<Squnion>k. ((rely r \<iinter> \<lblot>e\<rblot>k) ; body k))"
    by (simp only: bind_rely_alt_2)
  also have "\<dots> = rely r \<iinter> (\<Squnion>k. ((rely r \<iinter> (\<lblot>e\<rblot>k ; \<lbrace>expr_eq e k\<rbrace>)) ; body k))"
    using r_refl invar_e rely_expr_extract_eval by auto
  also have "\<dots> = rely r \<iinter> (\<Squnion>k. (rely r \<iinter> \<lblot>e\<rblot>k) ; \<lbrace>expr_eq e k\<rbrace> ; body k)"
    by (simp add: conj.op_Sup_UNIV rely_conj_seq)
  finally show ?thesis using bind_rely_alt_2
    by (simp add: seq_par.seq_assoc)
qed

text \<open>A rely can be copied into the bind body.\<close>
lemma rely_into_bind: "rely r \<iinter> bind e in body = rely r \<iinter> bind e in (\<lambda>k. rely r \<iinter> body k)"
  using bind_rely_alt_3 bind_command_def by auto

lemma bind_guar_alt: 
  assumes refl_g: "refl g"
  shows "guar\<^sub>\<pi> g \<iinter> bind e in body = (\<Squnion>k. \<lblot>e\<rblot>k ; (guar\<^sub>\<pi> g \<iinter> body k))"
  by (simp add: bind_command_def conj.op_Sup_UNIV pgm_guar_conj_seq refl_g expr_guar)

text \<open>A program guar can be moved into the bind body.\<close>
lemma guar_into_bind: 
  assumes refl_g: "refl g"
  shows "guar\<^sub>\<pi> g \<iinter> bind e in body = bind e in (\<lambda>k. guar\<^sub>\<pi> g \<iinter> body k)"
  using bind_guar_alt bind_command_def refl_g by auto

lemma bind_ref_mono:
  assumes step: "\<And>k2. \<exists>k1. \<lblot>e1\<rblot>k1 ; c1 k1 \<ge> \<lblot>e2\<rblot>k2 ; c2 k2"
  shows "bind e1 in c1 \<ge> bind e2 in c2"
  unfolding bind_command_def
  apply (rule SUP_mono) using step by simp 

lemma bind_ref_mono':
  assumes step: "\<And>k. c k \<ge> d k"
  shows "bind e in c \<ge> bind e in d"
  unfolding bind_command_def
  apply (rule SUP_mono')
  using step seq_par.seq_mono_right by simp

end
end