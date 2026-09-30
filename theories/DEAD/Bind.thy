
theory Bind
  imports Expressions Expressions_Mref Rely_Guarantee.Invariant
begin

context frame_state
begin

text\<open>Binds the evaluated value of an expression into a constant argument for body.
Effectively, let's you peak into the state, evaluate an expression and then refer to the
result of that expression later.

Might be useful if you know the evaluation of the expression is invariant within the
full bind body.\<close>

(* An alternate is to use (\<Squnion>k. \<lblot>e\<rblot>k ; body k), it requires
free idles and more complicated proofs, but is more realistic in an actual programming
langugage.*)
definition bind_command ::
  "('state, 'v) Expr \<Rightarrow>
   ('v \<Rightarrow> 'a::complete_distrib_lattice) \<Rightarrow> 'a"
  ("bind (_)/ in (_)" [1000, 91] 91)
where
  "bind_command e body \<equiv> (\<Squnion>k. \<tau> (expr_eq e k) ; body k)"

text\<open>Binds the evaluated l-value of an l-value expression into a constant argument for body.
Effectively, let's you peak into the state, evaluate an l-value expression and then refer to the
resulting lvalue.\<close>
definition bindlv_command ::
  "('state, 'v) LValueExpr \<Rightarrow>
   ('v LValue \<Rightarrow> 'a::complete_distrib_lattice) \<Rightarrow> 'a"
  ("bindlv (_)/ in (_)" [1000, 91] 91)
where
  "bindlv_command lve body \<equiv> (\<Squnion>lv. \<tau> (lval_eq lve lv) ; body lv)"

lemma nil_ref_bind: "body \<ge> bind e in (\<lambda>k. body)"
proof-
  have "bind e in (\<lambda>k. body) = (\<Squnion>k. \<tau> (expr_eq e k); body)" 
    by (simp add: bind_command_def)
  also have "\<dots> \<le> nil ; body"
  proof(rule Sup_least)
    fix x
    assume x_in: "x \<in> range (\<lambda>k. \<tau> (expr_eq e k) ; body)"
    obtain k where xk: "x = \<tau> (expr_eq e k) ; body" using x_in by auto
    then show "x \<le> nil ; body"
      by (simp add: seq.remove_assert_left seq.test_assert_galois)
  qed
  finally show ?thesis by simp 
qed

lemma bind_ref_nil: "bind e in (\<lambda>k. body) \<ge> body"
proof-
  have "bind e in (\<lambda>k. body) = (\<Squnion>k. \<tau> (expr_eq e k) ; body)" 
    by (simp add: bind_command_def)
  also have "\<dots> = (\<Squnion>k. \<tau> (expr_eq e k)) ; body"
    using seq.Sup_UNIV_op[where c="\<lambda>k. \<tau> (expr_eq e k)" and d="body"] by auto
  also have "\<dots> \<ge> nil ; body"
    by (simp add: fn_eq_all)
  finally show ?thesis by simp
qed

lemma bind_introduce: "bind e in (\<lambda>k. body) = body"
  apply (rule antisym)
  subgoal using nil_ref_bind .
  subgoal using bind_ref_nil .
  done

text \<open>The following l-value laws are the direct counterparts of the
expression bind laws above.\<close>
lemma nil_ref_bindlv: "body \<ge> bindlv lve in (\<lambda>lv. body)"
proof -
  have "bindlv lve in (\<lambda>lv. body) = (\<Squnion>lv. \<tau> (lval_eq lve lv) ; body)"
    by (simp add: bindlv_command_def)
  also have "\<dots> \<le> nil ; body"
  proof (rule Sup_least)
    fix x
    assume x_in: "x \<in> range (\<lambda>lv. \<tau> (lval_eq lve lv) ; body)"
    obtain lv where x_lv: "x = \<tau> (lval_eq lve lv) ; body"
      using x_in by auto
    then show "x \<le> nil ; body"
      by (simp add: seq.remove_assert_left seq.test_assert_galois)
  qed
  finally show ?thesis by simp
qed

lemma bindlv_ref_nil: "bindlv lve in (\<lambda>lv. body) \<ge> body"
proof -
  have "bindlv lve in (\<lambda>lv. body) = (\<Squnion>lv. \<tau> (lval_eq lve lv) ; body)"
    by (simp add: bindlv_command_def)
  also have "\<dots> = (\<Squnion>lv. \<tau> (lval_eq lve lv)) ; body"
    using seq.Sup_UNIV_op
      [where c = "\<lambda>lv. \<tau> (lval_eq lve lv)" and d = "body"] by auto
  also have "\<dots> \<ge> nil ; body"
    by (simp add: lval_eq_all)
  finally show ?thesis by simp
qed

lemma bindlv_introduce: "bindlv lve in (\<lambda>lv. body) = body"
  apply (rule antisym)
  subgoal using nil_ref_bindlv .
  subgoal using bindlv_ref_nil .
  done

lemma bind_var_is_expr_eval: "bind e in body = bind e in (\<lambda>k. \<lbrace>expr_eq e k\<rbrace> ; body k)"
proof-
  have "bind e in body = (\<Squnion>k. (\<tau> (expr_eq e k) ; body k))"
    by (simp only: bind_command_def)
  also have "\<dots> = (\<Squnion>k. ((\<tau> (expr_eq e k) ; \<lbrace>expr_eq e k\<rbrace>)) ; body k)"
    using seq.test_op_assert by auto
  also have "\<dots> =  (\<Squnion>k. \<tau> (expr_eq e k) ; (\<lbrace>expr_eq e k\<rbrace> ; body k))"
    using seq_par.seq_assoc by auto
  finally show ?thesis using bind_command_def by simp
qed

lemma bindlv_var_is_lval_eval:
  "bindlv lve in body = bindlv lve in (\<lambda>lv. \<lbrace>lval_eq lve lv\<rbrace> ; body lv)"
proof -
  have "bindlv lve in body = (\<Squnion>lv. \<tau> (lval_eq lve lv) ; body lv)"
    by (simp only: bindlv_command_def)
  also have "\<dots> = (\<Squnion>lv. (\<tau> (lval_eq lve lv) ; \<lbrace>lval_eq lve lv\<rbrace>) ; body lv)"
    using seq.test_op_assert by auto
  also have "\<dots> = (\<Squnion>lv. \<tau> (lval_eq lve lv) ; (\<lbrace>lval_eq lve lv\<rbrace> ; body lv))"
    using seq_par.seq_assoc by auto
  finally show ?thesis using bindlv_command_def by simp
qed

lemma bind_rely_alt: "rely r \<iinter> bind e in body = (\<Squnion>k. \<tau> (expr_eq e k) ; (rely r \<iinter> body k))"
  by (simp add: bind_command_def conj.op_Sup_UNIV rely_conj_seq test_seq_rely)

lemma rely_into_bind: "rely r \<iinter> bind e in body = bind e in (\<lambda>k. rely r \<iinter> body k)"
  using bind_rely_alt bind_command_def by auto

lemma bindlv_rely_alt:
 "rely r \<iinter> bindlv lve in body = (\<Squnion>lv. \<tau> (lval_eq lve lv) ; (rely r \<iinter> body lv))"
  by (simp add: bindlv_command_def conj.op_Sup_UNIV rely_conj_seq test_seq_rely)

lemma rely_into_bindlv: "rely r \<iinter> bindlv lve in body = bindlv lve in (\<lambda>lv. rely r \<iinter> body lv)"
  using bindlv_rely_alt bindlv_command_def by auto

lemma bind_guar_alt: "guar\<^sub>\<pi> g \<iinter> bind e in body = (\<Squnion>k. \<tau> (expr_eq e k) ; (guar\<^sub>\<pi> g \<iinter> body k))"
proof(simp add: bind_command_def conj.op_Sup_UNIV pgm_guar_conj_seq)
  have "\<And>x. guar\<^sub>\<pi> g \<iinter> \<tau> (expr_eq e x) = \<tau> (expr_eq e x)" 
    using pgm_guar_conj_test conj.commute by metis
  then show "(\<Squnion>x. (guar\<^sub>\<pi> g \<iinter> \<tau> (expr_eq e x)) ; (guar\<^sub>\<pi> g \<iinter> body x))
           = (\<Squnion>k. \<tau> (expr_eq e k) ; (guar\<^sub>\<pi> g \<iinter> body k))"
    by auto
qed

lemma guar_into_bind: "guar\<^sub>\<pi> g \<iinter> bind e in body = bind e in (\<lambda>k. guar\<^sub>\<pi> g \<iinter> body k)"
  using bind_guar_alt bind_command_def by auto

lemma bind_ref_mono:
  assumes step: "\<And>k2. \<exists>k1. \<tau> (expr_eq e1 k1) ; c1 k1 \<ge> \<tau> (expr_eq e2 k2) ; c2 k2"
  shows "bind e1 in c1 \<ge> bind e2 in c2"
  unfolding bind_command_def
  apply (rule SUP_mono) using step by simp 

lemma bind_ref_mono':
  assumes step: "\<And>k. c k \<ge> d k"
  shows "bind e in c \<ge> bind e in d"
  unfolding bind_command_def
  apply (rule SUP_mono')
  using step seq_par.seq_mono_right by simp

lemma bindlv_ref_mono':
  assumes step: "\<And>lv. c lv \<ge> d lv"
  shows "bindlv lve in c \<ge> bindlv lve in d"
  unfolding bindlv_command_def
  apply (rule SUP_mono')
  using step seq_par.seq_mono_right by simp

lemma bind_inv_alt2: "inv I \<iinter> bind e in body = (\<Squnion>k. inv I \<iinter> (\<tau> (expr_eq e k) ; body k))"
  by (simp add: bind_command_def conj.op_Sup_UNIV)

lemma bind_inv_alt: "inv I \<iinter> bind e in body = inv I \<iinter> (\<Squnion>k. \<tau> (expr_eq e k) ; (inv I \<iinter> body k))"
proof-
  have "inv I \<iinter> bind e in body = (\<Squnion>k. (inv I \<iinter> \<tau> (expr_eq e k)) ; (inv I \<iinter> body k))"
    by (simp add: bind_inv_alt2 inv_distrib_seq)
  also have "\<dots> = (\<Squnion>k. (inv I \<iinter> \<tau> (expr_eq e k)) ; (inv I \<iinter> (inv I \<iinter> body k)))"  by auto
  finally show ?thesis by (simp add: conj.op_Sup_UNIV inv_distrib_seq) 
qed

lemma bind_inv: "inv I \<iinter> bind e in body = inv I \<iinter> bind e in (\<lambda>k. inv I \<iinter> body k)"
  using bind_inv_alt bind_command_def by auto

lemma bindlv_inv_alt2: "inv I \<iinter> bindlv e in body = (\<Squnion>k. inv I \<iinter> (\<tau> (lval_eq e k) ; body k))"
  by (simp add: bindlv_command_def conj.op_Sup_UNIV)

lemma bindlv_inv_alt: "inv I \<iinter> bindlv e in body = inv I \<iinter> (\<Squnion>k. \<tau> (lval_eq e k) ; (inv I \<iinter> body k))"
proof-
  have "inv I \<iinter> bindlv e in body = (\<Squnion>k. (inv I \<iinter> \<tau> (lval_eq e k)) ; (inv I \<iinter> body k))"
    by (simp add: bindlv_inv_alt2 inv_distrib_seq)
  also have "\<dots> = (\<Squnion>k. (inv I \<iinter> \<tau> (lval_eq e k)) ; (inv I \<iinter> (inv I \<iinter> body k)))"  by auto
  finally show ?thesis by (simp add: conj.op_Sup_UNIV inv_distrib_seq) 
qed

lemma bindlv_inv: "inv I \<iinter> bindlv e in body = inv I \<iinter> bindlv e in (\<lambda>k. inv I \<iinter> body k)"
  using bindlv_inv_alt bind_command_def by auto

definition expr_inv where
  "expr_inv e k = inv (expr_eq e k)"

definition lval_inv where
  "lval_inv lve lv = inv (lval_eq lve lv)"

lemma introduce_expr_inv_eq: 
  assumes "stable (expr_eq e k) r"
  shows "rely r \<iinter> guar\<^sub>\<pi> (UNIV \<triangleright> expr_eq e k) \<iinter> \<lbrace>expr_eq e k\<rbrace> ; c = rely r \<iinter> expr_inv e k \<iinter> c"
  using expr_inv_def inv_introduce_eq assms by simp

lemma introduce_lval_inv_eq: 
  assumes "invar_lval lve r"
  shows "rely r \<iinter> guar\<^sub>\<pi> (UNIV \<triangleright> lval_eq lve lv) \<iinter> \<lbrace>lval_eq lve lv\<rbrace> ; c = rely r \<iinter> lval_inv lve lv \<iinter> c"
  using lval_inv_def inv_introduce_eq assms invar_lval_stable by simp

lemma introduce_expr_inv: 
  assumes "stable (expr_eq e k) r"
  shows "rely r \<iinter> \<lbrace>expr_eq e k\<rbrace> ; c \<ge> rely r \<iinter> expr_inv e k \<iinter> c"
  using expr_inv_def inv_introduce assms by simp

lemma introduce_lval_inv: 
  assumes "invar_lval lve r"
  shows "rely r \<iinter> \<lbrace>lval_eq lve lv\<rbrace> ; c \<ge> rely r \<iinter> lval_inv lve lv \<iinter> c"
  using lval_inv_def inv_introduce assms invar_lval_stable by simp

lemma bind_introduce_expr_inv_eq:
  assumes "invar_expr e r"
  shows "rely r \<iinter> bind e in (\<lambda>k. guar\<^sub>\<pi> (UNIV \<triangleright> expr_eq e k) \<iinter> body k)
       = rely r \<iinter> bind e in (\<lambda>k. expr_inv e k \<iinter> body k)"
proof-
  have "rely r \<iinter> bind e in (\<lambda>k. guar\<^sub>\<pi> (UNIV \<triangleright> expr_eq e k) \<iinter> body k)
      = bind e in (\<lambda>k. rely r \<iinter> (\<lambda>k. guar\<^sub>\<pi> (UNIV \<triangleright> expr_eq e k) \<iinter> body k) k)"
    using rely_into_bind by simp
  also have "\<dots> = bind e in (\<lambda>k. rely r \<iinter> guar\<^sub>\<pi> (UNIV \<triangleright> expr_eq e k) \<iinter> body k)"
    using seq_conj.sync_assoc by auto
  also have "\<dots> = bind e in (\<lambda>k. \<lbrace>expr_eq e k\<rbrace> ; (\<lambda>k. rely r \<iinter> guar\<^sub>\<pi> (UNIV \<triangleright> expr_eq e k) \<iinter> body k) k)"
    using bind_var_is_expr_eval by simp
  also have "\<dots> = bind e in (\<lambda>k. \<lbrace>expr_eq e k\<rbrace> ; rely r \<iinter> guar\<^sub>\<pi> (UNIV \<triangleright> expr_eq e k) \<iinter> body k)"
    by (simp add: local.conj.commute seq_conj.assert_op_sync_right)
  also have "\<dots> = bind e in (\<lambda>k. rely r \<iinter> guar\<^sub>\<pi> (UNIV \<triangleright> expr_eq e k) \<iinter> \<lbrace>expr_eq e k\<rbrace> ; body k)"
    by (simp add: seq_conj.assert_op_sync_left seq_conj.assert_op_sync_right)
  also have "\<dots> = bind e in (\<lambda>k. rely r \<iinter> expr_inv e k \<iinter> body k)"
    using assms introduce_expr_inv_eq invar_expr_stable by simp
  also have "\<dots> = bind e in (\<lambda>k. rely r \<iinter> (\<lambda>k. expr_inv e k \<iinter> body k) k)"
    by (simp add: seq_conj.sync_assoc) 
  finally show ?thesis using rely_into_bind by simp
qed

lemma bind_introduce_expr_inv:
  assumes "invar_expr e r"
  shows "rely r \<iinter> bind e in body \<ge> rely r \<iinter> bind e in (\<lambda>k. expr_inv e k \<iinter> body k)"
proof-
  have "bind e in body \<ge> bind e in (\<lambda>k. guar\<^sub>\<pi> (UNIV \<triangleright> expr_eq e k) \<iinter> body k)"
    by (rule bind_ref_mono'; simp add: pgm_guar_introduce)
  then have "rely r \<iinter> bind e in body \<ge> rely r \<iinter> bind e in (\<lambda>k. guar\<^sub>\<pi> (UNIV \<triangleright> expr_eq e k) \<iinter> body k)"
    by (simp add: seq_conj.sync_mono_right)
  then show ?thesis using assms bind_introduce_expr_inv_eq by auto
qed

(*TODO move these into test*)
lemma test_if_equiv: "(if p then c else d) = \<tau> {\<sigma>. p} ; c \<squnion> \<tau> ({\<sigma>. -p}) ; d"
proof (cases p)
  case True
  have p_univ: "UNIV = {\<sigma>. p}" using True by simp
  have np_bot: "\<bottom> = {\<sigma>. -p}" using True by simp
  have "(if p then c else d) = c" using True by simp
  also have "\<dots> = \<tau> UNIV ; c \<squnion> \<tau> \<bottom> ; d"
    using local.seq.nil_seq seq.bot_annihilates_left seq.test_bot seq.test_set_top by auto
  then show ?thesis using p_univ np_bot by auto
next
  case False
  have p_bot: "\<bottom> = {\<sigma>. p}" using False by simp
  have np_univ: "UNIV = {\<sigma>. -p}" using False by simp
  have "(if p then c else d) = d" using False by simp
  also have "\<dots> = \<tau> \<bottom> ; c \<squnion> \<tau> UNIV ; d"
    using local.seq.nil_seq seq.bot_annihilates_left seq.test_bot seq.test_set_top by auto
  then show ?thesis using p_bot np_univ by auto
qed

lemma test_if_bot_equiv: "(if p then c else \<bottom>) = \<tau> {\<sigma>. p} ; c"
proof-
  have "(if p then c else \<bottom>) = \<tau> {\<sigma>. p} ; c \<squnion> \<tau> {\<sigma>. -p} ; \<bottom>"
    using test_if_equiv by simp
  then show ?thesis
    using seq.bot_annihilates_left seq.test_bot by fastforce
qed

lemma bind_intro_rely_assert: "rely r \<iinter> c = bind e in (\<lambda>k. rely r \<iinter> \<lbrace>expr_eq e k\<rbrace> ; c)"
proof -
  have expand_c: "c = bind e in (\<lambda>k. \<lbrace>expr_eq e k\<rbrace> ; c)"
    using bind_introduce bind_var_is_expr_eval by auto
  
  have "rely r \<iinter> c = bind e in (\<lambda>k. rely r \<iinter> (\<lambda>k. \<lbrace>expr_eq e k\<rbrace> ; c) k)"
    using rely_into_bind expand_c by metis 
  also have "\<dots> = bind e in (\<lambda>k. rely r \<iinter> \<lbrace>expr_eq e k\<rbrace> ; c)"
    by auto
  
  show ?thesis
    by (simp add: calculation)
qed

lemma bind_intro_inv_rely_assert:
  "inv I \<iinter> rely r \<iinter> c = inv I \<iinter> bind e in (\<lambda>k. inv I \<iinter> rely r \<iinter> \<lbrace>expr_eq e k\<rbrace> ; c)"
proof -
  have expand_c_rely:
    "rely r \<iinter> c = bind e in (\<lambda>k. rely r \<iinter> \<lbrace>expr_eq e k\<rbrace> ; c)"
    using bind_intro_rely_assert by simp

  have "inv I \<iinter> rely r \<iinter> c = inv I \<iinter> bind e in (\<lambda>k. rely r \<iinter> \<lbrace>expr_eq e k\<rbrace> ; c)"
    using expand_c_rely by (simp add: seq_conj.sync_assoc)
  also have "\<dots> = inv I \<iinter> bind e in (\<lambda>k. inv I \<iinter> (rely r \<iinter> \<lbrace>expr_eq e k\<rbrace> ; c))"
    using bind_inv by auto
  also have "\<dots> = inv I \<iinter> bind e in (\<lambda>k. inv I \<iinter> rely r \<iinter> \<lbrace>expr_eq e k\<rbrace> ; c)"
    by (simp add: seq_conj.sync_assoc)
  finally show ?thesis .
qed

lemma bindlv_intro_rely_assert: "rely r \<iinter> c = bindlv lve in (\<lambda>lv. rely r \<iinter> (\<lbrace>lval_eq lve lv\<rbrace> ; c))"
proof -
  have expand_c:
    "c = bindlv lve in (\<lambda>lv. \<lbrace>lval_eq lve lv\<rbrace> ; c)"
    using bindlv_introduce bindlv_var_is_lval_eval by auto

  have "rely r \<iinter> c = rely r \<iinter> bindlv lve in (\<lambda>lv. \<lbrace>lval_eq lve lv\<rbrace> ; c)"
    using expand_c by (rule arg_cong)
  also have "\<dots> = bindlv lve in (\<lambda>lv. rely r \<iinter> (\<lbrace>lval_eq lve lv\<rbrace> ; c))"
    by (rule rely_into_bindlv)
  finally show ?thesis .
qed

lemma bindlv_intro_inv_rely_assert:
  "inv I \<iinter> rely r \<iinter> c = inv I \<iinter> bindlv lve in (\<lambda>lv. inv I \<iinter> rely r \<iinter> \<lbrace>lval_eq lve lv\<rbrace> ; c)"
proof -
  have expand_c_rely:
    "rely r \<iinter> c = bindlv lve in (\<lambda>lv. rely r \<iinter> \<lbrace>lval_eq lve lv\<rbrace> ; c)"
    using bindlv_intro_rely_assert by simp

  have "inv I \<iinter> rely r \<iinter> c = inv I \<iinter> bindlv lve in (\<lambda>lv. rely r \<iinter> \<lbrace>lval_eq lve lv\<rbrace> ; c)"
    using expand_c_rely by (simp add: seq_conj.sync_assoc)
  also have "\<dots> = inv I \<iinter> bindlv lve in (\<lambda>lv. inv I \<iinter> (rely r \<iinter> \<lbrace>lval_eq lve lv\<rbrace> ; c))"
    using bindlv_inv by auto
  also have "\<dots> = inv I \<iinter> bindlv lve in (\<lambda>lv. inv I \<iinter> rely r \<iinter> \<lbrace>lval_eq lve lv\<rbrace> ; c)"
    by (simp add: seq_conj.sync_assoc)
  finally show ?thesis .
qed

lemma ref_if_ref_expr_evals_both_const:
  assumes all_consts_ref:
    "\<And>k. rely r \<iinter> \<lbrace>expr_eq e k\<rbrace> ; c \<ge> d"
  shows "rely r \<iinter> c \<ge> d"
proof -
  have "rely r \<iinter> c = bind e in (\<lambda>k. rely r \<iinter> \<lbrace>expr_eq e k\<rbrace> ; c)"
    by (simp add: bind_intro_rely_assert)
  also have "\<dots> \<ge> bind e in (\<lambda>k. d)" (is "_ \<ge> ?rhs")
    using all_consts_ref bind_ref_mono' by auto
  also have "?rhs = d"
    by (simp add: bind_introduce)
  finally show ?thesis .
qed

text \<open>The l-value counterpart of \<open>ref_if_ref_expr_evals_both_const\<close>.\<close>
lemma ref_if_ref_lval_evals_both_const:
  assumes all_lvals_ref:
    "\<And>lv. rely r \<iinter> \<lbrace>lval_eq lve lv\<rbrace> ; c \<ge> d"
  shows "rely r \<iinter> c \<ge> d"
proof -
  have "rely r \<iinter> c = bindlv lve in (\<lambda>lv. rely r \<iinter> \<lbrace>lval_eq lve lv\<rbrace> ; c)"
    by (simp add: bindlv_intro_rely_assert)
  also have "\<dots> \<ge> bindlv lve in (\<lambda>lv. d)"  (is "_ \<ge> ?rhs")
    using all_lvals_ref bindlv_ref_mono' by auto
  also have "?rhs = d"
    by (simp add: bindlv_introduce)
  finally show ?thesis .
qed



(*Data refinement lemmas*)
lemma data_refine_bind:
  assumes step: "\<And>k2. \<exists>k1. \<tau> (expr_eq e1 k1) ; c1 k1 \<ge>\<^sub>I \<tau> (expr_eq e2 k2) ; c2 k2"
  shows "bind e1 in c1 \<ge>\<^sub>I bind e2 in c2"
  unfolding data_refine_def
  apply (simp only: bind_inv_alt2; rule SUP_mono) using step data_refine_def by simp

lemma data_refine_bind_mono':
  assumes step: "\<And>k. c k \<ge>\<^sub>I d k"
  shows "bind e in c \<ge>\<^sub>I bind e in d"
  unfolding data_refine_def
  apply (simp only: bind_inv_alt; rule conj.op_mono_right; rule SUP_mono')  
  using data_refine_def step seq_par.seq_mono_right by auto

lemma data_refine_bindlv_mono':
  assumes step: "\<And>k. c k \<ge>\<^sub>I d k"
  shows "bindlv e in c \<ge>\<^sub>I bindlv e in d"
  unfolding data_refine_def
  apply (simp only: bindlv_inv_alt; rule conj.op_mono_right; rule SUP_mono')  
  using data_refine_def step seq_par.seq_mono_right by auto

text \<open>Case-split a rely-constrained command by the value of an
expression or l-value expression.\<close>

text \<open>This may pair well with \<open>lval_cmd_equiv_constant_under_invar\<close> and 
\<open>expr_cmd_equiv_constant_under_invar\<close> or their logical equivalents in \<open>Expressions_Mref.thy\<close>. 
In Hoare logic, you can use the precondition \<open>expr_eq e r\<close> to replace expressions with
constant expressions.\<close>
lemma data_refine_rely_bind:
  assumes step: "\<And>k. rely r \<iinter> \<lbrace>expr_eq e k\<rbrace> ; c k \<ge>\<^sub>I d k"
  shows "rely r \<iinter> (bind e in c) \<ge>\<^sub>I bind e in d"
proof -
  have expand:
    "rely r \<iinter> (bind e in c) = bind e in (\<lambda>k. rely r \<iinter> (\<lbrace>expr_eq e k\<rbrace> ; c k))"
  proof -
    have "bind e in c = bind e in (\<lambda>k. \<lbrace>expr_eq e k\<rbrace> ; c k)"
      using bind_var_is_expr_eval by simp
    then have "rely r \<iinter> (bind e in c) = rely r \<iinter> bind e in (\<lambda>k. \<lbrace>expr_eq e k\<rbrace> ; c k)"
      by (rule arg_cong)
    also have "\<dots> = bind e in (\<lambda>k. rely r \<iinter> (\<lbrace>expr_eq e k\<rbrace> ; c k))"
      by (rule rely_into_bind)
    finally show ?thesis.
  qed
  have pointwise:
    "bind e in (\<lambda>k. rely r \<iinter> (\<lbrace>expr_eq e k\<rbrace> ; c k)) \<ge>\<^sub>I bind e in d"
    by (rule data_refine_bind_mono'[OF step])
  show ?thesis
    using expand pointwise by simp
qed

lemma data_refine_rely_bindlv:
  assumes step:
    "\<And>lv. rely r \<iinter> \<lbrace>lval_eq lve lv\<rbrace> ; c lv \<ge>\<^sub>I d lv"
  shows "rely r \<iinter> (bindlv lve in c) \<ge>\<^sub>I bindlv lve in d"
proof -
  have expand:
    "rely r \<iinter> (bindlv lve in c) = bindlv lve in (\<lambda>lv. rely r \<iinter> (\<lbrace>lval_eq lve lv\<rbrace> ; c lv))"
  proof -
    have "bindlv lve in c = bindlv lve in (\<lambda>lv. \<lbrace>lval_eq lve lv\<rbrace> ; c lv)"
      using bindlv_var_is_lval_eval by simp
    then have "rely r \<iinter> (bindlv lve in c) =
        rely r \<iinter> bindlv lve in (\<lambda>lv. \<lbrace>lval_eq lve lv\<rbrace> ; c lv)"
      by (rule arg_cong)
    also have "\<dots> = bindlv lve in (\<lambda>lv. rely r \<iinter> (\<lbrace>lval_eq lve lv\<rbrace> ; c lv))"
      by (rule rely_into_bindlv)
    finally show ?thesis .
  qed
  have pointwise:
    "bindlv lve in (\<lambda>lv. rely r \<iinter> (\<lbrace>lval_eq lve lv\<rbrace> ; c lv)) \<ge>\<^sub>I bindlv lve in d"
    by (rule data_refine_bindlv_mono'[OF step])
  show ?thesis
    using expand pointwise by simp
qed

text \<open>Convenience forms of the dependent bind rules when only one
body depends on the value selected by the bind.\<close>
lemma data_refine_rely_bind_lhs_const:
  assumes step: "\<And>k. rely r \<iinter> \<lbrace>expr_eq e k\<rbrace> ; c \<ge>\<^sub>I d k"
  shows "rely r \<iinter> c \<ge>\<^sub>I bind e in d"
proof -
  have "rely r \<iinter> (bind e in (\<lambda>k. c)) \<ge>\<^sub>I bind e in d"
    by (rule data_refine_rely_bind[where c = "\<lambda>k. c", OF step])
  then show ?thesis
    by (simp add: bind_introduce)
qed

lemma data_refine_rely_bind_rhs_const:
  assumes step: "\<And>k. rely r \<iinter> \<lbrace>expr_eq e k\<rbrace> ; c k \<ge>\<^sub>I d"
  shows "rely r \<iinter> (bind e in c) \<ge>\<^sub>I d"
proof -
  have "rely r \<iinter> (bind e in c) \<ge>\<^sub>I bind e in (\<lambda>k. d)"
    by (rule data_refine_rely_bind[where d = "\<lambda>k. d", OF step])
  then show ?thesis
    by (simp add: bind_introduce)
qed

lemma data_refine_rely_bindlv_lhs_const:
  assumes step: "\<And>lv. rely r \<iinter> \<lbrace>lval_eq lve lv\<rbrace> ; c \<ge>\<^sub>I d lv"
  shows "rely r \<iinter> c \<ge>\<^sub>I bindlv lve in d"
proof -
  have "rely r \<iinter> (bindlv lve in (\<lambda>lv. c)) \<ge>\<^sub>I bindlv lve in d"
    by (rule data_refine_rely_bindlv[where c = "\<lambda>lv. c", OF step])
  then show ?thesis
    by (simp add: bindlv_introduce)
qed

lemma data_refine_rely_bindlv_rhs_const:
  assumes step: "\<And>lv. rely r \<iinter> \<lbrace>lval_eq lve lv\<rbrace> ; c lv \<ge>\<^sub>I d"
  shows "rely r \<iinter> (bindlv lve in c) \<ge>\<^sub>I d"
proof -
  have "rely r \<iinter> (bindlv lve in c) \<ge>\<^sub>I bindlv lve in (\<lambda>lv. d)"
    by (rule data_refine_rely_bindlv[where d = "\<lambda>lv. d", OF step])
  then show ?thesis
    by (simp add: bindlv_introduce)
qed

text \<open>Both-constant specialisations of the dependent data-refinement
bind rules.\<close>
lemma data_refine_ref_if_ref_expr_evals_both_const:
  assumes all_consts_ref: "\<And>k. rely r \<iinter> \<lbrace>expr_eq e k\<rbrace> ; c \<ge>\<^sub>I d"
  shows "rely r \<iinter> c \<ge>\<^sub>I d"
proof -
  have "rely r \<iinter> c \<ge>\<^sub>I bind e in (\<lambda>k. d)"
    by (rule data_refine_rely_bind_lhs_const [where d = "\<lambda>k. d", OF all_consts_ref])
  then show ?thesis
    by (simp add: bind_introduce)
qed

lemma data_refine_ref_if_ref_lval_evals_both_const:
  assumes all_lvals_ref: "\<And>lv. rely r \<iinter> \<lbrace>lval_eq lve lv\<rbrace> ; c \<ge>\<^sub>I d"
  shows "rely r \<iinter> c \<ge>\<^sub>I d"
proof -
  have "rely r \<iinter> c \<ge>\<^sub>I bindlv lve in (\<lambda>lv. d)"
    by (rule data_refine_rely_bindlv_lhs_const [where d = "\<lambda>lv. d", OF all_lvals_ref])
  then show ?thesis
    by (simp add: bindlv_introduce)
qed

(*Remove Data Refinement Example*)
section \<open>Example: Remove an element from a set\<close>

theory Remove
  imports Typed_State Commands.Data_Refinement
begin

fun extract_set_from_word :: "64 word \<Rightarrow> nat set"
  where "extract_set_from_word w = {i::nat. bit w i}"

text \<open>Lift operations to operate on \<open>typed_values\<close>\<close>
abbreviation word_bit where
  "word_bit \<equiv> lift2 as_word64 as_nat BoolValue bit"

abbreviation word_unset_bit where
  "word_unset_bit \<equiv> lift2 as_word64 as_nat Word64Value (\<lambda>w i. unset_bit i w)"

abbreviation set_difference where
  "set_difference \<equiv> lift2 as_nat_set as_nat_set NatSetValue (-)"

abbreviation set_member where
  "set_member \<equiv> lift2 as_nat_set as_nat BoolValue (\<lambda>s i. i \<in> s)"

abbreviation extract_set_from_word_val where
  "extract_set_from_word_val \<equiv> lift1 as_word64 NatSetValue extract_set_from_word"

lemma extract_set_from_word_unset_bit:
  "extract_set_from_word (unset_bit i W) = extract_set_from_word W - {i}"
  by (auto simp: bit_unset_bit_iff)

context typed_frame_state
begin

text \<open>Define variables. The getter is \<open>s\<close> or \<open>w\<close>;
the corresponding l-value and l-value expression are \<open>s_lval\<close>,
\<open>s_lve\<close>, \<open>w_lval\<close>, and \<open>w_lve\<close>.\<close>
define_var s
define_var w

text \<open>Coupling invariant: nats in the set correspond to set bits in the word.\<close>
definition I :: "'state set" where
  "I = \<llangle>\<exists>S W.
      \<acute>s = NatSetValue S \<and>
      \<acute>w = Word64Value W \<and>
      S = extract_set_from_word W\<rrangle>"

text \<open>Helper lemmas\<close>
lemma I_w_eval_sub_s_eval: "I \<inter> expr_eq (*Var ''w'') k \<subseteq> expr_eq (*Var ''s'') (extract_set_from_word_val k)"
proof-
  have "I \<inter> expr_eq (*Var ''w'') k = \<llangle>\<exists>S W.
        \<acute>s = NatSetValue S \<and>
        \<acute>w = Word64Value W \<and>
        S = extract_set_from_word W \<and>
        \<acute>w = k\<rrangle>"
  by (auto simp: I_def expr_eq_def w_def w_lval_def)
  also have "\<dots> = \<llangle>\<exists>S W.
      \<acute>s = NatSetValue S \<and>
      \<acute>w = Word64Value W \<and>
      S = extract_set_from_word W \<and>
      \<acute>w = k \<and>
      \<acute>s = extract_set_from_word_val k\<rrangle>"
    by auto
  also have "\<dots> \<subseteq> \<llangle>\<acute>s = extract_set_from_word_val k\<rrangle>"
    (is "_ \<subseteq> ?rhs")
    by auto
  also have "?rhs = expr_eq (*Var ''s'') (extract_set_from_word_val k)"
    by (auto simp: expr_eq_def s_def s_lval_def)
  finally show ?thesis
    by blast
qed

lemma w_extracted_set_refines_s_test: "\<tau> (expr_eq (*s_lve) (extract_set_from_word_val k)) \<ge>\<^sub>I \<tau> (expr_eq (*w_lve) k)"
  unfolding w_lve_def s_lve_def
  using data_refine_test I_w_eval_sub_s_eval by auto

lemma w_extracted_set_refines_s: "\<lblot>*s_lve\<rblot>(extract_set_from_word_val k) \<ge>\<^sub>I \<lblot>*w_lve\<rblot>k"
proof -
  have base_refinement:
    "\<lblot>*Var ''s''\<rblot>(extract_set_from_word_val k) \<ge>\<^sub>I \<lblot>*Var ''w''\<rblot>k"
    using data_refine_variable I_w_eval_sub_s_eval by auto

  then show ?thesis
    by (simp add: s_lve_def w_lve_def)
qed

lemma removal_equivalence:
  "set_difference (extract_set_from_word_val wo) (NatSetValue {i}) =
   extract_set_from_word_val (word_unset_bit wo (NatValue i))"
  apply (cases wo; auto_undefined_types)
  using extract_set_from_word_unset_bit by auto

lemma const_expr_equiv: "expr_eq (Constant (word_unset_bit oldw (NatValue i))) neww
      \<subseteq> expr_eq (Constant (set_difference (extract_set_from_word_val oldw) (NatSetValue {i}))) (extract_set_from_word_val neww)"
  using expr_eq_def removal_equivalence by auto

text \<open>Refinement proof\<close>
lemma refine_remove_from_set:
  "while Binary set_member (*s_lve) (Constant (NatValue i)) do
     bind (*s_lve) in (\<lambda>olds.
       bind (Constant (set_difference olds (NatSetValue {i}))) in (\<lambda>news.
         {|s_lval,w_lval|}:\<^sub>s\<langle>\<top>,
            \<llangle>(\<ordmasculine>s = olds \<longrightarrow> \<ordfeminine>s = news) \<and>
            (\<ordmasculine>s \<noteq> olds \<longrightarrow> \<ordfeminine>s = \<ordmasculine>s)\<rrangle>\<rangle>))
   od \<ge>\<^sub>I
   while Binary word_bit (*w_lve) (Constant (NatValue i)) do
     bind (*w_lve) in (\<lambda>oldw.
       bind (Constant (word_unset_bit oldw (NatValue i))) in (\<lambda>neww.
         {|s_lval,w_lval|}:\<^sub>s\<langle>\<top>,
            \<llangle>(\<ordmasculine>w = oldw \<longrightarrow> \<ordfeminine>w = neww) \<and>
            (\<ordmasculine>w \<noteq> oldw \<longrightarrow> \<ordfeminine>w = \<ordmasculine>w)\<rrangle>\<rangle>))
    od"
proof (rule data_refine_while_alt)
  let ?frame = "{|s_lval, w_lval|}"
  let ?set_rel = "\<lambda>olds news.
    \<llangle>(\<ordmasculine>s = olds \<longrightarrow> \<ordfeminine>s = news) \<and>
      (\<ordmasculine>s \<noteq> olds \<longrightarrow>
       \<ordfeminine>s = \<ordmasculine>s)\<rrangle>"
  let ?word_rel = "\<lambda>oldw neww.
    \<llangle>(\<ordmasculine>w = oldw \<longrightarrow> \<ordfeminine>w = neww) \<and>
      (\<ordmasculine>w \<noteq> oldw \<longrightarrow>
       \<ordfeminine>w = \<ordmasculine>w)\<rrangle>"
  let ?set_update_atomic = "\<lambda>olds news. ?frame :\<^sub>s \<langle>\<top>, ?set_rel olds news\<rangle>"
  let ?word_update_atomic = "\<lambda>oldw neww. ?frame :\<^sub>s \<langle>\<top>, ?word_rel oldw neww\<rangle>"

  have binary_op_cond: "\<forall> k1' k2'. \<exists>k1 k2. set_member k1 k2 = word_bit k1' k2'
                                           \<and> (\<lblot>*s_lve\<rblot>k1 \<ge>\<^sub>I \<lblot>*w_lve\<rblot>k1')
                                           \<and> (\<lblot>Constant (NatValue i)\<rblot>k2 \<ge>\<^sub>I \<lblot>Constant (NatValue i)\<rblot>k2')"
  proof (intro allI)
    fix k1' k2' :: typed_value
    let ?k1 = "extract_set_from_word_val k1'"
    let ?k2 = "k2'"
    show "\<exists>k1 k2. set_member k1 k2 = word_bit k1' k2' \<and>
        (\<lblot>*s_lve\<rblot>k1 \<ge>\<^sub>I \<lblot>*w_lve\<rblot>k1') \<and>
        (\<lblot>Constant (NatValue i)\<rblot>k2 \<ge>\<^sub>I \<lblot>Constant (NatValue i)\<rblot>k2')"
      apply (rule exI[where x = ?k1], rule exI[where x = ?k2])
      proof (intro conjI)
        show "set_member ?k1 ?k2 = word_bit k1' k2'"
          by (cases k1'; cases k2'; simp)
      
        show "\<lblot>*s_lve\<rblot>?k1 \<ge>\<^sub>I \<lblot>*w_lve\<rblot>k1'"
          using w_extracted_set_refines_s by auto

        show "\<lblot>Constant (NatValue i)\<rblot>?k2 \<ge>\<^sub>I \<lblot>Constant (NatValue i)\<rblot>k2'"
          by (simp add: data_refine_refl)
      qed
    qed

  show "\<And>k. \<lblot>Binary set_member (*s_lve) (Constant (NatValue i))\<rblot>k
         \<ge>\<^sub>I \<lblot>Binary word_bit (*w_lve) (Constant (NatValue i))\<rblot>k"
    using binary_op_cond by (rule data_refine_binary)

  show "bind (*s_lve)
    in (\<lambda>olds. bind (Constant (set_difference olds (NatSetValue {i})))
           in (\<lambda>news. ?set_update_atomic olds news)) \<ge>\<^sub>I bind (*w_lve)
    in (\<lambda>oldw. bind (Constant (word_unset_bit oldw (NatValue i)))
           in (\<lambda>neww. ?word_update_atomic oldw neww))"
  proof (rule data_refine_bind)
    fix oldw :: typed_value
    let ?olds = "extract_set_from_word_val oldw"

    show "\<exists>k1. \<tau> (expr_eq (*s_lve) k1) ;
              bind (Constant (set_difference k1 (NatSetValue {i})))
                in (\<lambda>news. ?set_update_atomic k1 news)
           \<ge>\<^sub>I \<tau> (expr_eq (*w_lve) oldw) ;
              bind (Constant (word_unset_bit oldw (NatValue i)))
                in (\<lambda>neww. ?word_update_atomic oldw neww)"
      apply (rule exI[where x = "?olds"])
      apply (rule data_refine_seq)
      subgoal text \<open>left refines\<close>
        using w_extracted_set_refines_s_test by auto
      subgoal text \<open>right refines\<close>
        proof (rule data_refine_bind)
        fix neww :: typed_value
        let ?news = "extract_set_from_word_val neww"

        show "\<exists>k1. \<tau> (expr_eq (Constant (set_difference (extract_set_from_word_val oldw) (NatSetValue {i}))) k1) ;
                ?set_update_atomic (extract_set_from_word_val oldw) k1 \<ge>\<^sub>I
                \<tau> (expr_eq (Constant (word_unset_bit oldw (NatValue i))) neww);
                ?word_update_atomic oldw neww"
          apply (rule exI[where x = "?news"])
          apply (rule data_refine_seq)
          subgoal text \<open>left refines\<close>
            using data_refine_test const_expr_equiv
            by (simp add: refsto_implies_data_refine seq.test_mono) 
          subgoal text \<open>right refines\<close>
            apply (rule data_refine_frame_mono)
            apply (rule data_refine_atomic_spec)
            subgoal by simp
            subgoal
              proof (rule subsetI)
                fix x::"'state \<times> 'state"
                
                assume in_left: "x \<in> (I \<inter> UNIV) \<triangleleft>
                         ?word_rel oldw neww \<triangleright> I"

                have remove_success: "w (fst x) = oldw \<longrightarrow>
                    w (snd x) = neww"
                  using domain_restrict_remove in_left range_restrict_remove by fastforce

                have remove_fail: "w (fst x) \<noteq> oldw \<longrightarrow>
                    w (snd x) = w (fst x)"
                  using domain_restrict_remove in_left range_restrict_remove by fastforce

                have pre_I: "fst x \<in> I"
                  using in_left
                  by (auto simp: restrict_domain_def restrict_range_def)
                
                have post_I: "snd x \<in> I"
                  using in_left
                  by (auto simp: restrict_domain_def restrict_range_def)
              
                obtain S\<^sub>0 W\<^sub>0 where
                  pre_s: "s (fst x) = NatSetValue S\<^sub>0" and
                  pre_w: "w (fst x) = Word64Value W\<^sub>0" and
                  pre_bitset: "S\<^sub>0 = extract_set_from_word W\<^sub>0"
                  using pre_I
                  unfolding I_def
                  by auto
              
                obtain S\<^sub>1 W\<^sub>1 where
                  post_s: "s (snd x) = NatSetValue S\<^sub>1" and
                  post_w: "w (snd x) = Word64Value W\<^sub>1" and
                  post_bitset: "S\<^sub>1 = extract_set_from_word W\<^sub>1"
                  using post_I
                  unfolding I_def
                  by auto
              
                have pre_coupling:
                  "s (fst x) =
                   extract_set_from_word_val (w (fst x))"
                  using pre_s pre_w pre_bitset
                  by simp
              
                have post_coupling:
                  "s (snd x) =
                   extract_set_from_word_val (w (snd x))"
                  using post_s post_w post_bitset
                  by simp

                have s_w_bijection:
                  "s (fst x) = extract_set_from_word_val oldw
                    \<longleftrightarrow> w (fst x) = oldw"
                proof
                  assume asm: "s (fst x) = extract_set_from_word_val oldw"
                  have extract1: "extract_set_from_word_val (Word64Value W\<^sub>0) =
                      extract_set_from_word_val oldw"
                    using asm pre_coupling pre_w by simp
                  obtain W where oldw_word: "oldw = Word64Value W"
                   using extract1 by (cases oldw; simp)
                  have bit_sets: "{i::nat. bit W\<^sub>0 i} = {i. bit W i}"
                    using extract1 oldw_word by simp
                  then have "\<And>i::nat. bit W\<^sub>0 i = bit W i"
                    by auto
                  then have W_eq: "W\<^sub>0 = W"
                    by (rule bit_eqI)
                  then show "w (fst x) = oldw"
                    using pre_w oldw_word W_eq by simp
                next
                  assume asm: "w (fst x) = oldw"
                  show "s (fst x) = extract_set_from_word_val oldw"
                    using asm pre_coupling by simp
                qed

                have cond_1:
                  "s (fst x) = extract_set_from_word_val oldw
                    \<longrightarrow> s (snd x) = extract_set_from_word_val neww"
                proof (rule impI)
                  assume asm: "s (fst x) = extract_set_from_word_val oldw"
                  have pre_oldw: "w (fst x) = oldw"
                    using s_w_bijection asm by blast
                  have post_neww: "w (snd x) = neww"
                    using remove_success pre_oldw by simp
                  show "s (snd x) = extract_set_from_word_val neww"
                    using post_coupling post_neww by simp
                qed

                have cond_2:
                  "s (fst x) \<noteq> extract_set_from_word_val oldw
                    \<longrightarrow> s (snd x) = s (fst x)"
                proof (rule impI)
                  assume asm: "s (fst x) \<noteq> extract_set_from_word_val oldw"
                  have pre_not_oldw: "w (fst x) \<noteq> oldw"
                    using s_w_bijection asm by blast
                  have post_same_w: "w (snd x) = w (fst x)"
                    using remove_fail pre_not_oldw by simp
                  show "s (snd x) = s (fst x)"
                    using post_coupling pre_coupling post_same_w by simp
                qed

                show "x \<in> (I \<inter> UNIV) \<triangleleft> ?word_rel oldw neww \<triangleright> I \<Longrightarrow>
                    x \<in> ?set_rel (extract_set_from_word_val oldw)
                      (extract_set_from_word_val neww)"
                  by (simp add: cond_1 cond_2)
              qed
            done
          done
        qed
      done
    qed
  qed
end
end



end
end
