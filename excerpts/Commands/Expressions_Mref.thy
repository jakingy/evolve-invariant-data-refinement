(* Extracts from isabelle/new_rg_algebra/Commands/Expressions_Mref.thy. *)
(* These are source excerpts, not a standalone buildable theory. *)

(* Original lines 19-23. *)
text \<open>Constants are the base case for expression evaluation.\<close>
lemma post_constant: 
  assumes stable_p: "stable p r"
  shows "{. p .} rely r \<iinter> \<lblot>Constant \<kappa>\<rblot>k {. p \<inter> {\<sigma>. \<kappa> = k} .}"  
  using rely_idle_stable_assert seq_conj.assert_sync_Sup stable_p triple_with_rely by fastforce


(* Original lines 25-34. *)
lemma post_constant_univ: "{. p .} rely r \<iinter> \<lblot>Constant \<kappa>\<rblot>k {. {\<sigma>. \<kappa> = k} .}"
proof-
  have stable_univ: "stable UNIV r" by simp
  have univ_int: "UNIV \<inter> {\<sigma>. \<kappa> = k} = {\<sigma>. \<kappa> = k}" by simp
  have p_lt: "p \<subseteq> UNIV" by blast
  have "{. UNIV .} rely r \<iinter> \<lblot>Constant \<kappa>\<rblot>k {. {\<sigma>. \<kappa> = k} .}"
    using post_constant univ_int stable_univ by metis
  then show ?thesis
    using p_lt seq.triple_consequence_pre by presburger 
qed


(* Original lines 48-57. *)
lemma post_variable_univ: "{. p .} rely r \<iinter> \<ltort>Var v\<rtort>lv {. {\<sigma>. lv = Base v} .}"  
proof -
  have stable_univ: "stable UNIV r" by simp
  have univ_int: "UNIV \<inter> {\<sigma>. lv = Base v} = {\<sigma>. lv = Base v}" by simp
  have p_lt: "p \<subseteq> UNIV" by blast
  have "{. UNIV .} rely r \<iinter> \<ltort>Var v\<rtort>lv {. {\<sigma>. lv = Base v} .}"
    using post_variable univ_int stable_univ by metis
  then show ?thesis
    using p_lt seq.triple_consequence_pre by presburger 
qed


(* Original lines 243-265. *)
text \<open>If an expression is invariant under the rely restricted to the stable
precondition \<open>p\<close>, the postcondition can be taken to be
\<open>p \<inter> \<lfloor>e = k\<rfloor>\<close>.  A similar property holds for l-value
expressions.\<close>
lemma stable_inter_restrict:
  assumes stable_p: "stable p r"
  assumes stable_q: "stable q (p \<triangleleft> r \<triangleright> p)"
  shows "stable (p \<inter> q) r"
proof (rule subsetI)
  fix \<sigma>'
  assume \<sigma>'_in: "\<sigma>' \<in> r `` (p \<inter> q)"
  obtain \<sigma> where \<sigma>_in: "\<sigma> \<in> p \<inter> q" and step: "(\<sigma>, \<sigma>') \<in> r"
    using \<sigma>'_in by auto
  have \<sigma>'_in_p: "\<sigma>' \<in> p"
    using stable_p \<sigma>_in step by auto
  have restricted_step: "(\<sigma>, \<sigma>') \<in> p \<triangleleft> r \<triangleright> p"
    using \<sigma>_in \<sigma>'_in_p step
    by (simp add: restrict_domain_def restrict_range_def)
  have \<sigma>'_in_q: "\<sigma>' \<in> q"
    using stable_q \<sigma>_in restricted_step by auto
  show "\<sigma>' \<in> p \<inter> q"
    using \<sigma>'_in_p \<sigma>'_in_q by auto
qed


(* Original lines 267-366. *)
lemma post_expr_invariant_rely_pre:
  assumes refl_r: "refl r"
  assumes stable_p: "stable p r"
  shows "invar_expr e (p \<triangleleft> r \<triangleright> p) \<Longrightarrow> (\<And>k::'v. {. p .} rely r \<iinter> \<lblot>e\<rblot>k {. p \<inter> expr_eq e k .})"
    and "invar_lval lve (p \<triangleleft> r \<triangleright> p) \<Longrightarrow> (\<And>lv::'v LValue. {. p .} rely r \<iinter> \<ltort>lve\<rtort>lv {. p \<inter> lval_eq lve lv .})"
proof (induction e and lve)
  case (Constant \<kappa>) 
  then show ?case 
    using eval_expr.simps(1) expr_eq_def post_constant stable_p by presburger 
next
  case (Deref lve)
  then show ?case 
  proof -
    have stable_P1: "\<And>lv. stable (p \<inter> lval_eq lve lv) r"
      by (meson Deref.prems invar_expr.simps(2) invar_lval_stable
          stable_inter_restrict stable_p)
    have stable_P: "stable (p \<inter> expr_eq (Deref lve) k) r" 
      by (meson Deref.prems invar_expr_stable stable_inter_restrict stable_p)
    have establish_P1: "\<And>lv. {. p .} rely r \<iinter> \<ltort>lve\<rtort>lv {. p \<inter> lval_eq lve lv .}" 
      using Deref.IH Deref.prems invar_expr.simps(2) by blast
    have establish_P: "\<And>lv. p \<inter> lval_eq lve lv \<inter> {\<sigma>. get lv \<sigma> = k} \<subseteq> p \<inter> expr_eq (Deref lve) k"
      unfolding lval_eq_def expr_eq_def eval_expr.simps by blast
    show ?thesis 
      using post_deref[where P = "\<lambda>k. p \<inter> expr_eq (Deref lve) k" and ?P1.0 = "\<lambda>lv. p \<inter> lval_eq lve lv"]
      stable_p stable_P1 stable_P establish_P1 establish_P by blast
  qed
next
  case (Unary unop e1)
  then show ?case 
  proof -
    have sub_expr: "\<And>k1. {. p .} rely r \<iinter> \<lblot>e1\<rblot>k1 {. p \<inter> expr_eq e1 k1 .}" 
      using Unary.IH Unary.prems invar_expr.simps(3) by blast
    have P1_implies_P: "\<And>k1. unop k1 = k \<Longrightarrow> p \<inter> expr_eq e1 k1 \<subseteq> p \<inter> expr_eq (Unary unop e1) k" 
      using unary_eval_contains by force 
    show ?thesis using post_unary[where ?P1.0 = "\<lambda>k1. p \<inter> expr_eq e1 k1"] 
      by (meson P1_implies_P sub_expr) 
  qed
next
  case (Binary binop e1 e2)
  then show ?case
  proof -
    have sub_expr1: "\<And>k1. {. p .} rely r \<iinter> \<lblot>e1\<rblot>k1 {. p \<inter> expr_eq e1 k1 .}" 
      using Binary.IH(1) Binary.prems by force
    have sub_expr2: "\<And>k2. {. p .} rely r \<iinter> \<lblot>e2\<rblot>k2 {. p \<inter> expr_eq e2 k2 .}" 
      using Binary.IH(2) Binary.prems by force
    have P1P2_implies_P: "\<And>k1 k2. binop k1 k2 = k \<Longrightarrow> 
                p \<inter> expr_eq e1 k1 \<inter> expr_eq e2 k2 \<subseteq> p \<inter> expr_eq (Binary binop e1 e2) k" 
      by (metis binary_eval_contains boolean_algebra_cancel.inf1 inf_mono order_refl)
    show ?thesis
      using post_binary[where ?P1.0 = "\<lambda>k1. p \<inter> expr_eq e1 k1" and ?P2.0 = "\<lambda>k2. p \<inter> expr_eq e2 k2"
          and P = "\<lambda>k. p \<inter> expr_eq (Binary binop e1 e2) k"] sub_expr1 sub_expr2 P1P2_implies_P 
      using refl_r by blast 
  qed
next
  case (Var v)
  then show ?case  
  proof (cases "lv = Base v")
    case True
    then show ?thesis 
    proof -
      have "{. p .} rely r \<iinter> \<ltort>Var v\<rtort> (Base v) {. p .}" 
        using rely_lval_stable_triple stable_p by blast
      then have "{. p .} rely r \<iinter> \<ltort>Var v\<rtort> (Base v) {. p \<inter> lval_eq (Var v) (Base v) .}" 
        by (simp add: lval_eq_def)
      then show ?thesis by (simp add: True) 
    qed
  next
    case False
    then show ?thesis using triple_Sup_with_rely by force
  qed
next
  case (ArrayRef lve e)
  then show ?case
  proof (cases lv)
    case (Base v)
    then show ?thesis 
      by (meson empty_subsetI post_array_ref_base seq.triple_consequence_post) 
  next
    case (Indexed A i)
    then show ?thesis 
    proof -
      have lve: "{. p .} rely r \<iinter> \<ltort>lve\<rtort>A {. p \<inter> lval_eq lve A .}" 
        using ArrayRef.IH(1) ArrayRef.prems by force
      have e: "{. p .} rely r \<iinter> \<lblot>e\<rblot>i {. p \<inter> expr_eq e i .}" 
        using ArrayRef.IH(2) ArrayRef.prems by force
      have P: "(p \<inter> lval_eq lve A \<inter> expr_eq e i \<subseteq> p \<inter> lval_eq (ArrayRef lve e) lv)"
      proof -
        have "p \<inter> lval_eq lve A \<inter> expr_eq e i = p \<inter> {\<sigma>. [[lve]]\<sigma> = A \<and> \<lbrakk>e\<rbrakk>\<sigma> = i}" 
          by (simp add: Int_def expr_eq_def lval_eq_def) 
        also have "\<dots> \<subseteq> p \<inter> lval_eq (ArrayRef lve e) lv"
          by (simp add: Indexed lval_eq_def) 
        finally show "p \<inter> lval_eq lve A \<inter> expr_eq e i \<subseteq> p \<inter> lval_eq (ArrayRef lve e) lv" . 
      qed
    show ?thesis 
      using post_array_ref[where ?P1.0 = "\<lambda>A. p \<inter> lval_eq lve A" and ?P2.0 = "\<lambda>i. p \<inter> expr_eq e i"
          and ?P = "\<lambda>lv. p \<inter> lval_eq (ArrayRef lve e) lv"] refl_r lve e P Indexed 
      by blast
    qed
  qed
qed


(* Original lines 368-391. *)
lemma invar_expr_antimono_r:
  assumes r_subset: "r1 \<subseteq> r2"
  shows "invar_expr e r2 \<Longrightarrow> invar_expr e r1"
    and "invar_lval lve r2 \<Longrightarrow> invar_lval lve r1"
proof (induction e and lve)
  case (Constant \<kappa>)
  then show ?case by simp
next
  case (Deref lve)
  then show ?case
    using r_subset by auto 
next
  case (Unary unop e1)
  then show ?case by auto
next
  case (Binary binop e1 e2)
  then show ?case by auto
next
  case (Var v)
  then show ?case by simp
next
  case (ArrayRef lve e)
  then show ?case by auto
qed


(* Original lines 393-407. *)
lemma post_expr_invariant:
  assumes refl_r: "refl r"
  assumes stable_p: "stable p r"
  shows "invar_expr e r \<Longrightarrow> (\<And>k::'v. {. p .} rely r \<iinter> \<lblot>e\<rblot>k {. p \<inter> expr_eq e k .})"
    and "invar_lval lve r \<Longrightarrow> (\<And>lv::'v LValue. {. p .} rely r \<iinter> \<ltort>lve\<rtort>lv {. p \<inter> lval_eq lve lv .})"
proof -
  have restrict_subset: "p \<triangleleft> r \<triangleright> p \<subseteq> r"
    unfolding restrict_domain_def restrict_range_def by auto
  show "invar_expr e r \<Longrightarrow> (\<And>k::'v. {. p .} rely r \<iinter> \<lblot>e\<rblot>k {. p \<inter> expr_eq e k .})"
    using post_expr_invariant_rely_pre(1)[OF refl_r stable_p]
      invar_expr_antimono_r(1)[OF restrict_subset] by blast
  show "invar_lval lve r \<Longrightarrow> (\<And>lv::'v LValue. {. p .} rely r \<iinter> \<ltort>lve\<rtort>lv {. p \<inter> lval_eq lve lv .})"
    using post_expr_invariant_rely_pre(2)[OF refl_r stable_p]
      invar_expr_antimono_r(2)[OF restrict_subset] by blast
qed


(* Original lines 409-413. *)
lemma post_expr_invariant_expr_eq_intersect:
  assumes refl_r: "refl r"
  assumes invar_e: "invar_expr e r"
  shows "{. expr_eq e k1 .} rely r \<iinter> \<lblot>e\<rblot>k2 {. expr_eq e k1 \<inter> expr_eq e k2 .}"
  by (simp add: invar_expr_stable post_expr_invariant(1) refl_r invar_e)


(* Original lines 415-422. *)
lemma post_lval_invariant_lval_eq_intersect:
  assumes refl_r: "refl r"
  assumes invar_lve: "invar_lval lve r"
  shows "{. lval_eq lve lv1 .} rely r \<iinter> \<ltort>lve\<rtort>lv2
    {. lval_eq lve lv1 \<inter> lval_eq lve lv2 .}"
  by (simp add: invar_lval_stable post_expr_invariant(2) refl_r invar_lve)

(*TODO move these laws into lower theory*)


(* Original lines 423-458. *)
lemma triple_refine_nonaborting_conj_same_aborting:
  assumes nonabort_a: "chaos \<ge> a"
  assumes a_refines_b: "a \<ge> b"
  assumes a_triple: "{. p .} c \<iinter> a {. q .}"
  shows "{. p .} c \<iinter> b {. q .}"
proof -
 have a_conj_b: "a \<iinter> b = b"
    using nonabort_a a_refines_b
    by (rule conj.nonaborting_conj_of_to)

  have pre_expand: "\<lbrace>p\<rbrace> ; (c \<iinter> b) = (\<lbrace>p\<rbrace> ; (c \<iinter> a)) \<iinter> b"
    by (simp add: a_conj_b seq_conj.assert_op_sync_left seq_conj.sync_assoc)

  have refine_middle: "(\<lbrace>p\<rbrace> ; (c \<iinter> a)) \<iinter> b \<ge> ((c \<iinter> a) ; \<lbrace>q\<rbrace>) \<iinter> b"
    using a_triple
    unfolding seq.Hoare_triple_def
    by (rule seq_conj.sync_mono_left)

  have establish_post: "((c \<iinter> a) ; \<lbrace>q\<rbrace>) \<iinter> b \<ge> (c \<iinter> b) ; \<lbrace>q\<rbrace>"
  proof -
    have "((c \<iinter> a) ; \<lbrace>q\<rbrace>) \<iinter> b = ((c \<iinter> a) ; \<lbrace>q\<rbrace>) \<iinter> (b ; \<lbrace>\<top>\<rbrace>)"
      by (simp add: seq.assert_neut)
    also have "\<dots> \<ge> (c \<iinter> a \<iinter> b) ; \<lbrace>q \<inter> \<top>\<rbrace>" (is "_ \<ge> ?rhs")
      by (rule seq_conj.op_assert_sync_op_assert_to)
    also have "?rhs = (c \<iinter> b) ; \<lbrace>q\<rbrace>"
      by (simp add: a_conj_b seq_conj.sync_assoc)
    finally show ?thesis .
  qed

  have "\<lbrace>p\<rbrace> ; (c \<iinter> b) \<ge> ((c \<iinter> a) ; \<lbrace>q\<rbrace>) \<iinter> b"
    using pre_expand refine_middle by simp
  then have "\<lbrace>p\<rbrace> ; (c \<iinter> b) \<ge> (c \<iinter> b) ; \<lbrace>q\<rbrace>"
    using establish_post by order
  then show ?thesis
    unfolding seq.Hoare_triple_def .  
qed


(* Original lines 460-472. *)
lemma triple_refine_nonaborting:
  assumes nonabort_a: "chaos \<ge> a"
  assumes a_refines_b: "a \<ge> b"
  assumes a_triple: "{. p .} a {. q .}"
  shows "{. p .} b {. q .}"
proof -
  have ca: "chaos \<iinter> a = a" by simp
  then have "{. p .} chaos \<iinter> a {. q .}"
    by (simp add: a_triple)
  then have "{. p .} chaos \<iinter> b {. q .}"
    using a_refines_b nonabort_a triple_refine_nonaborting_conj_same_aborting by blast
  then show ?thesis by simp
qed


(* Original lines 474-482. *)
lemma triple_nil_pre_subset_post: 
  assumes triple_nil: "{. p .} nil {. q .}"
  shows "p \<subseteq> q"
proof-
  have "\<lbrace>p\<rbrace> \<ge> \<lbrace>q\<rbrace>" using triple_nil seq.Hoare_triple_def
    by simp 
  then show ?thesis
    by (simp add: seq.assert_to_assert_equiv) 
qed


(* Original lines 484-493. *)
lemma triple_nil_refines_nonaborting_pre_subset_post:
  assumes nonabort_a: "chaos \<ge> a"
  assumes a_refines_nil: "a \<ge> nil"
  assumes a_triple: "{. p .} a {. q .}"
  shows "p \<subseteq> q"
proof-
  have "{. p .} nil {. q .}" 
    using triple_refine_nonaborting nonabort_a a_refines_nil a_triple by simp
  then show ?thesis using triple_nil_pre_subset_post by simp
qed


(* Original lines 495-502. *)
lemma triple_nil_refines_nonaborting_pre_subset_post_conj:
  assumes nonabort_a: "chaos \<ge> a"
  assumes conj_nil_nil: "c \<iinter> nil = nil"
  assumes a_refines_nil: "a \<ge> nil"
  assumes a_triple: "{. p .} c \<iinter> a {. q .}"
  shows "p \<subseteq> q"
  using assms triple_nil_refines_nonaborting_pre_subset_post
  by (metis triple_nil_pre_subset_post triple_refine_nonaborting_conj_same_aborting)


(* Original lines 504-579. *)
lemma expr_cmd_equiv_constant_under_invar:
  assumes refl_r: "refl r"
  assumes invar_e: "invar_expr e r"
  shows "{. expr_eq e k1 .} rely r \<iinter> \<lblot>e\<rblot>k2 {. q .} 
\<longleftrightarrow> {. expr_eq e k1 .} rely r \<iinter> \<lblot>Constant k1\<rblot>k2 {. q .}"
proof-
  let ?Pconst = "\<lambda>q. {. expr_eq e k1 .} rely r \<iinter> \<lblot>Constant k1\<rblot>k2 {. q .}"
  let ?Pe = "\<lambda>q. {. expr_eq e k1 .} rely r \<iinter> \<lblot>e\<rblot>k2 {. q .}"

  have post_e: "?Pe (expr_eq e k1 \<inter> expr_eq e k2)"
    using post_expr_invariant_expr_eq_intersect assms by simp

  show ?thesis
  proof(cases "k1 = k2")
    case True
    then have constant_idle: "\<lblot>Constant k1\<rblot>k2 = idle" by simp

    have sup_idle: "(\<Squnion>k. \<lblot>e\<rblot>k) = idle" using eval_Sup_idle_eq by simp
    have eq_case_in_all: "\<lblot>e\<rblot>k2 \<in> range (\<lambda>k. \<lblot>e\<rblot>k)" by auto

    show ?thesis
    proof(cases "?Pconst q")
      case True
      then have idle_q: "{. expr_eq e k1 .} rely r \<iinter> idle {. q .}"
        using constant_idle by simp
      then have "expr_eq e k1 \<subseteq> q"
        using triple_nil_refines_nonaborting_pre_subset_post_conj
        by (metis idle_nonaborting idle_ref_nil local.conj.commute nil_conj_rely) 


      have " \<lblot>e\<rblot>k2 \<le> idle"
        by (simp add: idle_eval(1))
      then have "?Pe q" using triple_refine_nonaborting_conj_same_aborting
        using idle_nonaborting idle_q by blast 
      then show ?thesis using True 
        by auto
    next
      case False
      then have "\<not> {. expr_eq e k1 .} rely r \<iinter> (\<Squnion>k. \<lblot>e\<rblot>k) {. q .}"
        using sup_idle constant_idle by simp
      then have "\<exists>k. \<not> {. expr_eq e k1 .} rely r \<iinter> \<lblot>e\<rblot>k {. q .} "
        using triple_Sup_with_rely[where C="range (\<lambda>k. \<lblot>e\<rblot>k)"] by blast
      then obtain k where k_not_obtain_post_q: "\<not> {. expr_eq e k1 .} rely r \<iinter> \<lblot>e\<rblot>k {. q .}" by auto
      have "k = k2"
      proof (rule ccontr)
        assume asm: "k \<noteq> k2"
        then have "k \<noteq> k1" using True by simp
        then have "expr_eq e k1 \<inter> expr_eq e k = {}"
          using asm by (auto simp: expr_eq_def)
        then have "{. expr_eq e k1 .} rely r \<iinter> \<lblot>e\<rblot>k {. {} .}"
          by (metis invar_e post_expr_invariant_expr_eq_intersect refl_r)
        then have post: "{. expr_eq e k1 .} rely r \<iinter> \<lblot>e\<rblot>k {. q .}"
          by (simp add: seq.Hoare_triple_alt seq.assert_op_assert seq_par.seq_assoc)

        then show False using k_not_obtain_post_q by simp
      qed
      then show ?thesis using k_not_obtain_post_q False by auto
    qed
  next
    case False
    then have "expr_eq e k1 \<inter> expr_eq e k2 = {}"
      using False by (auto simp: expr_eq_def)
    then have "{. expr_eq e k1 .} rely r \<iinter> \<lblot>e\<rblot>k2 {. {} .}"
      using post_e by simp
    then have any_q_e: "\<And>q. {. expr_eq e k1 .} rely r \<iinter> \<lblot>e\<rblot>k2 {. q .}"
      by (simp add: seq.Hoare_triple_alt seq.assert_op_assert seq_par.seq_assoc)

    have constant_nil: "\<lblot>Constant k1\<rblot>k2 = \<bottom>"
      using False by auto
    then have "{. expr_eq e k1 .} rely r \<iinter> \<lblot>Constant k1\<rblot>k2 {. {} .}"
      by (simp add: Hoare_triple_alt_with_rely seq.bot_annihilates_left seq_par.seq_assoc)
    then have "\<And>q. {. expr_eq e k1 .} rely r \<iinter> \<lblot>Constant k1\<rblot>k2 {. q .}"
      using constant_nil seq.bot_annihilates_left triple_with_rely by fastforce
    then show ?thesis using any_q_e by blast
  qed
qed


(* Original lines 581-663. *)
text \<open>If an l-value expression is invariant under the rely, then after
asserting that it denotes \<open>lv1\<close>, evaluating it for \<open>lv2\<close> has the
same Hoare triples as the corresponding fixed-result command.  There is no
\<open>Constant\<close> constructor for l-value expressions, so the fixed-result
command is written explicitly.\<close>
lemma lval_cmd_equiv_constant_under_invar:
  assumes refl_r: "refl r"
  assumes invar_lve: "invar_lval lve r"
  shows "{. lval_eq lve lv1 .} rely r \<iinter> \<ltort>lve\<rtort>lv2 {. q .}
     \<longleftrightarrow> {. lval_eq lve lv1 .} rely r \<iinter> (if lv1 = lv2 then idle else \<bottom>) {. q .}"
proof -
  let ?Pknown = "\<lambda>q. {. lval_eq lve lv1 .} rely r \<iinter>  (if lv1 = lv2 then idle else \<bottom>) {. q .}"
  let ?Plve = "\<lambda>q. {. lval_eq lve lv1 .} rely r \<iinter> \<ltort>lve\<rtort>lv2 {. q .}"

  have post_lve: "?Plve (lval_eq lve lv1 \<inter> lval_eq lve lv2)"
    using post_lval_invariant_lval_eq_intersect refl_r invar_lve by simp

  show ?thesis
  proof (cases "lv1 = lv2")
    case True
    then have known_idle: "(if lv1 = lv2 then idle else \<bottom>) = idle"
      by simp

    have sup_idle: "(\<Squnion>lv. \<ltort>lve\<rtort>lv) = idle"
      using lval_Sup_idle_eq by simp 

    show ?thesis
    proof (cases "?Pknown q")
      case True
      then have idle_q: "{. lval_eq lve lv1 .} rely r \<iinter> idle {. q .}"
        using known_idle by simp
      then have "lval_eq lve lv1 \<subseteq> q"
        using triple_nil_refines_nonaborting_pre_subset_post_conj
        by (metis idle_nonaborting idle_ref_nil local.conj.commute nil_conj_rely)

      have "\<ltort>lve\<rtort>lv2 \<le> idle"
        by (simp add: idle_eval(2))
      then have "?Plve q"
        using triple_refine_nonaborting_conj_same_aborting
          idle_nonaborting idle_q by blast
      then show ?thesis using True by auto
    next
      case False
      then have "\<not> {. lval_eq lve lv1 .} rely r \<iinter> (\<Squnion>lv. \<ltort>lve\<rtort>lv) {. q .}"
        using sup_idle known_idle by simp
      then have "\<exists>lv. \<not> {. lval_eq lve lv1 .} rely r \<iinter> \<ltort>lve\<rtort>lv {. q .}"
        using triple_Sup_with_rely
          [where C = "range (\<lambda>lv. \<ltort>lve\<rtort>lv)"] by blast
      then obtain lv where no_post: "\<not> {. lval_eq lve lv1 .} rely r \<iinter> \<ltort>lve\<rtort>lv {. q .}"
        by auto
      have "lv = lv2"
      proof (rule ccontr)
        assume lv_neq: "lv \<noteq> lv2"
        then have "lv \<noteq> lv1" using True by simp
        then have "lval_eq lve lv1 \<inter> lval_eq lve lv = {}"
          by (auto simp: lval_eq_def)
        then have "{. lval_eq lve lv1 .} rely r \<iinter> \<ltort>lve\<rtort>lv {. {} .}"
          using post_lval_invariant_lval_eq_intersect refl_r invar_lve by metis 
        then have "{. lval_eq lve lv1 .} rely r \<iinter> \<ltort>lve\<rtort>lv {. q .}"
          by (simp add: seq.Hoare_triple_alt seq.assert_op_assert seq_par.seq_assoc)
        with no_post show False by simp
      qed
      then show ?thesis using no_post False by auto
    qed
  next
    case False
    then have "lval_eq lve lv1 \<inter> lval_eq lve lv2 = {}"
      by (auto simp: lval_eq_def)
    then have "{. lval_eq lve lv1 .} rely r \<iinter> \<ltort>lve\<rtort>lv2 {. {} .}"
      using post_lve by simp
    then have any_q_lve:
      "\<And>q. {. lval_eq lve lv1 .} rely r \<iinter> \<ltort>lve\<rtort>lv2 {. q .}"
      by (simp add: seq.Hoare_triple_alt seq.assert_op_assert seq_par.seq_assoc)

    have known_nil: "(if lv1 = lv2 then idle else \<bottom>) = \<bottom>"
      using False by simp
    then have "{. lval_eq lve lv1 .} rely r \<iinter> (if lv1 = lv2 then idle else \<bottom>) {. {} .}"
      by (simp add: Hoare_triple_alt_with_rely seq.bot_annihilates_left seq_par.seq_assoc)
    then have "\<And>q. {. lval_eq lve lv1 .} rely r \<iinter> (if lv1 = lv2 then idle else \<bottom>) {. q .}"
      using known_nil seq.bot_annihilates_left triple_with_rely by fastforce
    then show ?thesis using any_q_lve by blast
  qed
qed


(* Original lines 665-679. *)
lemma triple_rely_idle_iff:
  assumes stable_p: "stable p r"
  shows "{. p .} rely r \<iinter> idle {. q .} \<longleftrightarrow> p \<subseteq> q"
proof
  assume idle_q: "{. p .} rely r \<iinter> idle {. q .}"
  show "p \<subseteq> q"
    using triple_nil_refines_nonaborting_pre_subset_post_conj idle_q
    by (metis idle_nonaborting idle_ref_nil local.conj.commute nil_conj_rely)
next
  assume p_subset_q: "p \<subseteq> q"
  have "{. p .} rely r \<iinter> idle {. p .}"
    using rely_idle_stable_assert stable_p triple_with_rely by simp 
  then show "{. p .} rely r \<iinter> idle {. q .}"
    using p_subset_q seq.triple_consequence_post by blast
qed


(* Original lines 681-705. *)
text \<open>logical form of \<open>expr_cmd_equiv_constant_under_invar\<close>.\<close>
lemma expr_cmd_hoare_iff_under_invar:
  assumes refl_r: "refl r"
  assumes invar_e: "invar_expr e r"
  shows "{. expr_eq e k1 .} rely r \<iinter> \<lblot>e\<rblot>k2 {. q .} \<longleftrightarrow> (k1 = k2 \<longrightarrow> expr_eq e k1 \<subseteq> q)"
proof (cases "k1 = k2")
  case True
  have stable_expr: "stable (expr_eq e k1) r"
    using invar_e invar_expr_stable by blast
  have eval_iff:
    "{. expr_eq e k1 .} rely r \<iinter> \<lblot>e\<rblot>k2 {. q .} \<longleftrightarrow> {. expr_eq e k1 .} rely r \<iinter> idle {. q .}"
    using expr_cmd_equiv_constant_under_invar[OF refl_r invar_e] True by simp
  show ?thesis
    using eval_iff triple_rely_idle_iff[OF stable_expr] True by simp
next
  case False
  have disjoint: "expr_eq e k1 \<inter> expr_eq e k2 = {}"
    using False by (auto simp: expr_eq_def)
  have empty_post: "{. expr_eq e k1 .} rely r \<iinter> \<lblot>e\<rblot>k2 {. {} .}"
    using post_expr_invariant_expr_eq_intersect refl_r invar_e disjoint by metis 
  have any_post: "{. expr_eq e k1 .} rely r \<iinter> \<lblot>e\<rblot>k2 {. q .}"
    using empty_post by (simp add: seq.Hoare_triple_alt seq.assert_op_assert seq_par.seq_assoc)
  show ?thesis
    using False any_post by simp
qed


(* Original lines 707-734. *)
text \<open>logical form of \<open>lval_cmd_equiv_constant_under_invar\<close>.\<close>
lemma lval_cmd_hoare_iff_under_invar:
  assumes refl_r: "refl r"
  assumes invar_lve: "invar_lval lve r"
  shows "{. lval_eq lve lv1 .} rely r \<iinter> \<ltort>lve\<rtort>lv2 {. q .} \<longleftrightarrow> (lv1 = lv2 \<longrightarrow> lval_eq lve lv1 \<subseteq> q)"
proof (cases "lv1 = lv2")
  case True
  have stable_lval: "stable (lval_eq lve lv1) r"
    using invar_lve invar_lval_stable by blast
  have eval_iff:
    "{. lval_eq lve lv1 .} rely r \<iinter> \<ltort>lve\<rtort>lv2 {. q .}
      \<longleftrightarrow>
     {. lval_eq lve lv1 .} rely r \<iinter> idle {. q .}"
    using lval_cmd_equiv_constant_under_invar[OF refl_r invar_lve] True
    by simp
  show ?thesis
    using eval_iff triple_rely_idle_iff[OF stable_lval] True by simp
next
  case False
  have disjoint: "lval_eq lve lv1 \<inter> lval_eq lve lv2 = {}"
    using False by (auto simp: lval_eq_def)
  have empty_post: "{. lval_eq lve lv1 .} rely r \<iinter> \<ltort>lve\<rtort>lv2 {. {} .}"
    using post_lval_invariant_lval_eq_intersect refl_r invar_lve disjoint by metis 
  have any_post: "{. lval_eq lve lv1 .} rely r \<iinter> \<ltort>lve\<rtort>lv2 {. q .}"
    using empty_post by (simp add: seq.Hoare_triple_alt seq.assert_op_assert seq_par.seq_assoc)
  show ?thesis
    using False any_post by simp
qed


(* Original lines 736-752. *)
text \<open>Alternative syntax for special case with p=UNIV. If an expression is invariant under r,
then we have the assertion that k is equal to the evaluation of e after an expression command.\<close>
lemma rely_expr_extract_eval:
  assumes refl_r: "refl r"
  assumes invar_e: "invar_expr e r"
  shows "rely r \<iinter> \<lblot>e\<rblot>k = rely r \<iinter> (\<lblot>e\<rblot>k ; \<lbrace>expr_eq e k\<rbrace>)"
proof -
  have stable_univ: "stable UNIV r" by simp
  have univ_absorb: "UNIV \<inter> {\<sigma>. k = \<lbrakk>e\<rbrakk>\<sigma>} = {\<sigma>. k = \<lbrakk>e\<rbrakk>\<sigma>}" by simp
  
  have "\<And>k::'v. {. UNIV .} rely r \<iinter> \<lblot>e\<rblot>k {. UNIV \<inter> expr_eq e k .}"
    using invar_e post_expr_invariant(1) refl_r stable_univ by presburger
  then have "{. UNIV .} rely r \<iinter> \<lblot>e\<rblot>k {. expr_eq e k .}" using univ_absorb by simp

  then show ?thesis using Hoare_triple_alt_with_rely
    by (metis local.seq.nil_seq seq.assert_neut)
qed


(* Original lines 754-769. *)
lemma rely_lval_expr_extract_lval:
  assumes refl_r: "refl r"
  assumes invar_e: "invar_lval lve r"
  shows "rely r \<iinter> \<ltort>lve\<rtort>lv = rely r \<iinter> (\<ltort>lve\<rtort>lv ; \<lbrace>lval_eq lve lv\<rbrace>)"
proof -
  have stable_univ: "stable UNIV r" by simp
  have univ_absorb: "UNIV \<inter> lval_eq lve k = lval_eq lve k" by simp
  
  have "\<And>lv.  {. UNIV .} rely r \<iinter> \<ltort>lve\<rtort>lv {. UNIV \<inter> lval_eq lve lv .}"
    using invar_e post_expr_invariant(2) refl_r stable_univ by presburger
  then have " {. UNIV .} rely r \<iinter> \<ltort>lve\<rtort>lv {. lval_eq lve lv .}"
    using univ_absorb by simp

  then show ?thesis using Hoare_triple_alt_with_rely
    by (metis local.seq.nil_seq seq.assert_neut)
qed
