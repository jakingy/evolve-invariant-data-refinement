(* Extracts from isabelle/new_rg_algebra/Commands/Expressions.thy. *)
(* These are source excerpts, not a standalone buildable theory. *)

(* Original lines 93-100. *)
lemma lval_eq_all: "(\<Squnion>lv. \<tau>(lval_eq lve lv)) = nil"
proof -
  have all: "(\<Union>lv. lval_eq lve lv) = UNIV"
    unfolding lval_eq_def by blast
  have "(\<Squnion>lv. \<tau>(lval_eq lve lv)) = \<tau>(\<Union>lv. lval_eq lve lv)"
    by (simp add: range_composition seq.test_Union)
  then show ?thesis by (simp add: all seq.test_set_top)
qed


(* Original lines 311-321. *)
text \<open>For each lvalue lv, the union of tests of all possible values for lv is nil.\<close>
lemma lval_get_all_test_nil: "\<And>lv. (\<Squnion>x::'v. \<tau> {\<sigma>. get lv \<sigma> = x}) = nil"
proof -
  fix lv
  have cover: "(\<Union>x::'v. {\<sigma>. get lv \<sigma> = x}) = UNIV" by blast
  have "(\<Squnion>x::'v. \<tau> {\<sigma>. get lv \<sigma> = x}) = \<tau> (\<Union>x::'v. {\<sigma>. get lv \<sigma> = x})"
    by (metis image_image seq.test_Union)
  also have "\<dots> = nil"
    by (simp add: cover seq.test_set_top)
  finally show "(\<Squnion>x::'v. \<tau> {\<sigma>. get lv \<sigma> = x}) = nil" .
qed


(* Original lines 323-455. *)
text \<open>The union of expression evaluation over all possible results is idle.
The following lemma just shows it is a refinement as a helper for \<open>bind_ref_idle\<close> (DEAD).\<close>
lemma eval_Sup_idle: "(\<Squnion>k. \<lblot>e\<rblot>k) \<ge> idle"
  and lval_Sup_idle: "(\<Squnion>lv. \<ltort>lve\<rtort>lv) \<ge> idle"                      
proof (induction e and lve)
  case (Constant \<kappa>)
  show ?case
  proof-
    have k_idle: "\<lblot>Constant \<kappa>\<rblot>\<kappa> = idle" by simp
    have "\<lblot>Constant \<kappa>\<rblot>\<kappa> \<in> range (expr_cmd (Constant \<kappa>))" by simp
    then show ?thesis using Sup_upper k_idle by simp
  qed
next
  case (Deref lve)
  then show ?case
  proof -
    assume IH: "idle \<le> (\<Squnion>lv. \<ltort>lve\<rtort>lv)"

    have "idle = idle ; nil ; idle"
      by (simp add: idle_seq_idle)
    also have "\<dots> \<le> (\<Squnion>lv. \<ltort>lve\<rtort>lv) ; nil ; idle"
      using IH by (simp add: seq_par.seq_mono_left)
    also have "\<dots> = (\<Squnion>lv. \<ltort>lve\<rtort>lv ; nil ; idle)"
      by (simp add: seq.Sup_UNIV_op seq_par.seq_assoc)
    also have "\<dots> = (\<Squnion>lv. \<ltort>lve\<rtort>lv ; (\<Squnion>x. \<tau> {\<sigma>. get lv \<sigma> = x}) ; idle)"
      by (simp add: lval_get_all_test_nil)
    also have "\<dots> = (\<Squnion>lv. (\<Squnion>x. \<ltort>lve\<rtort>lv ; \<tau> {\<sigma>. get lv \<sigma> = x}) ; idle)"
      by (simp add: seq.op_Sup_UNIV)
    also have "\<dots> = (\<Squnion>lv. (\<Squnion>x. \<ltort>lve\<rtort>lv ; \<tau> {\<sigma>. get lv \<sigma> = x} ; idle))"
      by (simp add: seq.Sup_UNIV_op)
    also have "\<dots> = (\<Squnion>x. (\<Squnion>lv. \<ltort>lve\<rtort>lv ; \<tau> {\<sigma>. get lv \<sigma> = x} ; idle))"
      by (rule SUP_commute)
    finally have "idle \<le> (\<Squnion>x. (\<Squnion>lv. \<ltort>lve\<rtort>lv ; \<tau> {\<sigma>. get lv \<sigma> = x} ; idle))" .

    then show ?thesis by simp
  qed
next
  case (Unary unop e)
  have lift: "(\<Squnion>k. \<lblot>e\<rblot>k) \<le> (\<Squnion>x. \<lblot>Unary unop e\<rblot>x)"
  proof (simp only: SUP_le_iff; intro ballI)
    fix k
    have k_in: "k \<in> {k1. unop k1 = unop k}" by simp
    have elem: "\<lblot>Unary unop e\<rblot>(unop k) \<in> range (expr_cmd (Unary unop e))" by simp
    have "\<lblot>e\<rblot>k \<le> (\<Squnion>k1 \<in> {k1. unop k1 = unop k}. \<lblot>e\<rblot>k1)"
      using k_in by (simp add: SUP_upper)
    also have "\<dots> = \<lblot>Unary unop e\<rblot>(unop k)"
      using unary_alt by auto
    also have "\<dots> \<le> (\<Squnion>x. \<lblot>Unary unop e\<rblot>x)"
      using Sup_upper elem by metis  
    finally show "\<lblot>e\<rblot>k \<le> (\<Squnion>x. \<lblot>Unary unop e\<rblot>x)" .
  qed

  have "idle \<le> (\<Squnion>x. \<lblot>Unary unop e\<rblot>x)"
    using Unary.IH lift by (rule order_trans)
  then show ?case by simp
next
  case (Binary binop e1 e2)
  have lift_binary: "(\<Squnion>k1. \<Squnion>k2. \<lblot>e1\<rblot>k1 \<parallel> \<lblot>e2\<rblot>k2) \<le> (\<Squnion>x. \<lblot>Binary binop e1 e2\<rblot>x)"
  proof (rule SUP_least)
    fix k1
    show "(\<Squnion>k2. \<lblot>e1\<rblot>k1 \<parallel> \<lblot>e2\<rblot>k2) \<le> (\<Squnion>x. \<lblot>Binary binop e1 e2\<rblot>x)"
    proof (rule SUP_least)
      fix k2
      have k_in: "(k1, k2) \<in> {(a, b). binop a b = binop k1 k2}" by simp
      have elem: "\<lblot>Binary binop e1 e2\<rblot>(binop k1 k2) \<in> range (expr_cmd (Binary binop e1 e2))" by simp
      have branch_in:
        "\<lblot>e1\<rblot>k1 \<parallel> \<lblot>e2\<rblot>k2 \<in> (\<lambda>k12. \<lblot>e1\<rblot>(fst k12) \<parallel> \<lblot>e2\<rblot>(snd k12)) ` {(a, b). binop a b = binop k1 k2}"
        by (rule image_eqI[where x = "(k1, k2)"]; simp add: k_in)
      have branch:
        "\<lblot>e1\<rblot>k1 \<parallel> \<lblot>e2\<rblot>k2 \<le> (\<Squnion>k12 \<in> {(a, b). binop a b = binop k1 k2}. \<lblot>e1\<rblot>(fst k12) \<parallel> \<lblot>e2\<rblot>(snd k12))"
        by (rule Sup_upper[OF branch_in])
      have "\<lblot>e1\<rblot>k1 \<parallel> \<lblot>e2\<rblot>k2 \<le> (\<Squnion>k12 \<in> {(a, b). binop a b = binop k1 k2}. \<lblot>e1\<rblot>(fst k12) \<parallel> \<lblot>e2\<rblot>(snd k12))"
        by (rule branch)
      also have "\<dots> = \<lblot>Binary binop e1 e2\<rblot>(binop k1 k2)"
        by (rule binary_alt[symmetric])
      also have "\<dots> \<le> (\<Squnion>x. \<lblot>Binary binop e1 e2\<rblot>x)"
        by (rule Sup_upper[OF elem])
      finally show "\<lblot>e1\<rblot>k1 \<parallel> \<lblot>e2\<rblot>k2 \<le>
          (\<Squnion>x. \<lblot>Binary binop e1 e2\<rblot>x)" .
    qed
  qed

  have evals_cover: "idle \<le> (\<Squnion>k1. \<Squnion>k2. \<lblot>e1\<rblot>k1 \<parallel> \<lblot>e2\<rblot>k2)"
  proof -
    have "idle = idle \<parallel> idle"
      by (simp add: idle_par_idle)
    also have "\<dots> \<le> (\<Squnion>k1. \<lblot>e1\<rblot>k1) \<parallel> (\<Squnion>k2. \<lblot>e2\<rblot>k2)"
      using Binary.IH(1,2) by (rule seq_par.sync_mono)
    also have "\<dots> = (\<Squnion>k1. \<Squnion>k2. \<lblot>e1\<rblot>k1 \<parallel> \<lblot>e2\<rblot>k2)"
      by (rule par.Sup_UNIV_op_Sup_UNIV)
    finally show ?thesis .
  qed

  have result: "idle \<le> (\<Squnion>x. \<lblot>Binary binop e1 e2\<rblot>x)"
    using evals_cover lift_binary by (rule order_trans)
  then show ?case by simp
next
  case (Var v)
  have "idle = \<ltort>Var v\<rtort>(Base v)" by simp
  also have "\<dots> \<le> (\<Squnion>lv. \<ltort>Var v\<rtort>lv)" by simp
  finally show ?case .
next
  case (ArrayRef lve e)
  have lift_array: "(\<Squnion>A. \<Squnion>i. \<ltort>lve\<rtort>A \<parallel> \<lblot>e\<rblot>i) \<le> (\<Squnion>lv. \<ltort>ArrayRef lve e\<rtort>lv)"
  proof (rule SUP_least)
    fix A
    show "(\<Squnion>i. \<ltort>lve\<rtort>A \<parallel> \<lblot>e\<rblot>i) \<le> (\<Squnion>lv. \<ltort>ArrayRef lve e\<rtort>lv)"
    proof (rule SUP_least)
      fix i
      have elem: "\<ltort>ArrayRef lve e\<rtort>(Indexed A i) \<in> range (lval_cmd (ArrayRef lve e))" by blast
      have "\<ltort>lve\<rtort>A \<parallel> \<lblot>e\<rblot>i = \<ltort>ArrayRef lve e\<rtort>(Indexed A i)" by simp
      also have "\<dots> \<le> (\<Squnion>lv. \<ltort>ArrayRef lve e\<rtort>lv)"
        using elem by (simp add: Sup_upper) 
      finally show "\<ltort>lve\<rtort>A \<parallel> \<lblot>e\<rblot>i  \<le> (\<Squnion>lv. \<ltort>ArrayRef lve e\<rtort>lv)" .
    qed
  qed

  have evals_cover:
    "idle \<le> (\<Squnion>A. \<Squnion>i. \<ltort>lve\<rtort>A \<parallel> \<lblot>e\<rblot>i)"
  proof -
    have "idle = idle \<parallel> idle"
      by (simp add: idle_par_idle)
    also have "\<dots> \<le> (\<Squnion>A. \<ltort>lve\<rtort>A) \<parallel> (\<Squnion>i. \<lblot>e\<rblot>i)"
      using ArrayRef.IH(1,2) by (rule seq_par.sync_mono)
    also have "\<dots> = (\<Squnion>A. \<Squnion>i. \<ltort>lve\<rtort>A \<parallel> \<lblot>e\<rblot>i)"
      by (rule par.Sup_UNIV_op_Sup_UNIV)
    finally show ?thesis .
  qed

  have result: "idle \<le> (\<Squnion>lv. \<ltort>ArrayRef lve e\<rtort>lv)"
    using evals_cover lift_array by (rule order_trans)
  then show ?case .
qed


(* Original lines 457-468. *)
text \<open>The equality variant.\<close>
lemma eval_Sup_idle_eq: "(\<Squnion>k. \<lblot>e\<rblot>k) = idle"
proof (rule antisym)
  show "(\<Squnion>k. \<lblot>e\<rblot>k) \<le> idle"
  proof (rule SUP_least)
    fix k
    show "\<lblot>e\<rblot>k \<le> idle"
      by (rule idle_eval(1))
  qed
  show "idle \<le> (\<Squnion>k. \<lblot>e\<rblot>k)"
    using eval_Sup_idle by simp
qed


(* Original lines 470-480. *)
lemma lval_Sup_idle_eq: "(\<Squnion>lv. \<ltort>lve\<rtort>lv) = idle"
proof (rule antisym)
  show "(\<Squnion>lv. \<ltort>lve\<rtort>lv) \<le> idle"
  proof (rule SUP_least)
    fix lv
    show "\<ltort>lve\<rtort>lv \<le> idle"
      by (rule idle_eval(2))
  qed
  show "idle \<le> (\<Squnion>lv. \<ltort>lve\<rtort>lv)"
    using lval_Sup_idle by simp
qed


(* Original lines 490-501. *)
text \<open>Having \<open>idle\<close> sequentially after an expression evaluation command is redundant.\<close>
(*TODO move this lemma to lower theory.*)
lemma par_seq_idle:
  assumes c_idle: "c ; idle = c"
  assumes d_idle: "d ; idle = d"
  shows "(c \<parallel> d) ; idle = c \<parallel> d"
proof (rule antisym)
  show "(c \<parallel> d) ; idle \<le> c \<parallel> d"
    using c_idle d_idle seq_par.weak_interchange by (metis idle_par_idle)
  show "c \<parallel> d \<le> (c \<parallel> d) ; idle"
    using idle_ref_nil seq.seq_mono_right by (metis local.seq.seq_nil)
qed


(* Original lines 503-581. *)
lemma expr_seq_idle: "\<And>k. \<lblot>e\<rblot>k ; idle = \<lblot>e\<rblot>k"
  and lval_seq_idle: "\<And>lv. \<ltort>lve\<rtort>lv ; idle = \<ltort>lve\<rtort>lv"
proof (induction e and lve)
  case (Constant \<kappa>)
  then show ?case
    by (simp add: idle_seq_idle seq.bot_annihilates_left)
next
  case (Deref lve)
  then show ?case
    by (simp add: seq.Sup_UNIV_op seq_par.seq_assoc idle_seq_idle)
next
  case (Unary unop e)
  show ?case
  proof -
    have "\<lblot>Unary unop e\<rblot>k = \<Squnion>{\<lblot>e\<rblot>k1 |k1. unop k1 = k}"
      by simp
    also have "\<dots> = \<Squnion>{\<lblot>e\<rblot>k1 ; idle |k1. unop k1 = k}"
      using Unary by auto
    also have "\<dots> = (\<Squnion>{\<lblot>e\<rblot>k1 |k1. unop k1 = k}) ; idle"
    proof -
      have image_eq:
        "{c ; idle |c. c \<in> {\<lblot>e\<rblot>k1 |k1. unop k1 = k}} =  {\<lblot>e\<rblot>k1 ; idle |k1. unop k1 = k}"
        by auto
      have "(\<Squnion>{\<lblot>e\<rblot>k1 |k1. unop k1 = k}) ; idle = (\<Squnion>c \<in> {\<lblot>e\<rblot>k1 |k1. unop k1 = k}. c ; idle)"
        by (rule seq.Sup_op)
      also have "\<dots> = \<Squnion>{c ; idle |c. c \<in> {\<lblot>e\<rblot>k1 |k1. unop k1 = k}}"
        by (rule SUP_eq_Sup)
      also have "\<dots> = \<Squnion>{\<lblot>e\<rblot>k1 ; idle |k1. unop k1 = k}"
        using image_eq by simp
      finally show ?thesis by simp
    qed
    finally show ?thesis by auto
  qed
next
  case (Binary binop e1 e2)
  have branch_idle: "\<And>k1 k2. (\<lblot>e1\<rblot>k1 \<parallel> \<lblot>e2\<rblot>k2) ; idle =  \<lblot>e1\<rblot>k1 \<parallel> \<lblot>e2\<rblot>k2"
  proof -
    fix k1 k2
    show "(\<lblot>e1\<rblot>k1 \<parallel> \<lblot>e2\<rblot>k2) ; idle = \<lblot>e1\<rblot>k1 \<parallel> \<lblot>e2\<rblot>k2"
      using par_seq_idle[OF Binary.IH(1)[of k1] Binary.IH(2)[of k2]] .
  qed
  have branch_set_eq:
    "{(\<lblot>e1\<rblot>k1 \<parallel> \<lblot>e2\<rblot>k2) ; idle |k1 k2. binop k1 k2 = k} = {\<lblot>e1\<rblot>k1 \<parallel> \<lblot>e2\<rblot>k2 |k1 k2. binop k1 k2 = k}"
    using branch_idle by auto
  have image_eq:
    "{c ; idle |c. c \<in> {\<lblot>e1\<rblot>k1 \<parallel> \<lblot>e2\<rblot>k2 |k1 k2. binop k1 k2 = k}} =
     {(\<lblot>e1\<rblot>k1 \<parallel> \<lblot>e2\<rblot>k2) ; idle |k1 k2. binop k1 k2 = k}"
    by auto
  show ?case
  proof -
    have "\<lblot>Binary binop e1 e2\<rblot>k ; idle = (\<Squnion>{\<lblot>e1\<rblot>k1 \<parallel> \<lblot>e2\<rblot>k2 |k1 k2. binop k1 k2 = k}) ; idle"
      by simp
    also have "\<dots> = (\<Squnion>c \<in> {\<lblot>e1\<rblot>k1 \<parallel> \<lblot>e2\<rblot>k2 |k1 k2. binop k1 k2 = k}. c ; idle)"
      by (rule seq.Sup_op)
    also have "\<dots> = \<Squnion>{c ; idle |c. c \<in> {\<lblot>e1\<rblot>k1 \<parallel> \<lblot>e2\<rblot>k2 |k1 k2. binop k1 k2 = k}}"
      by (rule SUP_eq_Sup)
    also have "\<dots> = \<Squnion>{(\<lblot>e1\<rblot>k1 \<parallel> \<lblot>e2\<rblot>k2) ; idle |k1 k2. binop k1 k2 = k}"
      using image_eq by simp
    also have "\<dots> = \<Squnion>{\<lblot>e1\<rblot>k1 \<parallel> \<lblot>e2\<rblot>k2 |k1 k2. binop k1 k2 = k}"
      using branch_set_eq by simp
    finally show ?thesis by simp
  qed
next
  case (Var v)
  then show ?case
    by (simp add: idle_seq_idle seq.bot_annihilates_left) 
next
  case (ArrayRef lve e)
  then show ?case
  proof (cases lv)
    case (Base v)
    then show ?thesis 
      by (simp add: seq.bot_annihilates_left)
  next
    case (Indexed A i)
    then show ?thesis
      using par_seq_idle[OF ArrayRef.IH(1)[of A] ArrayRef.IH(2)[of i]] by simp
  qed
qed


(* Original lines 583-584. *)
lemma eval_pair_seq_idle: "(\<ltort>lve\<rtort>lv \<parallel> \<lblot>e\<rblot>k) ; idle = \<ltort>lve\<rtort>lv \<parallel> \<lblot>e\<rblot>k"
  using par_seq_idle by (simp add: expr_seq_idle lval_seq_idle par_seq_idle)
