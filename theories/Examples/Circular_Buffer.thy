section \<open>Example: Circular Buffer\<close>

theory Circular_Buffer
  imports Typed_State Commands.Data_Refinement
begin

text \<open>Max size of queue/circular buffer\<close>
consts N :: nat

subsection \<open>Lift operations to operate on \<open>typed_values\<close>\<close>
abbreviation q_size_lift where
  "q_size_lift \<equiv> lift1 as_nat_queue NatValue q_size"

abbreviation q_suffix_lift where
  "q_suffix_lift \<equiv> lift2 as_nat_queue as_nat_queue BoolValue q_suffix"

definition q_suffix_of :: "typed_value \<Rightarrow> typed_value \<Rightarrow> bool"
  (infix "suffix'_of" 60)
where
  "q_suffix_of q1 q2 \<longleftrightarrow>
     q_suffix_lift q1 q2 = BoolValue True"

abbreviation q_prefix_lift where
  "q_prefix_lift \<equiv> lift2 as_nat_queue as_nat_queue BoolValue q_prefix"

abbreviation circ_buf_pointer_increment where
  "circ_buf_pointer_increment \<equiv> lift1 as_nat NatValue (\<lambda> n. (n + 1) mod (N + 1))"

definition q_prefix_of :: "typed_value \<Rightarrow> typed_value \<Rightarrow> bool"
  (infix "prefix'_of" 60)
where
  "q_prefix_of q1 q2 \<longleftrightarrow>
     q_prefix_lift q1 q2 = BoolValue True"

abbreviation enqueue_lift where
  "enqueue_lift \<equiv> lift2 as_nat_queue as_nat NatQueueValue enqueue"

abbreviation concat_front where
  "concat_front \<equiv> lift2 as_nat as_nat_queue NatQueueValue q_concat_front"

definition q_has_space :: "typed_value \<Rightarrow> bool" where
  "q_has_space qv \<longleftrightarrow>
     (\<exists>Q. qv = NatQueueValue Q \<and> q_size Q < N)"

definition q_non_empty :: "typed_value \<Rightarrow> bool" where
  "q_non_empty qv \<longleftrightarrow>
     (\<exists>Q. qv = NatQueueValue Q \<and> \<not>is_empty Q)"

context typed_frame_state
begin

subsection \<open>Define variables\<close>
text \<open>\<open>define_var\<close> uses the base name for
the getter, and creates the corresponding \<open>_lval\<close> and \<open>_lve\<close>
names.\<close>
define_var q
define_var r
define_var w
define_var x
define_var buffer

text \<open>A is the finite set of abstract variable l-values.\<close>
abbreviation A where "A \<equiv> {|q_lval|}"

definition buffer_at ::
  "('state, typed_value) Expr \<Rightarrow> ('state, typed_value) LValueExpr"
where
  "buffer_at i = ArrayRef buffer_lve i"

text \<open>Get the buffer value at a particular nat index in a state.\<close>
definition buffer_value :: "nat \<Rightarrow> 'state \<Rightarrow> typed_value" where
  "buffer_value i \<sigma> = \<lbrakk>Deref (buffer_at (Constant (NatValue i)))\<rbrakk> \<sigma>"

definition buffer_at_lval :: "nat \<Rightarrow> typed_value LValue" where
  "buffer_at_lval i = Indexed buffer_lval (NatValue i)"

declare buffer_at_def [simp_vars]
declare buffer_value_def [simp_vars]
declare buffer_at_lval_def [simp_vars]

text \<open>\<open>fset\<close> of buffer values so it can be supplied to frame.\<close>
definition buf_lvals :: "typed_value LValue fset" where
  "buf_lvals = fset_of_list (map buffer_at_lval [0..<N + 1])"

lemma eval_Deref_buf: "get (buffer_at_lval i) \<sigma> = buffer_value i \<sigma>" 
  by (simp add: buffer_at_def buffer_at_lval_def buffer_lval_def buffer_lve_def buffer_value_def)

text \<open>Enqueue can change q, w and buf[i] for all i < N+1.\<close>
definition enqueue_lvals :: "typed_value LValue fset" where
  "enqueue_lvals = finsert q_lval (finsert w_lval buf_lvals)"

text \<open>The atomic spec idles become framed terms when w,r,buf are introduced.\<close>
definition enqueue_lvals_term :: "typed_value LValue fset" where
  "enqueue_lvals_term = finsert w_lval buf_lvals"

lemma term_lvals_subset: "enqueue_lvals_term |\<subseteq>| enqueue_lvals"
  by (simp add: enqueue_lvals_def enqueue_lvals_term_def fsubset_finsertI)

definition dequeue_lvals :: "typed_value LValue fset" where
  "dequeue_lvals = {|q_lval,x_lval,r_lval|}"

definition dequeue_lvals_term :: "typed_value LValue fset" where
  "dequeue_lvals_term = {|x_lval|}"

subsection \<open>Retrieval function\<close>
text \<open>The concrete buffer uses read head \<open>r\<close> and write head \<open>w\<close> which are
indices in \<open>{0 ..< N+1}\<close>. It represents at most \<open>N\<close> queue values.\<close>
definition queued_count :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "queued_count rh wh = (wh + (N + 1) - rh) mod (N+1)"

text \<open>Needed to decrease on \<open>queued_count\<close> for it to find termination order.\<close>
definition retr_list :: "nat \<Rightarrow> nat \<Rightarrow> 'state \<Rightarrow> nat list" where
  "retr_list rh n \<sigma> =
    map (\<lambda>i. the (as_nat (buffer_value ((rh + i) mod (N + 1)) \<sigma>)))
        [0..<n]"

lemma retr_list_suc:
  "retr_list rh (Suc n) \<sigma> =
    retr_list rh n \<sigma> @
      [the (as_nat (buffer_value ((rh + n) mod (N + 1)) \<sigma>))]"
  by (simp add: retr_list_def)

definition retr :: "nat \<Rightarrow> nat \<Rightarrow> 'state \<Rightarrow> nat queue" where
  "retr rh wh \<sigma> = Queue (retr_list rh (queued_count rh wh) \<sigma>)"

subsection \<open>Queue and modular arithmetic helper lemmas\<close>
lemma queued_count_no_wrap:
  assumes "rh \<le> wh"
  assumes "wh < N + 1"
  shows "queued_count rh wh = wh - rh"
proof -
  have eq: "wh + (N + 1) - rh = (N + 1) + (wh - rh)"
    using assms by arith
  show ?thesis
    by (simp only: queued_count_def eq mod_add_self1) (use assms in auto)
qed

lemma queued_count_wrap:
  assumes "wh < rh"
  assumes "rh < N + 1"
  shows "queued_count rh wh = wh + (N + 1) - rh"
  unfolding queued_count_def
  by (rule mod_less) (use assms in linarith)

lemma queued_count_cases:
  assumes "rh < N + 1" "wh < N + 1"
  shows "queued_count rh wh = (if rh \<le> wh then wh - rh else wh + (N + 1) - rh)"
  using assms queued_count_no_wrap queued_count_wrap by simp

lemma queued_count_eq_zero_iff:
  assumes rh_bound: "rh < N + 1"
  assumes wh_bound: "wh < N + 1"
  shows "queued_count rh wh = 0 \<longleftrightarrow> rh = wh"
  using assms queued_count_cases[OF assms]
  by (auto split: if_splits; arith)

lemma queued_count_circ_inc_is_suc:
  assumes rh_bound: "rh < N + 1"
  assumes wh_bound: "wh < N + 1"
  assumes has_space: "queued_count rh wh < N"
  shows "queued_count rh ((wh + 1) mod (N + 1)) =  Suc (queued_count rh wh)"
proof -
  have inc: "(wh + 1) mod (N + 1) = (if wh = N then 0 else wh + 1)"
    using wh_bound by auto
  have bound: "(wh + 1) mod (N + 1) < N + 1" by simp
  show ?thesis
    using assms queued_count_cases[OF rh_bound wh_bound]
      queued_count_cases[OF rh_bound bound]
    unfolding inc
    using if_splits by fastforce
qed

lemma queued_count_at_write:
  assumes rh_bound: "rh < N + 1"
  assumes wh_bound: "wh < N + 1"
  shows "(rh + queued_count rh wh) mod (N + 1) = wh"
proof -
  have cancel: "rh + (wh + (N + 1) - rh) = wh + (N + 1)"
    using rh_bound by linarith
  then show ?thesis
    by (simp only: queued_count_def mod_add_right_eq mod_add_self2)
       (use wh_bound in simp)
qed

lemma circular_index_lt_ne:
  assumes r_bound: "rh < N + 1"
  assumes i_lt_q: "i < j"
  assumes q_bound: "j < N + 1"
  shows "(rh + i) mod (N + 1) \<noteq> (rh + j) mod (N + 1)"
proof
  assume eq: "(rh + i) mod (N + 1) = (rh + j) mod (N + 1)"
  have le: "rh + i \<le> rh + j" using i_lt_q by simp
  have divides: "(N + 1) dvd (j - i)"
    using mod_eq_dvd_iff_nat[OF le, of "N + 1"] eq by simp
  have "N + 1 \<le> j - i"
    using dvd_imp_le[OF divides] i_lt_q by simp
  then show False using q_bound by arith
qed

lemma retr_enqueue1: 
  assumes rh_bound: "rh < N + 1"
  assumes wh_bound: "wh < N + 1"
  assumes has_space: "queued_count rh wh < N"
  assumes enqueue_val: "buffer_value wh \<sigma> = NatValue W"
  shows "retr rh ((wh + 1) mod (N + 1)) \<sigma> = enqueue (retr rh wh \<sigma>) W"
  unfolding retr_def
  by (simp only: queued_count_circ_inc_is_suc[OF rh_bound wh_bound has_space]
      retr_list_suc queued_count_at_write[OF rh_bound wh_bound] enqueue_val) simp

lemma queued_count_circ_inc_read_is_pred:
  assumes rh_bound: "rh < N + 1"
  assumes wh_bound: "wh < N + 1"
  assumes non_empty: "0 < queued_count rh wh"
  shows "queued_count ((rh + 1) mod (N + 1)) wh = queued_count rh wh - 1"
proof -
  have inc: "(rh + 1) mod (N + 1) = (if rh = N then 0 else rh + 1)"
    using rh_bound by auto
  have bound: "(rh + 1) mod (N + 1) < N + 1" by simp
  show ?thesis
    using assms queued_count_cases[OF rh_bound wh_bound]
      queued_count_cases[OF bound wh_bound]
    unfolding inc
    by (auto split: if_splits)
qed

lemma retr_list_dequeue:
  assumes rh_bound: "rh < N + 1"
  shows "retr_list rh (Suc n) \<sigma>
       = the (as_nat (buffer_value rh \<sigma>)) # retr_list ((rh + 1) mod (N + 1)) n \<sigma>"
proof -
  have upt_suc: "[0..<Suc n] = 0 # map Suc [0..<n]"
    using map_Suc_upt upt_rec by auto
  show ?thesis
    using rh_bound
    unfolding retr_list_def
    by (subst upt_suc) (simp add: mod_add_left_eq)
qed

lemma retr_unchanged:
  assumes buffers_unchanged: "\<forall>i. buffer_value i s = buffer_value i s'"
  shows "retr R W s = retr R W s'"
  using assms by (simp add: retr_def retr_list_def)

lemma retr_dequeue1:
  assumes rh_bound: "rh < N + 1"
  assumes wh_bound: "wh < N + 1"
  assumes non_empty: "0 < queued_count rh wh"
  assumes buffers_unchanged: "\<forall>i. buffer_value i \<sigma>' = buffer_value i \<sigma>"
  shows "retr rh wh \<sigma> = q_concat_front (the (as_nat (buffer_value rh \<sigma>)))
                                       (retr ((rh + 1) mod (N + 1)) wh \<sigma>')"
proof-
  have "retr ((rh + 1) mod (N + 1)) wh \<sigma> = retr ((rh + 1) mod (N + 1)) wh \<sigma>'"
    using wh_bound buffers_unchanged retr_unchanged by simp

  then show ?thesis
  unfolding retr_def
  using retr_list_dequeue assms
  by (metis Suc_diff_1 q_concat_front.simps queued_count_circ_inc_read_is_pred) 
qed

lemma retr_list_n_length_n: "length (retr_list rh n s) = n"
  by (simp add: retr_list_def)

lemma q_size_queued_count_equiv:
  assumes "retr rh wh \<sigma> = Q"
  shows "queued_count rh wh = q_size Q"
  using assms by (auto simp: retr_def retr_list_def)

subsection "Invariant, rely and guarantees"
text \<open>Coupling invariant between the abstract queue and concrete buffer.\<close>
definition I :: "'state set" where
  "I = \<llangle>\<exists>Q R W.
        \<acute>q = NatQueueValue Q \<and>
        \<acute>r = NatValue R \<and>
        \<acute>w = NatValue W \<and>
         R < N+1 \<and> W < N+1 \<and>
         q_size Q < N+1 \<and>
         (\<forall>i. \<exists>b. \<acute>(buffer_value i) = NatValue b) \<and>
         Q = \<acute>(retr R W)\<rrangle>"

lemma I_retr:
  assumes "s \<in> I" "r s = NatValue R" "w s = NatValue W"
  shows "q s = NatQueueValue (retr R W s)"
  using assms by (auto simp: I_def)

(* Need to make this reflexive so I can use it in assignment refinement lemmas. *)
definition enqueue_rely_dequeue_guar :: "('state \<times> 'state) set" where
  "enqueue_rely_dequeue_guar = \<llangle>\<ordmasculine>(\<lambda>\<sigma>. \<sigma>) = \<ordfeminine>(\<lambda>\<sigma>. \<sigma>)
                                \<or> (\<exists>W. \<ordmasculine>w = NatValue W
                                     \<and> \<ordfeminine>q suffix_of \<ordmasculine>q
                                     \<and> \<ordfeminine>w = \<ordmasculine>w
                                     \<and> \<ordmasculine>(buffer_value W) = \<ordfeminine>(buffer_value W))\<rrangle>"

lemma refl_enqueue_rely_dequeue_guar: "refl enqueue_rely_dequeue_guar"
  unfolding enqueue_rely_dequeue_guar_def
  apply (rule reflI) by simp

(* Same reflexivity issue. Due to type existentials.
Also, once the atomic is split into two operations, needs to rely that the value in buf r
does not change before the final atomic step that asserts that x contains buf[r] from the pre state.

However, this is not true in general since if R = W, then the writer needs to be able to write into
buf[r]..*)

definition enqueue_guar_dequeue_rely :: "('state \<times> 'state) set" where
"enqueue_guar_dequeue_rely = \<llangle>\<ordmasculine>(\<lambda>\<sigma>. \<sigma>) = \<ordfeminine>(\<lambda>\<sigma>. \<sigma>)
                              \<or> (\<exists>R. \<ordmasculine>r = NatValue R
                                   \<and> \<ordmasculine>q prefix_of \<ordfeminine>q
                                   \<and> \<ordfeminine>x = \<ordmasculine>x
                                   \<and> \<ordfeminine>r = \<ordmasculine>r
                                   \<and> (q_non_empty \<ordmasculine>q \<longrightarrow> q_non_empty \<ordfeminine>q)
                                   \<and> (q_non_empty \<ordmasculine>q \<longrightarrow> \<ordmasculine>(buffer_value R) = \<ordfeminine>(buffer_value R)))\<rrangle>"

lemma refl_enqueue_guar_dequeue_rely: "refl enqueue_guar_dequeue_rely"
  unfolding enqueue_guar_dequeue_rely_def
  apply (rule reflI) by simp

subsection \<open>Enqueue data refinement\<close>
abbreviation buf_written where
 "buf_written a \<equiv> \<llangle>\<exists>W. \<acute>w = NatValue W \<and> \<acute>(buffer_value W) = NatValue a\<rrangle>"

lemma refine_enqueue:
  "rely enqueue_rely_dequeue_guar
 \<iinter> guar\<^sub>\<pi> enqueue_guar_dequeue_rely
 \<iinter> enqueue_lvals:\<^sub>s\<langle>\<llangle>q_has_space \<acute>q\<rrangle>, \<llangle>\<ordfeminine>q = enqueue_lift \<ordmasculine>q (NatValue a)\<rrangle>, enqueue_lvals_term\<rangle>
 \<ge>\<^sub>I (buffer_at (*w_lve)) := Constant (NatValue a) open[A] ;
     w_lve := Unary circ_buf_pointer_increment (*w_lve) open[A]"
proof-
  let ?R = "(enqueue_rely_dequeue_guar \<inter> (- I \<triangleleft> UNIV \<union> UNIV \<triangleright> I))"

  have refl_R: "refl ?R" using refl_enqueue_rely_dequeue_guar inv_rely_refl
    by (metis refl_on_Int seq.inf_quantale.left_neutral)

  have stable_I: "stable I ?R"
    using inv_rely_stable by (metis Int_lower2 stable_antimono_r)

  have stable_buf_written: "stable (buf_written a) ?R"
    unfolding Image_def enqueue_rely_dequeue_guar_def by auto

  have stable_I_buf: "stable (I \<inter> buf_written a) ?R"
    using stable_inter[OF stable_I stable_buf_written] .

  have in_r_implies_w_const: "\<forall>(\<sigma>,\<sigma>') \<in> ?R. \<lbrakk>*w_lve\<rbrakk>\<sigma>' = \<lbrakk>*w_lve\<rbrakk>\<sigma>"
    by (simp only: eval_Deref_w) (auto simp: enqueue_rely_dequeue_guar_def)

  have buf_lv_invar: "invar_lval (buffer_at (*w_lve)) ?R"
    using in_r_implies_w_const 
    by (simp add: buffer_at_def buffer_lve_def w_lve_def in_r_implies_w_const)

  have w_inc_invar: "invar_expr (Unary circ_buf_pointer_increment (*w_lve)) ?R"
    using in_r_implies_w_const by (simp add: w_lve_def)

  let ?bufwlve_post = "\<lambda>lv. I \<inter> lval_eq (buffer_at (*w_lve)) lv"

  have intro_buf_assign:
      "rely enqueue_rely_dequeue_guar
     \<iinter> guar\<^sub>\<pi> enqueue_guar_dequeue_rely
     \<iinter> enqueue_lvals:\<^sub>s\<langle>\<llangle>q_has_space \<acute>q\<rrangle>,\<llangle>\<ordfeminine>q = enqueue_lift \<ordmasculine>q (NatValue a)\<rrangle>, enqueue_lvals_term\<rangle>
     \<ge>\<^sub>I
     buffer_at (*w_lve) := Constant (NatValue a) open[A] ;
     (rely enqueue_rely_dequeue_guar
    \<iinter> guar\<^sub>\<pi> enqueue_guar_dequeue_rely
    \<iinter> \<lbrace>buf_written a\<rbrace> ;
      enqueue_lvals:\<^sub>s\<langle>\<llangle>q_has_space \<acute>q\<rrangle>, \<llangle>\<ordfeminine>q = enqueue_lift \<ordmasculine>q (NatValue a)\<rrangle>, enqueue_lvals_term\<rangle>)"
  proof (rule data_refine_intro_local_atomic_open_assign_left_no_pre
      [where ?P1.0 = "?bufwlve_post"
         and ?P2.0 = "\<lambda>k. \<llangle>NatValue a = k\<rrangle>"
         and ?p1.0 = "buf_written a"])
    show "refl enqueue_rely_dequeue_guar" using refl_enqueue_rely_dequeue_guar .
    show "refl enqueue_guar_dequeue_rely" using refl_enqueue_guar_dequeue_rely .
    show "stable (buf_written a) ?R" using stable_buf_written .
    show "enqueue_lvals_term |\<subseteq>| enqueue_lvals" using term_lvals_subset .
    show "\<And>lv. {. I .} rely ?R \<iinter> \<ltort>buffer_at (*w_lve)\<rtort>lv {. I \<inter> lval_eq (buffer_at (*w_lve)) lv .}"
      using post_expr_invariant(2)[OF refl_R stable_I buf_lv_invar] .
    show "\<And>k. {. I .} rely ?R \<iinter> \<lblot>Constant (NatValue a)\<rblot>k {. \<llangle>NatValue a = k\<rrangle> .}"
      using post_constant_univ by auto
    show "\<And>k lv. (I \<inter> ?bufwlve_post lv \<inter> \<llangle>NatValue a = k\<rrangle>) \<triangleleft> open_update lv k A \<triangleright> I
               \<subseteq> (id_bar enqueue_lvals_term \<inter> enqueue_guar_dequeue_rely) \<triangleright> buf_written a"
    proof (rule subsetI)
      text \<open>Unpacking LHS.\<close>
      fix k lv ss
      assume ss_in: "ss \<in> (I \<inter> ?bufwlve_post lv \<inter> \<llangle>NatValue a = k\<rrangle>) \<triangleleft> open_update lv k A \<triangleright> I"
      obtain s s' where ss_eq: "ss = (s, s')" and
        pre: "s \<in> I \<inter> lval_eq (buffer_at (*w_lve)) lv \<inter> \<llangle>NatValue a = k\<rrangle>" and
        post_I: "s' \<in> I" and
        update_step: "(s, s') \<in> open_update lv k A"
        using ss_in by (auto simp: restrict_domain_def restrict_range_def)
      have pre_I: "s \<in> I" using pre by simp
      have pre_lval: "s \<in> lval_eq (buffer_at (*w_lve)) lv" using pre by simp
      have k_nat: "k = NatValue a" using pre by blast

      text \<open>Pre and post states are in invariant, so we can get types and the retr relation.\<close>
      obtain Q R W where
          q_pre: "q s = NatQueueValue Q" and
          r_pre: "r s = NatValue R" and
          w_pre: "w s = NatValue W" and
          R_bound: "R < N + 1" and
          W_bound: "W < N + 1" and
          q_bound: "q_size Q < N + 1" and
          retr_pre: "Q = retr R W s"
        using pre_I unfolding I_def by blast
      have count_bound: "queued_count R W < N + 1"
        using q_size_queued_count_equiv[OF retr_pre[symmetric]] q_bound
        by simp

      have lv_buf_w: "lv = buffer_at_lval W"
        using pre_lval w_pre by (simp add: lval_eq_def simp_vars)

      have lv_buf_lval: "lv |\<in>| buf_lvals"
        unfolding buf_lvals_def fset_of_list_elem set_map atLeastLessThan_upt
        by (rule image_eqI[where x=W]) (use W_bound lv_buf_w in auto)
      then have lv_term: "lv |\<in>| enqueue_lvals_term "
        by (simp add: enqueue_lvals_term_def)

      have var_nochange: "r s = r s' \<and> w s = w s' \<and> x s = x s'"
        by (simp_lvals add:lv_buf_w update_lval:update_step)
      have other_buffers_unchanged: "\<forall>i \<le> N. i \<noteq> W \<longrightarrow> buffer_value i s' = buffer_value i s"
        by (simp_lvals add:lv_buf_w update_lval:update_step)
      then have retr_same: "retr R W s = retr R W s'"
      proof-
        have write_index: "(R + queued_count R W) mod (N + 1) = W"
          by (rule queued_count_at_write[OF R_bound W_bound])
        have relative_buffers_unchanged:
          "\<forall>i < queued_count R W. buffer_value ((R + i) mod (N + 1)) s'
                                = buffer_value ((R + i) mod (N + 1)) s"
        by (metis Nat.add_0_right One_nat_def R_bound add_Suc_right circular_index_lt_ne
            count_bound mod_Suc_le_divisor other_buffers_unchanged write_index) 
              
        then show ?thesis 
          by (simp add: retr_def retr_list_def)
      qed

      have q_post: "q s' = NatQueueValue (retr R W s')"
        using I_retr[OF post_I] r_pre w_pre var_nochange by auto
      have q_nochange: "q s = q s'"
        using q_pre retr_pre retr_same q_post by simp

      have frame_single: "(s, s') \<in> id_bar {|lv|}"
        using simp_vars q_nochange open_update_case_no_abstract_change update_step lv_buf_w
        by auto
      then have frame: "(s, s') \<in> id_bar enqueue_lvals_term"
        using id_bar_narrow lv_term by auto

      have buffer_post: "buffer_value W s' = NatValue a"
        using open_update_lv_eq[OF update_step] lv_buf_w k_nat by (simp add: eval_Deref_buf)

      have post_buf_written: "s' \<in> buf_written a"
        using w_pre var_nochange buffer_post by auto
      have q_prefix: "q s prefix_of q s'"
        using q_nochange q_pre q_post q_prefix_of_def q_prefix_eq by fastforce
      have buffer_R:
        "q_non_empty (q s) \<longrightarrow> buffer_value R s = buffer_value R s'"
      proof
        assume q_nonempty: "q_non_empty (q s)"
        then have Q_nonempty: "\<not>is_empty Q"
          by (simp add: q_non_empty_def q_pre)
        have R_ne_W: "R \<noteq> W"
          using Q_nonempty retr_pre
          by (auto simp: retr_def retr_list_def queued_count_def)
        show "buffer_value R s = buffer_value R s'"
          using other_buffers_unchanged R_ne_W R_bound by auto
      qed
      have guar: "(s, s') \<in> enqueue_guar_dequeue_rely"
        unfolding enqueue_guar_dequeue_rely_def
        using ss_eq r_pre var_nochange q_prefix buffer_R q_nochange
        by auto
      show "ss \<in> (id_bar enqueue_lvals_term \<inter> enqueue_guar_dequeue_rely) \<triangleright> buf_written a"
        using ss_eq frame guar post_buf_written restrict_range_def by auto
    qed
  qed

  let ?w_inc_post = "\<lambda>k. I \<inter> buf_written a \<inter> expr_eq (Unary circ_buf_pointer_increment (*w_lve)) k"

  have data_refine_w_inc:
      "rely enqueue_rely_dequeue_guar
     \<iinter> guar\<^sub>\<pi> enqueue_guar_dequeue_rely
     \<iinter> \<lbrace>buf_written a\<rbrace> ;
       enqueue_lvals:\<^sub>s\<langle>\<llangle>q_has_space \<acute>q\<rrangle>,\<llangle>\<ordfeminine>q = enqueue_lift \<ordmasculine>q (NatValue a)\<rrangle>,enqueue_lvals_term\<rangle>
     \<ge>\<^sub>I w_lve := Unary circ_buf_pointer_increment (*w_lve) open[A]"
  proof (rule refine_local_atomic_from_atomic,
    rule chain_data_refine_framed_atomic_spec_to_open_assign_no_post
      [where ?P1.0 = "\<lambda>lv. \<llangle>lv = w_lval\<rrangle>" and ?P2.0 = "?w_inc_post"])
    show "refl enqueue_rely_dequeue_guar" using refl_enqueue_rely_dequeue_guar .
    show "refl enqueue_guar_dequeue_rely" using refl_enqueue_guar_dequeue_rely .
    show "\<And>lv. {. I \<inter> buf_written a .} rely ?R \<iinter> \<ltort>w_lve\<rtort>lv {. \<llangle>lv = w_lval\<rrangle> .}"
      unfolding w_simps using post_variable_univ by auto
    show "\<And>k. {. I \<inter> buf_written a .} rely ?R \<iinter> \<lblot>Unary circ_buf_pointer_increment (*w_lve)\<rblot>k
               {. ?w_inc_post k .}"
      using post_expr_invariant(1)[OF refl_R stable_I_buf w_inc_invar] .
    show "\<And>k lv. (I \<inter> \<llangle>q_has_space \<acute>q\<rrangle> \<inter> \<llangle>lv = w_lval\<rrangle> \<inter> ?w_inc_post k) \<triangleleft> open_update lv k A \<triangleright> I
          \<subseteq> id_bar enqueue_lvals \<inter> enqueue_guar_dequeue_rely \<inter> \<llangle>\<ordfeminine>q = enqueue_lift \<ordmasculine>q (NatValue a)\<rrangle>"
    proof (rule subsetI)
      fix k lv ss
      text \<open>Unpacking LHS.\<close>
      assume ss_in:
        "ss \<in> (I \<inter> \<llangle>q_has_space \<acute>q\<rrangle> \<inter> \<llangle>lv = w_lval\<rrangle> \<inter> ?w_inc_post k) \<triangleleft> open_update lv k A \<triangleright> I"
      obtain s s' where ss_eq: "ss = (s, s')" and
        pre: "s \<in> I \<inter> \<llangle>q_has_space \<acute>q\<rrangle> \<inter> \<llangle>lv = w_lval\<rrangle> \<inter> ?w_inc_post k" and
        post_I: "s' \<in> I" and
        update_step: "(s, s') \<in> open_update lv k A"
        using ss_in by (auto simp: restrict_domain_def restrict_range_def)
      have lv_w: "lv = w_lval" using pre by blast
      have w_update: "(s,s') \<in> open_update w_lval k A"
        using update_step lv_w by simp

      text \<open>Pre and post states in invariant, so get types and retr.\<close>
      obtain Q R W where
          q_pre: "q s = NatQueueValue Q" and
          r_pre: "r s = NatValue R" and
          w_pre: "w s = NatValue W" and
          R_bound: "R < N + 1" and
          W_bound: "W < N + 1" and
          q_size_lt_N: "q_size Q < N" and
          written_buffer: "buffer_value W s = NatValue a" and
          retr_pre: "Q = retr R W s"
        using pre unfolding I_def q_has_space_def by fastforce
      obtain Q' R' W' where
          q_post: "q s' = NatQueueValue Q'" and
          r_post: "r s' = NatValue R'" and
          w_post: "w s' = NatValue W'" and
          retr_post: "Q' = retr R' W' s'"
        using post_I unfolding I_def by blast
      have count_bound: "queued_count R W < N"
        using q_size_queued_count_equiv[OF retr_pre[symmetric]] q_size_lt_N by simp


      have var_nochange: "r s = r s' \<and> x s = x s'
                       \<and> (\<forall>i. buffer_value i s = buffer_value i s')"
        by (simp_lvals update_lval:w_update)
      then have R'_eq: "R' = R"
        using r_pre r_post by simp

      have w_increment:
          "w s' = circ_buf_pointer_increment (w s)"
        using w_simps pre open_update_lv_eq[OF w_update] expr_eq_def by auto
      then have W'_eq: "W' = (W + 1) mod (N + 1)"
        using w_pre w_post by simp
      have buffer_post: "buffer_value W s' = NatValue a"
        using written_buffer var_nochange by simp

      have Q'_eq: "Q' = enqueue Q a"
        using retr_enqueue1[OF R_bound W_bound count_bound buffer_post]
              var_nochange retr_unchanged retr_pre retr_post R'_eq W'_eq by metis
      then have abstract_step: "(s, s') \<in> \<llangle>\<ordfeminine>q = enqueue_lift \<ordmasculine>q (NatValue a)\<rrangle>"
        using q_pre q_post by simp

      have frame_vars: "finsert lv A |\<subseteq>| enqueue_lvals"
        using lv_w by (simp add: enqueue_lvals_def)
      have frame: "(s, s') \<in> id_bar enqueue_lvals"
        using update_step open_update_in_frame[OF frame_vars] by blast

      have q_prefix: "q s prefix_of q s'"
        using q_pre q_post Q'_eq by (cases Q; simp add: q_prefix_of_def)
      have guar: "(s, s') \<in> enqueue_guar_dequeue_rely"
        unfolding enqueue_guar_dequeue_rely_def
        using r_pre var_nochange q_prefix q_pre q_post Q'_eq
        by (cases Q; auto simp: q_non_empty_def)

      show "ss \<in> id_bar enqueue_lvals \<inter> enqueue_guar_dequeue_rely
               \<inter> \<llangle>\<ordfeminine>q = enqueue_lift \<ordmasculine>q (NatValue a)\<rrangle>"
        using ss_eq frame guar abstract_step by auto
    qed

  qed

  then show ?thesis using intro_buf_assign
    by (meson data_refine_refl data_refine_seq data_refine_trans)
qed


subsection \<open>Dequeue data refinement\<close>

abbreviation buf_read where
 "buf_read \<equiv> \<llangle>\<exists>R. \<acute>r = NatValue R \<and> \<acute>x = \<acute>(buffer_value R) \<and> q_non_empty \<acute>q\<rrangle>"

lemma refine_dequeue:
   "rely enqueue_guar_dequeue_rely
  \<iinter> guar\<^sub>\<pi> enqueue_rely_dequeue_guar
  \<iinter> \<lbrace>\<llangle>q_non_empty \<acute>q\<rrangle>\<rbrace> ;
    dequeue_lvals:\<^sub>s\<langle>\<top>, \<llangle>\<ordmasculine>q = concat_front \<ordfeminine>x \<ordfeminine>q\<rrangle>, dequeue_lvals_term\<rangle>
 \<ge>\<^sub>I
    x_lve := (*(buffer_at (*r_lve))) open[A] ;
    r_lve := Unary circ_buf_pointer_increment (*r_lve) open[A]"
proof-
  text \<open>Stability and invariant expr/lval facts under the rely.\<close>
  let ?R = "enqueue_guar_dequeue_rely \<inter> (- I \<triangleleft> UNIV \<union> UNIV \<triangleright> I)"
  have stable_buf_read: "stable buf_read ?R"
    unfolding Image_def enqueue_guar_dequeue_rely_def by auto

  let ?IQ = "I \<inter> \<llangle>q_non_empty \<acute>q\<rrangle>"
  let ?RIQ = "?IQ \<triangleleft> ?R \<triangleright> ?IQ"
  let ?bufrpost = "\<lambda>k. ?IQ \<inter> expr_eq (*(buffer_at (*r_lve))) k"

  have refl_R: "refl ?R"
    using refl_enqueue_guar_dequeue_rely inv_rely_refl
    by (metis refl_on_Int seq.inf_quantale.left_neutral)

  have stable_Q_nonempty: "stable \<llangle>q_non_empty \<acute>q\<rrangle> ?R"
    unfolding Image_def enqueue_guar_dequeue_rely_def by auto
  have stable_I: "stable I ?R"
    using inv_rely_stable by fastforce
  then have stable_IQ: "stable ?IQ ?R"
    using stable_Q_nonempty by auto

  have stable_I_bufread: "stable (I \<inter> buf_read) ?R"
    using stable_I stable_buf_read by blast

  have in_R_implies_r_const: "\<forall>(\<sigma>,\<sigma>') \<in> ?R. \<lbrakk>*r_lve\<rbrakk>\<sigma>' = \<lbrakk>*r_lve\<rbrakk>\<sigma>"
    by (simp only: eval_Deref_r) (auto simp: enqueue_guar_dequeue_rely_def)

  have bufr_invar_q_nonempty: "invar_expr (*(buffer_at (*r_lve))) ?RIQ"
    by (auto simp: restrict_domain_def restrict_range_def
        enqueue_guar_dequeue_rely_def simp_vars)

  text \<open>Refine the framed terminate on the left of the local atomic into the operation that assigns
x the value in buf[r].\<close>
  have intro_x_assign: "rely enqueue_guar_dequeue_rely
                      \<iinter> guar\<^sub>\<pi> enqueue_rely_dequeue_guar
                      \<iinter> \<lbrace>\<llangle>q_non_empty \<acute>q\<rrangle>\<rbrace> ;
                        dequeue_lvals:\<^sub>s\<langle>\<top>, \<llangle>\<ordmasculine>q = concat_front \<ordfeminine>x \<ordfeminine>q\<rrangle>, dequeue_lvals_term\<rangle>
                    \<ge>\<^sub>I  x_lve := (*(buffer_at (*r_lve))) open[A] ;
                        (rely enqueue_guar_dequeue_rely
                       \<iinter> guar\<^sub>\<pi> enqueue_rely_dequeue_guar
                       \<iinter> \<lbrace>buf_read\<rbrace> ;
                         dequeue_lvals:\<^sub>s\<langle>\<top>, \<llangle>\<ordmasculine>q = concat_front \<ordfeminine>x \<ordfeminine>q\<rrangle>, dequeue_lvals_term\<rangle>)"
  proof(rule data_refine_intro_local_atomic_open_assign_left
          [where ?P1.0="\<lambda>lv. \<llangle>lv = x_lval\<rrangle>" and
                 ?P2.0="?bufrpost"])
    show "refl enqueue_guar_dequeue_rely" using refl_enqueue_guar_dequeue_rely .
    show "refl enqueue_rely_dequeue_guar" using refl_enqueue_rely_dequeue_guar .
    show "dequeue_lvals_term |\<subseteq>| dequeue_lvals"
      by (simp add: dequeue_lvals_def dequeue_lvals_term_def)
    show "stable buf_read ?R" using stable_buf_read .
    show "\<And>lv. {. ?IQ .} rely ?R \<iinter> \<ltort>x_lve\<rtort>lv {. \<llangle>lv = x_lval\<rrangle> .}"
      unfolding x_simps using post_variable_univ by auto
    show "\<And>k. {. ?IQ .} rely ?R \<iinter> \<lblot>*(buffer_at (*r_lve))\<rblot>k {. ?bufrpost k .}"
      using post_expr_invariant_rely_pre(1) [OF refl_R stable_IQ bufr_invar_q_nonempty] by simp
    show "\<And>k lv. (I \<inter> \<llangle>lv = x_lval\<rrangle> \<inter> ?bufrpost k) \<triangleleft> open_update lv k A \<triangleright> I
               \<subseteq> (id_bar dequeue_lvals_term \<inter> enqueue_rely_dequeue_guar) \<triangleright> buf_read"
    proof (rule subsetI)
      fix k lv ss
      assume ss_in: "ss \<in> (I \<inter> \<llangle>lv = x_lval\<rrangle> \<inter> ?bufrpost k) \<triangleleft> open_update lv k A \<triangleright> I"
      obtain s s' where ss_eq: "ss = (s, s')" and
        pre: "s \<in> I \<inter> \<llangle>lv = x_lval\<rrangle> \<inter> ?bufrpost k" and
        post: "s' \<in> I" and
        update_step: "(s,s') \<in> open_update lv k A"
        using ss_in by (auto simp: restrict_domain_def restrict_range_def)
      have lv_x: "lv = x_lval" using pre by blast
      have x_update: "(s,s') \<in> open_update x_lval k A"
        using update_step lv_x by simp

      obtain Q R W where
        q_pre: "q s = NatQueueValue Q" and
        r_pre: "r s = NatValue R" and
        w_pre: "w s = NatValue W" and
        retr_pre: "Q = retr R W s"
        using pre unfolding I_def by blast
      have q_nonempty_pre: "q_non_empty (q s)"
        using pre by auto


      have var_nochange: "r s = r s'
                        \<and> w s = w s'
                        \<and> (\<forall>i. buffer_value i s = buffer_value i s')"
        by (simp_lvals update_lval:x_update)
      then have q_nochange: "q s = q s'"
        using I_retr[OF post] q_pre retr_pre r_pre w_pre retr_unchanged by metis

      have "\<lbrakk>*(buffer_at (*r_lve))\<rbrakk>s = buffer_value R s"
        using r_pre simp_vars by auto
      then have k_is_buffer_value: "k = buffer_value R s"
        using pre by (auto simp: expr_eq_def)

      have x_post: "x s' = k"
        using open_update_lv_eq x_update x_simps by auto

      have post_buf_read: "s' \<in> buf_read"
        using r_pre var_nochange q_nonempty_pre q_nochange k_is_buffer_value
          var_nochange x_post by auto

      have frame: "(s,s') \<in> id_bar dequeue_lvals_term"
        using open_update_case_no_abstract_change x_update q_nochange
        by (simp add: dequeue_lvals_term_def q_def)

      have q_suffix: "q s' suffix_of q s"
        using q_pre q_nochange q_suffix_of_def q_suffix_eq by simp

      show "ss \<in> (id_bar dequeue_lvals_term \<inter> enqueue_rely_dequeue_guar) \<triangleright> buf_read"
        unfolding restrict_range_def enqueue_rely_dequeue_guar_def
        using ss_eq frame post_buf_read w_pre q_suffix var_nochange
        by fastforce
    qed
  qed

  have r_inc_invar: "invar_expr (Unary circ_buf_pointer_increment (*r_lve)) ?R"
    using in_R_implies_r_const by (simp add: r_lve_def)

  let ?r_inc_post = "\<lambda>k. I \<inter> buf_read \<inter> expr_eq (Unary circ_buf_pointer_increment (*r_lve)) k"

  text \<open>Refine the local atomic to an atomic, then refine it to the r increment assignment.\<close>
  have data_refine_r_inc: "rely enqueue_guar_dequeue_rely
                         \<iinter> guar\<^sub>\<pi> enqueue_rely_dequeue_guar
                         \<iinter> \<lbrace>buf_read\<rbrace> ;
                           dequeue_lvals:\<^sub>s\<langle>\<top>, \<llangle>\<ordmasculine>q = concat_front \<ordfeminine>x \<ordfeminine>q\<rrangle>, dequeue_lvals_term\<rangle>
                        \<ge>\<^sub>I r_lve := Unary circ_buf_pointer_increment (*r_lve) open[A]"
  proof (rule refine_local_atomic_from_atomic,
    rule chain_data_refine_framed_atomic_spec_to_open_assign_no_post
      [where ?P1.0="\<lambda>lv. \<llangle>lv = r_lval\<rrangle>" and ?P2.0="?r_inc_post"])
    show "refl enqueue_guar_dequeue_rely" using refl_enqueue_guar_dequeue_rely .
    show "refl enqueue_rely_dequeue_guar" using refl_enqueue_rely_dequeue_guar .
    show "\<And>lv. {. I \<inter> buf_read .} rely ?R \<iinter> \<ltort>r_lve\<rtort>lv {. \<llangle>lv = r_lval\<rrangle> .}"
      unfolding r_simps using post_variable_univ by auto
    show "\<And>k. {. I \<inter> buf_read .} rely ?R \<iinter> \<lblot>Unary circ_buf_pointer_increment (*r_lve)\<rblot>k
               {. ?r_inc_post k .}"
      using post_expr_invariant(1) r_inc_invar refl_R stable_I_bufread by blast
    show "\<And>k lv. (I \<inter> UNIV \<inter> \<llangle>lv = r_lval\<rrangle> \<inter> ?r_inc_post k) \<triangleleft> open_update lv k A \<triangleright> I
               \<subseteq> id_bar dequeue_lvals \<inter> enqueue_rely_dequeue_guar \<inter> \<llangle>\<ordmasculine>q = concat_front \<ordfeminine>x \<ordfeminine>q\<rrangle>"
    proof (rule subsetI)
      fix k lv ss
      assume ss_in: "ss \<in> (I \<inter> UNIV \<inter> \<llangle>lv = r_lval\<rrangle> \<inter> ?r_inc_post k) \<triangleleft> open_update lv k A \<triangleright> I"
      obtain s s' where ss_eq: "ss = (s, s')" and
        pre: "s \<in> I \<inter> UNIV \<inter> \<llangle>lv = r_lval\<rrangle> \<inter> ?r_inc_post k" and
        post_I: "s' \<in> I" and
        update_step: "(s,s') \<in> open_update lv k A"
        using ss_in by (auto simp: restrict_domain_def restrict_range_def)
      have lv_r: "lv = r_lval" using pre by blast
      have r_update: "(s,s') \<in> open_update r_lval k A"
        using update_step lv_r by simp

      obtain Q R W b where
          q_pre: "q s = NatQueueValue Q" and
          r_pre: "r s = NatValue R" and
          w_pre: "w s = NatValue W" and
          R_bound: "R < N + 1" and
          W_bound: "W < N + 1" and
          retr_pre: "Q = retr R W s" and
          read_x: "x s = buffer_value R s" and
          q_nonempty: "\<not> is_empty Q" and
          buffer_R: "buffer_value R s = NatValue b"
        using pre q_non_empty_def unfolding I_def by fastforce
      obtain Q' R' W' where
          q_post: "q s' = NatQueueValue Q'" and
          r_post: "r s' = NatValue R'" and
          w_post: "w s' = NatValue W'" and
          retr_post: "Q' = retr R' W' s'"
        using post_I unfolding I_def by blast

      have var_nochange: "w s = w s' \<and> x s = x s' \<and> (\<forall>i. buffer_value i s = buffer_value i s')"
        by (simp_lvals update_lval:r_update)
      then have x_post: "x s' = buffer_value R s"
        using read_x by auto
      have r_increment: "r s' = circ_buf_pointer_increment (r s)"
        using r_simps pre open_update_lv_eq[OF r_update] expr_eq_def by auto

      have abstract_step: "(s,s') \<in> \<llangle>\<ordmasculine>q = concat_front \<ordfeminine>x \<ordfeminine>q\<rrangle>"
      proof -
        have count_pos: "0 < queued_count R W"
        using q_nonempty retr_pre
        by (auto simp: retr_def retr_list_def)
        have R'_eq: "R' = (R + 1) mod (N + 1)"
          using r_post r_increment r_pre by simp
        have W'_eq: "W' = W"
          using w_post var_nochange w_pre by simp
        have read_nat: "the (as_nat (buffer_value R s)) = b"
          using buffer_R by simp
        have "retr R W s = q_concat_front b (retr ((R + 1) mod (N + 1)) W s')"
          using retr_dequeue1 R_bound W_bound count_pos var_nochange read_nat by metis
        then have "q s = concat_front (x s') (q s')"
          using q_pre q_post x_post buffer_R  retr_pre retr_post R'_eq W'_eq by simp
        then show ?thesis by auto
      qed

      have frame_vars: "finsert lv A |\<subseteq>| dequeue_lvals"
        using lv_r by (simp add: dequeue_lvals_def)
      have frame: "(s,s') \<in> id_bar dequeue_lvals"
        using update_step open_update_in_frame[OF frame_vars] by blast

      have "q_suffix Q' (q_concat_front b Q')"
        by (cases Q'; auto simp: suffix_def)
      then have "q s' suffix_of q s"
        using q_pre q_post x_post buffer_R abstract_step by (simp add: q_suffix_of_def)
      then have rely: "(s,s') \<in> enqueue_rely_dequeue_guar"
        unfolding enqueue_rely_dequeue_guar_def
        using w_pre var_nochange by auto

      show "ss \<in> id_bar dequeue_lvals \<inter> enqueue_rely_dequeue_guar \<inter> \<llangle>\<ordmasculine>q = concat_front \<ordfeminine>x \<ordfeminine>q\<rrangle>"
        using ss_eq frame rely abstract_step by auto
    qed

  qed

  then show ?thesis using intro_x_assign
    by (meson data_refine_refl data_refine_seq data_refine_trans)
qed

(*Surrounding context

while 
enqueue_lvals:\<^sub>s\<langle>\<llangle>q_has_space \<acute>q\<rrangle>, \<llangle>\<ordfeminine>q = enqueue_lift \<ordmasculine>q (NatValue a)\<rrangle>, enqueue_lvals_term\<rangle>

|| 
while (Constant BoolValue True) do
  if () fi
od
*)



end
end
