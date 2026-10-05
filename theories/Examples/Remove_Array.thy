section \<open>Example: Remove an element from a set\<close>

text \<open>Data refinement example written using ChatGPT 6 Astra and Codex.
Chat log can be found here:
https://chatgpt.com/s/cx_6abf833e15388191b520e406ec0acaa5\<close>

theory Remove_Array
  imports Typed_State Commands.Data_Refinement
begin

fun extract_set_from_word :: "64 word \<Rightarrow> nat set"
  where "extract_set_from_word w = {i::nat. bit w i}"

text \<open>Number of array words.\<close>
consts N :: nat

abbreviation word_bit where
  "word_bit \<equiv> lift2 as_word64 as_nat BoolValue bit"

abbreviation word_unset_bit where
  "word_unset_bit \<equiv> lift2 as_word64 as_nat Word64Value (\<lambda>w i. unset_bit i w)"

abbreviation set_difference where
  "set_difference \<equiv> lift2 as_nat_set as_nat_set NatSetValue (-)"

abbreviation set_member where
  "set_member \<equiv> lift2 as_nat_set as_nat BoolValue (\<lambda>s i. i \<in> s)"

context typed_frame_state
begin

subsection \<open>Define variables\<close>
define_var s
define_var arr

fun retr :: "(nat \<Rightarrow> 64 word) \<Rightarrow> nat set" where
  "retr Ws = (\<Union>i\<in>{..<N}. (\<lambda>j. i*64 + j) ` extract_set_from_word (Ws i))"

declare retr.simps [simp del]

definition arr_at_lve ::
  "('state, typed_value) Expr \<Rightarrow> ('state, typed_value) LValueExpr"
where
  "arr_at_lve i = ArrayRef arr_lve i"

definition arr_at :: "nat \<Rightarrow> 'state \<Rightarrow> typed_value" where
  "arr_at i \<sigma> = \<lbrakk>Deref (arr_at_lve (Constant (NatValue i)))\<rbrakk> \<sigma>"

definition arr_at_lval :: "nat \<Rightarrow> typed_value LValue" where
  "arr_at_lval i = Indexed arr_lval (NatValue i)"

declare arr_at_def [simp_vars]
declare arr_at_lve_def [simp_vars]
declare arr_at_lval_def [simp_vars]

definition I :: "'state set" where
  "I = \<llangle>\<exists>S (Ws :: nat \<Rightarrow> 64 word).
        (\<forall>i. \<acute>(arr_at i) = Word64Value (Ws i)) \<and>
        \<acute>s = NatSetValue S \<and>
        S = retr Ws\<rrangle>"

subsection \<open>Retrieval lemmas\<close>

lemma word_bit_bound:
  "bit (w :: 64 word) j \<Longrightarrow> j < 64"
  using bit_imp_le_length by fastforce

lemma retr_member:
  "x \<in> retr Ws \<longleftrightarrow> x div 64 < N \<and> bit (Ws (x div 64)) (x mod 64)"
proof
  assume "x \<in> retr Ws"
  then obtain i j where "i < N" "bit (Ws i) j" "x = i*64 + j" by (auto simp: retr.simps)
  then show "x div 64 < N \<and> bit (Ws (x div 64)) (x mod 64)"
    using word_bit_bound by auto
next
  assume "x div 64 < N \<and> bit (Ws (x div 64)) (x mod 64)"
  then have "x div 64 * 64 + x mod 64 \<in> retr Ws"
    unfolding retr.simps extract_set_from_word.simps by blast
  then show "x \<in> retr Ws" by simp
qed

lemma retr_unset_bit:
  "retr (fun_upd Ws (i div 64) (unset_bit (i mod 64) (Ws (i div 64)))) = retr Ws - {i}"
  by (auto simp: set_eq_iff retr_member bit_unset_bit_iff)
     (metis div_mult_mod_eq)

lemma retr_word_eq:
  assumes "retr Ws = retr Vs" "k < N"
  shows "Ws k = Vs k"
proof (rule bit_eqI)
  fix j
  show "bit (Ws k) j \<longleftrightarrow> bit (Vs k) j"
  proof (cases "j < 64")
    case True
    have "k*64+j \<in> retr Ws \<longleftrightarrow> k*64+j \<in> retr Vs"
      using assms by simp
    then show ?thesis using True assms(2) by (simp add: retr_member)
  next
    case False
    then show ?thesis using word_bit_bound by blast
  qed
qed

lemma I_word_determined:
  assumes "\<sigma> \<in> I" "\<sigma>' \<in> I" "s \<sigma> = s \<sigma>'" "k < N"
  shows "arr_at k \<sigma> = arr_at k \<sigma>'"
  using assms retr_word_eq unfolding I_def by fastforce

lemma I_member:
  assumes "\<sigma> \<in> I" "i div 64 < N"
  shows "set_member (s \<sigma>) (NatValue i) =
         word_bit (arr_at (i div 64) \<sigma>) (NatValue (i mod 64))"
  using assms by (auto simp: I_def retr_member)

lemma array_frame_unchanged:
  assumes "(\<sigma>,\<sigma>') \<in> id_bar {|s_lval, arr_at_lval k|}" "j \<noteq> k"
  shows "arr_at j \<sigma> = arr_at j \<sigma>'"
  using assms by (auto simp: id_bar_def id_bar_pred_def simp_vars)

lemma I_array_update:
  assumes pre: "\<sigma> \<in> I" and post: "\<sigma>' \<in> I"
      and frame: "(\<sigma>,\<sigma>') \<in> id_bar {|s_lval, arr_at_lval (i div 64)|}"
      and update: "arr_at (i div 64) \<sigma>' = word_unset_bit (arr_at (i div 64) \<sigma>) (NatValue (i mod 64))"
  shows "s \<sigma>' = set_difference (s \<sigma>) (NatSetValue {i})"
proof -
  obtain Ws Vs where W: "\<forall>j. arr_at j \<sigma> = Word64Value (Ws j)"
      "s \<sigma> = NatSetValue (retr Ws)"
    and V: "\<forall>j. arr_at j \<sigma>' = Word64Value (Vs j)"
      "s \<sigma>' = NatSetValue (retr Vs)"
    using pre post by (auto simp: I_def)
  have "Vs = fun_upd Ws (i div 64) (unset_bit (i mod 64) (Ws (i div 64)))"
    using W V update array_frame_unchanged[OF frame]
    by (intro ext) (auto split: if_splits)
  then show ?thesis using W V retr_unset_bit by simp
qed

lemma I_array_unchanged:
  assumes "\<sigma> \<in> I" "\<sigma>' \<in> I"
      "(\<sigma>,\<sigma>') \<in> id_bar {|s_lval, arr_at_lval k|}"
      "arr_at k \<sigma>' = arr_at k \<sigma>"
  shows "s \<sigma>' = s \<sigma>"
proof -
  have "\<forall>j. arr_at j \<sigma> = arr_at j \<sigma>'"
    using assms array_frame_unchanged by metis
  moreover obtain Ws Vs where
    W: "\<forall>j. arr_at j \<sigma> = Word64Value (Ws j)" "s \<sigma> = NatSetValue (retr Ws)"
    and V: "\<forall>j. arr_at j \<sigma>' = Word64Value (Vs j)" "s \<sigma>' = NatSetValue (retr Vs)"
    using assms(1,2) by (auto simp: I_def)
  ultimately have "Ws = Vs" by (intro ext) fastforce
  then show ?thesis using W V by simp
qed

subsection \<open>Algebraic helpers for compare-and-swap\<close>

definition cas_rel where
  "cas_rel v f k = {(\<sigma>,\<sigma>'). v \<sigma>' = (if v \<sigma> = k then f k else v \<sigma>)}"

definition cas_body where
  "cas_body v f F = (\<Squnion>k. idle ; \<tau>{\<sigma>. v \<sigma> = k} ; idle ;
     opt (F \<inter> cas_rel v f k) ; idle)"

lemma opt_UNION:
  "opt (\<Union>k. Q k) = (\<Squnion>k. opt (Q k))"
proof -
  have diagonal: "{\<sigma>. (\<sigma>,\<sigma>) \<in> (\<Union>k. Q k)} = (\<Union>k. {\<sigma>. (\<sigma>,\<sigma>) \<in> Q k})" by auto
  show ?thesis unfolding opt_def diagonal
    apply (simp only: pgm.hom_Sup seq.test.hom_Sup SUP_image comp_def)
    apply (rule SUP_sup_distrib[of UNIV, simplified])
    apply simp_all
    done
qed

lemma opt_union:
  "opt (Q \<union> R) = opt Q \<squnion> opt R"
proof -
  have diagonal: "{\<sigma>. (\<sigma>,\<sigma>) \<in> Q \<union> R} =
    {\<sigma>. (\<sigma>,\<sigma>) \<in> Q} \<union> {\<sigma>. (\<sigma>,\<sigma>) \<in> R}" by auto
  show ?thesis unfolding opt_def diagonal
    by (simp only: pgm.hom_sup[symmetric] seq.test.hom_sup[symmetric]
        sup_assoc sup_left_commute sup_commute)
qed

lemma cas_body_idle:
  "idle ; cas_body v f F = cas_body v f F"
  unfolding cas_body_def
  by (simp add: seq.op_Sup_UNIV seq_par.seq_assoc[symmetric] idle_seq_idle)

lemma cas_body_atomic:
  "cas_body v f F \<ge> \<langle>UNIV, F \<inter> {(\<sigma>,\<sigma>'). v \<sigma>' = f (v \<sigma>)}\<rangle>"
proof -
  have partition: "F \<inter> {(\<sigma>,\<sigma>'). v \<sigma>' = f (v \<sigma>)} =
      (\<Union>k. {\<sigma>. v \<sigma> = k} \<triangleleft> (F \<inter> cas_rel v f k))"
    by (auto simp: cas_rel_def restrict_domain_def)
  have insert_idle: "c ; d \<le> c ; idle ; d" for c d
  proof -
    have "c ; nil ; d \<le> c ; idle ; d"
      by (intro seq.seq_mono idle_ref_nil order_refl)
    then show ?thesis by simp
  qed
  have "idle ; opt ({\<sigma>. v \<sigma> = k} \<triangleleft> (F \<inter> cas_rel v f k)) ; idle
      \<le> idle ; \<tau>{\<sigma>. v \<sigma> = k} ; idle ; opt (F \<inter> cas_rel v f k) ; idle" for k
    unfolding test_seq_opt[symmetric]
    by (simp only: seq.seq_assoc[symmetric]; rule seq.seq_mono_left; rule insert_idle)
  then show ?thesis
    unfolding cas_body_def atomic_spec_def partition opt_UNION
    by (simp add: seq.assert_neut seq.op_Sup_UNIV seq.Sup_UNIV_op SUP_mono')
qed

text \<open>The abstract read may be delayed until a successful concrete update.
For a failed update, an abstract snapshot taken with the concrete read is already
different from the current abstract value. This allows unrelated array words to
change between the read and the compare-and-swap.\<close>

lemma cas_body_data_refine:
  assumes determines: "\<And>\<sigma> \<sigma>'. \<sigma> \<in> J \<Longrightarrow> \<sigma>' \<in> J \<Longrightarrow>
      a \<sigma> = a \<sigma>' \<Longrightarrow> b \<sigma> = b \<sigma>'"
      and success: "J \<triangleleft> (F \<inter> {(\<sigma>,\<sigma>'). b \<sigma>' = g (b \<sigma>)}) \<triangleright> J
        \<subseteq> F \<inter> {(\<sigma>,\<sigma>'). a \<sigma>' = f (a \<sigma>)}"
      and failure: "J \<triangleleft> (F \<inter> {(\<sigma>,\<sigma>'). b \<sigma>' = b \<sigma>}) \<triangleright> J
        \<subseteq> {(\<sigma>,\<sigma>'). a \<sigma>' = a \<sigma>}"
  shows "cas_body a f F \<ge>\<^sub>J cas_body b g F"
proof -
  let ?A = "cas_body a f F"
  have succeeds: "?A \<ge>\<^sub>J \<langle>UNIV, F \<inter> {(\<sigma>,\<sigma>'). b \<sigma>' = g (b \<sigma>)}\<rangle>"
    by (rule data_refine_trans[OF refsto_implies_data_refine[OF cas_body_atomic]])
       (rule data_refine_atomic_spec; use success in auto)
  have step: "?A \<ge>\<^sub>J idle ; \<tau>{\<sigma>. b \<sigma> = w} ; idle ;
      opt (F \<inter> cas_rel b g w) ; idle" for w
  proof -
    let ?S = "F \<inter> {(\<sigma>,\<sigma>'). b \<sigma> = w \<and> b \<sigma>' = g w}"
    let ?T = "F \<inter> {(\<sigma>,\<sigma>'). b \<sigma> \<noteq> w \<and> b \<sigma>' = b \<sigma>}"
    let ?P = "\<lambda>k. J \<inter> {\<sigma>. a \<sigma> = k \<and> b \<sigma> = w}"
    have s_ref: "?A \<ge>\<^sub>J idle ; \<tau>{\<sigma>. b \<sigma> = w} ; idle ; opt ?S ; idle"
    proof (rule data_refine_trans[OF succeeds], rule refsto_implies_data_refine)
      have "opt ?S \<le> opt (F \<inter> {(\<sigma>,\<sigma>'). b \<sigma>' = g (b \<sigma>)})"
        by (rule opt_mono) auto
      then show "\<langle>UNIV, F \<inter> {(\<sigma>,\<sigma>'). b \<sigma>' = g (b \<sigma>)}\<rangle>
          \<ge> idle ; \<tau>{\<sigma>. b \<sigma> = w} ; idle ; opt ?S ; idle"
        unfolding atomic_spec_def
        by (simp only: seq.assert_neut seq.right_neutral;
            intro seq.seq_mono order_refl idle_intro_test)
    qed
    have fail_k: "?A \<ge>\<^sub>J idle ; \<tau>(?P k) ; idle ; opt ?T ; idle" for k
    proof (cases "?P k = {}")
      case True
      have "idle ; \<bottom> \<le> idle ; ?A"
        by (rule seq.seq_mono_right) simp
      then show ?thesis unfolding True
        by (simp add: seq.test_bot seq.seq_assoc seq.bot_annihilates_left cas_body_idle
            refsto_implies_data_refine)
    next
      case False
      then obtain \<sigma> where snapshot: "\<sigma> \<in> J" "a \<sigma> = k" "b \<sigma> = w" by blast
      have rel: "J \<triangleleft> ?T \<triangleright> J \<subseteq> F \<inter> cas_rel a f k"
      proof
        fix ss
        assume "ss \<in> J \<triangleleft> ?T \<triangleright> J"
        then obtain x y where ss: "ss = (x,y)" and xy: "x \<in> J" "y \<in> J"
            "(x,y) \<in> F" "b x \<noteq> w" "b y = b x"
          by (auto simp: restrict_domain_def restrict_range_def)
        have unchanged: "a y = a x"
          using failure xy by (auto simp: restrict_domain_def restrict_range_def)
        have different: "a x \<noteq> k"
          using determines[OF snapshot(1) xy(1)] snapshot xy(4) by metis
        show "ss \<in> F \<inter> cas_rel a f k"
          using ss xy(3) unchanged different by (simp add: cas_rel_def)
      qed
      have member: "?A \<ge> idle ; \<tau>{\<sigma>. a \<sigma> = k} ; idle ; opt (F \<inter> cas_rel a f k) ; idle"
        unfolding cas_body_def by (rule SUP_upper) simp
      show ?thesis
        apply (rule data_refine_trans[OF refsto_implies_data_refine[OF member]])
        apply (intro data_refine_seq data_refine_refl)
        subgoal by (rule data_refine_test) auto
        subgoal by (rule data_refine_opt[OF rel])
        done
    qed
    have fail_sup: "?A \<ge>\<^sub>J (\<Squnion>k. idle ; \<tau>(?P k) ; idle ; opt ?T ; idle)"
      using data_refine_SUP[of UNIV "\<lambda>_. ?A" J "\<lambda>k. idle ; \<tau>(?P k) ; idle ; opt ?T ; idle"] fail_k
      by simp
    have partition: "(\<Union>k. ?P k) = J \<inter> {\<sigma>. b \<sigma> = w}" by auto
    have split: "(\<Squnion>k. idle ; \<tau>(?P k) ; idle ; opt ?T ; idle) =
        idle ; \<tau>(J \<inter> {\<sigma>. b \<sigma> = w}) ; idle ; opt ?T ; idle"
      by (simp only: partition[symmetric] seq.test.hom_Sup SUP_image comp_def
          seq.op_Sup_UNIV seq.Sup_UNIV_op)
    have t_ref: "?A \<ge>\<^sub>J idle ; \<tau>{\<sigma>. b \<sigma> = w} ; idle ; opt ?T ; idle"
      apply (rule data_refine_trans[OF fail_sup])
      unfolding split
      apply (intro data_refine_seq data_refine_refl)
      by (rule data_refine_test) auto
    have partition_rel: "F \<inter> cas_rel b g w = ?S \<union> ?T"
      by (auto simp: cas_rel_def split: if_splits)
    show ?thesis
      using data_refine_sup[OF s_ref t_ref]
      by (simp add: partition_rel opt_union seq.op_sup seq.sup_op)
  qed
  show ?thesis unfolding cas_body_def[of b]
    using data_refine_SUP[of UNIV "\<lambda>_. ?A" J
      "\<lambda>k. idle ; \<tau>{\<sigma>. b \<sigma> = k} ; idle ; opt (F \<inter> cas_rel b g k) ; idle"] step by simp
qed

subsection \<open>Expression and bind normal forms\<close>

lemma arr_at_eval:
  "\<lblot>*(arr_at_lve (Constant (NatValue j)))\<rblot>k =
    idle ; \<tau>{\<sigma>. arr_at j \<sigma> = k} ; idle"
proof -
  have lv: "\<ltort>arr_at_lve (Constant (NatValue j))\<rtort>l =
      (if l = arr_at_lval j then idle else \<bottom>)" for l
    by (cases l) (auto simp: simp_vars idle_par_idle nonaborting_par_magic
        idle_nonaborting par.commute split: if_splits)
  have inner: "(if l = arr_at_lval j then idle else \<bottom>) ; \<tau>{\<sigma>. get l \<sigma> = k} ; idle =
      (if l = arr_at_lval j then idle ; \<tau>{\<sigma>. get l \<sigma> = k} ; idle else \<bottom>)" for l
    by (simp add: seq.bot_annihilates_left)
  have "\<lblot>*(arr_at_lve (Constant (NatValue j)))\<rblot>k =
      (\<Squnion>l. if l = arr_at_lval j then idle ; \<tau>{\<sigma>. get l \<sigma> = k} ; idle else \<bottom>)"
    by (simp only: expr_cmd.simps(2) lv inner)
  also have "\<dots> = idle ; \<tau>{\<sigma>. get (arr_at_lval j) \<sigma> = k} ; idle"
    by (rule antisym) (auto simp: SUP_le_iff intro: SUP_upper2)
  finally show ?thesis by (simp add: simp_vars)
qed

lemma s_eval:
  "\<lblot>*s_lve\<rblot>k = idle ; \<tau>{\<sigma>. s \<sigma> = k} ; idle"
  unfolding s_lve_def s_def s_lval_def by (rule var_deref_eval_alternate)

lemma bind_constant:
  "bind (Constant k) in c = idle ; c k"
  unfolding bind_command_def
  by (rule antisym) (auto simp: SUP_le_iff seq.bot_annihilates_left intro: SUP_upper2)

lemma bind_cas_body:
  assumes eval: "\<And>k. \<lblot>e\<rblot>k = idle ; \<tau>{\<sigma>. v \<sigma> = k} ; idle"
  shows "bind e in (\<lambda>old. bind (Constant (f old)) in (\<lambda>new.
      vars:\<^sub>s\<langle>UNIV, {(\<sigma>,\<sigma>').
        (v \<sigma> = old \<longrightarrow> v \<sigma>' = new) \<and>
        (v \<sigma> \<noteq> old \<longrightarrow> v \<sigma>' = v \<sigma>)}\<rangle>)) =
      cas_body v f (id_bar vars)"
proof -
  have idle_twice: "idle ; (idle ; c) = idle ; c" for c
    by (simp only: seq.seq_assoc[symmetric] idle_seq_idle)
  show ?thesis
    unfolding bind_constant
    unfolding bind_command_def
    unfolding atomic_frame
    unfolding atomic_spec_def cas_body_def
    by (simp add: eval cas_rel_def seq.assert_neut seq.seq_assoc idle_twice if_split)
qed

lemma binary_read_constant_choice:
  assumes eval: "\<And>x. \<lblot>e\<rblot>x = idle ; \<tau>{\<sigma>. v \<sigma> = x} ; idle"
  shows "\<lblot>Binary f e (Constant c)\<rblot>k = (\<Squnion>x\<in>{x. f x c = k}. \<lblot>e\<rblot>x)"
proof -
  have magic: "\<lblot>e\<rblot>x \<parallel> \<bottom> = \<bottom>" for x
    by (subst par.commute, rule nonaborting_par_magic)
       (rule order_trans[OF idle_eval(1) idle_nonaborting])
  have one: "\<lblot>e\<rblot>x \<parallel> \<lblot>Constant c\<rblot>y =
      (if y = c then \<lblot>e\<rblot>x else \<bottom>)" for x y
    by (cases "y = c"; simp only: expr_cmd.simps if_True if_False magic)
       (simp add: eval par.commute idle_test_idle)
  show ?thesis
    unfolding expr_cmd.simps(4) one
  proof (rule antisym)
    show "\<Squnion>{if y = c then \<lblot>e\<rblot>x else \<bottom> |x y. f x y = k}
        \<le> (\<Squnion>x\<in>{x. f x c = k}. \<lblot>e\<rblot>x)"
    proof (rule Sup_least)
      fix z
      assume "z \<in> {if y = c then \<lblot>e\<rblot>x else \<bottom> |x y. f x y = k}"
      then obtain x y where z: "z = (if y = c then \<lblot>e\<rblot>x else \<bottom>)" "f x y = k" by blast
      show "z \<le> (\<Squnion>x\<in>{x. f x c = k}. \<lblot>e\<rblot>x)"
      proof (cases "y = c")
        case True
        then have member: "x \<in> {x. f x c = k}" using z(2) by simp
        have "\<lblot>e\<rblot>x \<le> (\<Squnion>x\<in>{x. f x c = k}. \<lblot>e\<rblot>x)"
          by (rule SUP_upper[OF member])
        then show ?thesis using z(1) True by simp
      next
        case False
        then show ?thesis using z(1) by simp
      qed
    qed
    show "(\<Squnion>x\<in>{x. f x c = k}. \<lblot>e\<rblot>x)
        \<le> \<Squnion>{if y = c then \<lblot>e\<rblot>x else \<bottom> |x y. f x y = k}"
    proof (rule SUP_least)
      fix x
      assume x: "x \<in> {x. f x c = k}"
      have "\<lblot>e\<rblot>x \<in> {if y = c then \<lblot>e\<rblot>x else \<bottom> |x y. f x y = k}"
        using x by (intro CollectI exI[of _ x] exI[of _ c]) simp
      then show "\<lblot>e\<rblot>x \<le> \<Squnion>{if y = c then \<lblot>e\<rblot>x else \<bottom> |x y. f x y = k}"
        by (rule Sup_upper)
    qed
  qed
qed

lemma binary_read_constant:
  assumes eval: "\<And>x. \<lblot>e\<rblot>x = idle ; \<tau>{\<sigma>. v \<sigma> = x} ; idle"
      and nonempty: "{x. f x c = k} \<noteq> {}"
  shows "\<lblot>Binary f e (Constant c)\<rblot>k =
      idle ; \<tau>{\<sigma>. f (v \<sigma>) c = k} ; idle"
proof -
  have partition: "(\<Union>x\<in>{x. f x c = k}. {\<sigma>. v \<sigma> = x}) = {\<sigma>. f (v \<sigma>) c = k}"
    by auto
  have "\<lblot>Binary f e (Constant c)\<rblot>k = (\<Squnion>x\<in>{x. f x c = k}. \<lblot>e\<rblot>x)"
    by (rule binary_read_constant_choice[OF eval])
  also have "\<dots> = idle ; \<tau>(\<Union>x\<in>{x. f x c = k}. {\<sigma>. v \<sigma> = x}) ; idle"
    by (simp add: eval seq.test.hom_Sup image_image seq.op_SUP_nonempty[OF nonempty] seq.SUP_op)
  also have "\<dots> = idle ; \<tau>{\<sigma>. f (v \<sigma>) c = k} ; idle"
    by (simp only: partition)
  finally show ?thesis .
qed

lemma binary_read_data_refine:
  assumes eval_a: "\<And>x. \<lblot>e\<rblot>x = idle ; \<tau>{\<sigma>. a \<sigma> = x} ; idle"
      and eval_b: "\<And>x. \<lblot>e'\<rblot>x = idle ; \<tau>{\<sigma>. b \<sigma> = x} ; idle"
      and results: "\<And>x. \<exists>y. f y c = g x d"
      and agree: "\<And>\<sigma>. \<sigma> \<in> J \<Longrightarrow> f (a \<sigma>) c = g (b \<sigma>) d"
  shows "\<lblot>Binary f e (Constant c)\<rblot>k \<ge>\<^sub>J \<lblot>Binary g e' (Constant d)\<rblot>k"
proof (cases "{x. g x d = k} = {}")
  case True
  show ?thesis unfolding binary_read_constant_choice[OF eval_b] True
    by (rule refsto_implies_data_refine) simp
next
  case False
  then have nonempty_a: "{x. f x c = k} \<noteq> {}" using results by blast
  show ?thesis
    unfolding binary_read_constant[where f=f and c=c and k=k, OF eval_a nonempty_a]
      binary_read_constant[where f=g and c=d and k=k, OF eval_b False]
    apply (intro data_refine_seq data_refine_refl)
    by (rule data_refine_test) (use agree in auto)
qed

subsection \<open>Data refinement\<close>

lemma refine_remove_from_set_to_word_array:
  assumes index: "i div 64 < N"
  shows
  "while Binary set_member (*s_lve) (Constant (NatValue i)) do
     bind (*s_lve) in (\<lambda>olds.
       bind (Constant (set_difference olds (NatSetValue {i}))) in (\<lambda>news.
         {|s_lval,arr_at_lval (i div 64)|}:\<^sub>s\<langle>\<top>,\<llangle>(\<ordmasculine>s = olds \<longrightarrow> \<ordfeminine>s = news) \<and> (\<ordmasculine>s \<noteq> olds \<longrightarrow> \<ordfeminine>s = \<ordmasculine>s)\<rrangle>\<rangle>))
   od \<ge>\<^sub>I
   while Binary word_bit (*(arr_at_lve (Constant (NatValue (i div 64))))) (Constant (NatValue (i mod 64))) do
     bind (*(arr_at_lve (Constant (NatValue (i div 64))))) in (\<lambda>oldw.
       bind (Constant (word_unset_bit oldw (NatValue (i mod 64)))) in (\<lambda>neww.
         {|s_lval,arr_at_lval (i div 64)|}:\<^sub>s\<langle>\<top>,\<llangle>(\<ordmasculine>(arr_at (i div 64)) = oldw \<longrightarrow> \<ordfeminine>(arr_at (i div 64)) = neww) \<and> (\<ordmasculine>(arr_at (i div 64)) \<noteq> oldw \<longrightarrow> \<ordfeminine>(arr_at (i div 64)) = \<ordmasculine>(arr_at (i div 64)))\<rrangle>\<rangle>))
    od"
proof (rule data_refine_while_alt)
  show "\<And>k. \<lblot>Binary set_member (*s_lve) (Constant (NatValue i))\<rblot>k \<ge>\<^sub>I
    \<lblot>Binary word_bit (*(arr_at_lve (Constant (NatValue (i div 64))))) (Constant (NatValue (i mod 64)))\<rblot>k"
  proof (rule binary_read_data_refine[OF s_eval arr_at_eval])
    show "\<And>x. \<exists>y. set_member y (NatValue i) = word_bit x (NatValue (i mod 64))"
    proof -
      fix x
      show "\<exists>y. set_member y (NatValue i) = word_bit x (NatValue (i mod 64))"
      proof (cases x)
        case (Word64Value W)
        then show ?thesis
          by (intro exI[of _ "NatSetValue (if bit W (i mod 64) then {i} else {})"]) simp
      qed (auto intro!: exI[of _ UndefValue])
    qed
    show "\<And>\<sigma>. \<sigma> \<in> I \<Longrightarrow> set_member (s \<sigma>) (NatValue i) =
      word_bit (arr_at (i div 64) \<sigma>) (NatValue (i mod 64))"
      using I_member index by blast
  qed
  show "bind (*s_lve) in (\<lambda>olds.
       bind (Constant (set_difference olds (NatSetValue {i}))) in (\<lambda>news.
         {|s_lval,arr_at_lval (i div 64)|}:\<^sub>s\<langle>\<top>,\<llangle>(\<ordmasculine>s = olds \<longrightarrow> \<ordfeminine>s = news) \<and> (\<ordmasculine>s \<noteq> olds \<longrightarrow> \<ordfeminine>s = \<ordmasculine>s)\<rrangle>\<rangle>))
    \<ge>\<^sub>I
    bind (*(arr_at_lve (Constant (NatValue (i div 64))))) in (\<lambda>oldw.
       bind (Constant (word_unset_bit oldw (NatValue (i mod 64)))) in (\<lambda>neww.
         {|s_lval,arr_at_lval (i div 64)|}:\<^sub>s\<langle>\<top>,\<llangle>(\<ordmasculine>(arr_at (i div 64)) = oldw \<longrightarrow> \<ordfeminine>(arr_at (i div 64)) = neww) \<and> (\<ordmasculine>(arr_at (i div 64)) \<noteq> oldw \<longrightarrow> \<ordfeminine>(arr_at (i div 64)) = \<ordmasculine>(arr_at (i div 64)))\<rrangle>\<rangle>))"
    unfolding bind_cas_body[OF s_eval, unfolded split_def]
      bind_cas_body[OF arr_at_eval, unfolded split_def]
    apply (rule cas_body_data_refine)
    subgoal using I_word_determined index by blast
    subgoal using I_array_update by (auto simp: restrict_domain_def restrict_range_def)
    subgoal using I_array_unchanged by (auto simp: restrict_domain_def restrict_range_def)
    done
qed

end
end
