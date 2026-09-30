section \<open>Example: Remove an element from a set\<close>

theory Remove
  imports Typed_State Commands.Data_Refinement
begin

fun extract_set_from_word :: "64 word \<Rightarrow> nat set"
  where "extract_set_from_word w = {i::nat. bit w i}"

subsection \<open>Lift operations to operate on \<open>typed_values\<close>\<close>
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

context typed_frame_state
begin

subsection \<open>Define variables\<close>
text \<open>syntax to define the state getters \<open>s\<close>, \<open>w\<close> and the corresponding l-values and l-value
expressions \<open>s_lval\<close>, \<open>s_lve\<close>, \<open>w_lval\<close>, and \<open>w_lve\<close>.\<close>
define_var s
define_var w

subsection \<open>Invariant\<close>
text \<open>Coupling invariant: nats in the set correspond to set bits in the word.\<close>
definition I :: "'state set" where
  "I = \<llangle>\<exists>S W.
      \<acute>s = NatSetValue S \<and>
      \<acute>w = Word64Value W \<and>
      S = extract_set_from_word W\<rrangle>"

subsection \<open>Helper lemmas\<close>
lemma I_coupling:
  assumes "\<sigma> \<in> I"
  shows "s \<sigma> = extract_set_from_word_val (w \<sigma>)"
  using assms I_def by auto

lemma I_word_set_bijection:
  assumes "\<sigma> \<in> I"
  shows "s \<sigma> = extract_set_from_word_val k \<longleftrightarrow> w \<sigma> = k"
proof -
  obtain W where "w \<sigma> = Word64Value W"
                 "s \<sigma> = NatSetValue (extract_set_from_word W)"
    using assms by (auto simp: I_def)
  then show ?thesis
    using bit_eqI by (cases k) auto
qed

lemma w_extracted_set_refines_s: "\<lblot>*s_lve\<rblot>(extract_set_from_word_val k) \<ge>\<^sub>I \<lblot>*w_lve\<rblot>k"
  unfolding s_lve_def w_lve_def
  by (rule data_refine_variable) (auto simp: I_def expr_eq_def simp_vars)

lemma set_in_equiv_bit_set: "set_member (extract_set_from_word_val wo) k = word_bit wo k"
  by (cases wo; cases k; simp)

subsection \<open>Data refinement\<close>
lemma refine_remove_from_set:
  "while Binary set_member (*s_lve) (Constant (NatValue i)) do
     bind (*s_lve) in (\<lambda>olds.
       bind (Constant (set_difference olds (NatSetValue {i}))) in (\<lambda>news.
         {|s_lval,w_lval|}:\<^sub>s\<langle>\<top>,\<llangle>(\<ordmasculine>s = olds \<longrightarrow> \<ordfeminine>s = news) \<and> (\<ordmasculine>s \<noteq> olds \<longrightarrow> \<ordfeminine>s = \<ordmasculine>s)\<rrangle>\<rangle>))
   od \<ge>\<^sub>I
   while Binary word_bit (*w_lve) (Constant (NatValue i)) do
     bind (*w_lve) in (\<lambda>oldw.
       bind (Constant (word_unset_bit oldw (NatValue i))) in (\<lambda>neww.
         {|s_lval,w_lval|}:\<^sub>s\<langle>\<top>,\<llangle>(\<ordmasculine>w = oldw \<longrightarrow> \<ordfeminine>w = neww) \<and> (\<ordmasculine>w \<noteq> oldw \<longrightarrow> \<ordfeminine>w = \<ordmasculine>w)\<rrangle>\<rangle>))
    od"
proof (rule data_refine_while_alt)
  let ?set_rel = "\<lambda>olds news. \<llangle>(\<ordmasculine>s = olds \<longrightarrow> \<ordfeminine>s = news) \<and> (\<ordmasculine>s \<noteq> olds \<longrightarrow> \<ordfeminine>s = \<ordmasculine>s)\<rrangle>"
  let ?word_rel = "\<lambda>oldw neww. \<llangle>(\<ordmasculine>w = oldw \<longrightarrow> \<ordfeminine>w = neww) \<and> (\<ordmasculine>w \<noteq> oldw \<longrightarrow> \<ordfeminine>w = \<ordmasculine>w)\<rrangle>"
  let ?set_update_atomic = "\<lambda>olds news. {|s_lval,w_lval|}:\<^sub>s\<langle>\<top>, ?set_rel olds news\<rangle>"
  let ?word_update_atomic = "\<lambda>oldw neww. {|s_lval,w_lval|}:\<^sub>s\<langle>\<top>, ?word_rel oldw neww\<rangle>"

  show "\<And>k. \<lblot>Binary set_member (*s_lve) (Constant (NatValue i))\<rblot>k
         \<ge>\<^sub>I \<lblot>Binary word_bit (*w_lve) (Constant (NatValue i))\<rblot>k"
    by (rule data_refine_binary)
      (metis set_in_equiv_bit_set w_extracted_set_refines_s data_refine_refl)

  show "bind (*s_lve)
        in (\<lambda>olds. bind (Constant (set_difference olds (NatSetValue {i})))
                   in (\<lambda>news. ?set_update_atomic olds news))
     \<ge>\<^sub>I bind (*w_lve)
        in (\<lambda>oldw. bind (Constant (word_unset_bit oldw (NatValue i)))
                   in (\<lambda>neww. ?word_update_atomic oldw neww))"
  proof (rule data_refine_bind)
    fix oldw :: typed_value
    let ?olds = "extract_set_from_word_val oldw"

    show "\<exists>k1. \<lblot>*s_lve\<rblot>k1 ; bind (Constant (set_difference k1 (NatSetValue {i})))
                           in (\<lambda>news. ?set_update_atomic k1 news) 
          \<ge>\<^sub>I \<lblot>*w_lve\<rblot>oldw ; bind (Constant (word_unset_bit oldw (NatValue i)))
                           in (\<lambda>neww. ?word_update_atomic oldw neww)"
      apply (rule exI[where x = "?olds"])
      apply (rule data_refine_seq)
      subgoal text \<open>left refines\<close>
        using w_extracted_set_refines_s by auto
      subgoal text \<open>right refines\<close>
        proof (rule data_refine_bind)
        fix neww :: typed_value
        let ?news = "extract_set_from_word_val neww"

        show "\<exists>k1. \<lblot>Constant (set_difference (extract_set_from_word_val oldw) (NatSetValue {i}))\<rblot>k1 ;
                   ?set_update_atomic (extract_set_from_word_val oldw) k1
                \<ge>\<^sub>I \<lblot>Constant (word_unset_bit oldw (NatValue i))\<rblot>neww ;
                   ?word_update_atomic oldw neww"
          apply (rule exI[where x = "?news"])
          apply (rule data_refine_seq)
          subgoal text \<open>left refines\<close>
            by (rule data_refine_constant) (cases oldw; auto simp: bit_unset_bit_iff)
          subgoal text \<open>right refines\<close>
            apply (rule data_refine_frame_mono)
            apply (rule data_refine_atomic_spec)
            subgoal by simp
            subgoal unfolding restrict_domain_def restrict_range_def
                    using I_coupling I_word_set_bijection by auto
            done
          done
        qed
      done
    qed
  qed
end
end