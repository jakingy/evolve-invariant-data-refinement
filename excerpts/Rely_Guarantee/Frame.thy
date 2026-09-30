(* Extracts from isabelle/new_rg_algebra/Rely_Guarantee/Frame.thy. *)
(* These are source excerpts, not a standalone buildable theory. *)

(* Original lines 37-39. *)
text \<open>Updating one l-value preserves every other l-value.\<close>
lemma update_nochange: "update lv k \<subseteq> id_bar {|lv|}"
  by (auto simp: update_def id_bar_def id_bar_pred_def get_set_neq)


(* Original lines 41-53. *)
lemma lval_ne_implies_update_id:
  assumes "lv1 \<noteq> lv2"
  assumes "s \<in> update lv2 k"
  shows "get lv1 (fst s) = get lv1 (snd s)"
proof-
  have in_id_bar: "s \<in> id_bar {|lv2|}"
    using assms(2) update_nochange by auto

  have "lv1 |\<notin>| {|lv2|}"
    using assms(1) by simp
  then show ?thesis 
    using id_bar_def id_bar_pred_def in_id_bar by auto
qed


(* Original lines 55-63. *)
lemma update_unchanged_lvals:
  assumes "(\<sigma>,\<sigma>') \<in> update lv k"
  shows "\<And>lv'. lv' \<noteq> lv \<longrightarrow> get lv' \<sigma>' = get lv' \<sigma>"
proof (intro allI impI)
  fix lv'
  assume "lv' \<noteq> lv"
  then show "get lv' \<sigma>' = get lv' \<sigma>"
    using assms lval_ne_implies_update_id by auto
qed


(* Original lines 66-104. *)
lemma update_in_frame:
  assumes "lv |\<in>| vars"
  shows "update lv k \<subseteq> id_bar vars"
proof -
  have singleton_subset: "{|lv|} |\<subseteq>| vars"
    using assms by auto
  have "id_bar {|lv|} \<subseteq> id_bar vars"
    by (rule id_bar_narrow[OF singleton_subset])
  then show ?thesis
    using update_nochange by blast
qed

(*
definition update_pred :: "('state \<Rightarrow> 'v) \<Rightarrow> 'v \<Rightarrow> ('state \<times>'state \<Rightarrow> bool)" where
  "update_pred v k \<equiv> \<guillemotleft>\<acute>(id_bar_pred{|v|}) \<and> \<guillemotleft>\<acute>(var_eq_pred v k)\<guillemotright>\<acute>snd\<guillemotright>"

definition update :: "('state \<Rightarrow> 'v) \<Rightarrow> 'v \<Rightarrow> 'state rel" where
  "update v k \<equiv> \<llangle>\<acute>(update_pred v k)\<rrangle>"

text \<open>Updating a variable \<open>lv\<close> does not change any other variables.\<close>
lemma update_nochange: "update lv k \<subseteq> id_bar{|lv|}" 
proof -
  have "\<And>lv1 \<sigma>. lv1 \<noteq> lv \<Longrightarrow> get lv1 (set lv k \<sigma>) = get lv1 \<sigma>" 
    using get_set_neq by blast 
  have "update lv k \<subseteq> {(\<sigma>,\<sigma>'). \<forall>lv1. lv1 \<noteq> lv \<longrightarrow> get lv1 \<sigma>' = get lv1 (set lv k \<sigma>)}" 
    using update_def by auto
  also have "\<dots> = {(\<sigma>,\<sigma>'). \<forall>lv1. lv1 \<noteq> lv \<longrightarrow> get lv1 \<sigma>' = get lv1 \<sigma>}" 
    using get_set_neq by presburger 
  also have "\<dots> = {(\<sigma>,\<sigma>'). \<forall>lv1. lv1 |\<notin>| {|lv|} \<longrightarrow> get lv1 \<sigma>' = get lv1 \<sigma>}" 
    by blast 
  also have "\<dots> = id_bar{|lv|}" 
    using id_bar_def by auto 
  finally show ?thesis .
qed

lemma update_eq: "update x k \<subseteq> \<llangle>\<ordfeminine>x = k\<rrangle>" 
  using update_def update_pred_def
  by (metis (mono_tags, lifting) mem_Collect_eq subsetI var_eq_pred_def)
*)
