section \<open>Open assignment commands\<close>

theory Open_Assignments
  imports Assignments
begin

context frame_state
begin

section \<open>Open update\<close>
text\<open>An open update is the useful special case of a ghost update: the l-values in
\<open>G\<close> are unconstrained, while \<open>lv\<close> is assigned \<open>k\<close>. All other l-values are preserved.\<close>
definition open_update ::
  "'v LValue \<Rightarrow> 'v \<Rightarrow> ('v LValue) fset \<Rightarrow> 'state rel"
where
  "open_update lv k G \<equiv> id_bar (finsert lv G) \<inter> {(\<sigma>, \<sigma>'). get lv \<sigma>' = k}"

text \<open>All l-values outside of finsert lv G are preserved.\<close>
lemma open_update_nochange: "open_update lv k G \<subseteq> id_bar (finsert lv G)" 
  unfolding open_update_def by simp

lemma lval_not_lv_or_abstract_implies_open_update_id:
  assumes "lv1 |\<notin>| finsert lv G"
  assumes "s \<in> open_update lv k G"
  shows "get lv1 (fst s) = get lv1 (snd s)"
  using id_bar_def id_bar_pred_def open_update_nochange assms
  by (simp add: subset_iff)

lemma open_update_unchanged_lvals:
  assumes "(\<sigma>,\<sigma>') \<in> open_update lv k G"
  shows "\<And>lv'. lv' |\<notin>| finsert lv G \<longrightarrow> get lv' \<sigma>' = get lv' \<sigma>"
  using assms lval_not_lv_or_abstract_implies_open_update_id by auto

lemma open_update_in_frame:
  assumes "finsert lv G |\<subseteq>| vars"
  shows "open_update lv k G \<subseteq> id_bar vars"
  by (meson assms dual_order.trans id_bar_narrow open_update_nochange)

text \<open>Updating \<open>lv\<close> to \<open>k\<close> ensures \<open>lv = k\<close> afterwards.\<close>
lemma open_update_eq: "open_update lv k G \<subseteq> {(\<sigma>,\<sigma>'). get lv \<sigma>' = k}" 
  using get_set_eq open_update_def by fastforce

lemma open_update_lv_eq: 
  assumes "(\<sigma>,\<sigma>') \<in> open_update lv k G"
  shows "get lv \<sigma>' = k"
  using open_update_eq assms by auto

lemma open_update_case_no_abstract_change:
  assumes "(\<sigma>,\<sigma>') \<in> open_update lv k G"
  assumes "\<And>glv. glv |\<in>| G \<longrightarrow> get glv \<sigma> = get glv \<sigma>'"
  shows "(\<sigma>,\<sigma>') \<in> id_bar {|lv|}"
  unfolding id_bar_def id_bar_pred_def
  using assms open_update_unchanged_lvals by fastforce

section \<open>Open assignment\<close>
text\<open>Allows an assignment to be performed on the concrete state, while also allowing unconstrained
behaviour on the abstract state, thus maintaining the independence from the abstract state
necessary for the data reification theorem.

Example:
\<open>  rely enqueue_rely_dequeue_guar
 \<iinter> guar\<^sub>\<pi> enqueue_guar_dequeue_rely
 \<iinter> enqueue_lvals:\<^sub>s\<langle>\<llangle>q_has_space \<acute>q\<rrangle>, \<llangle>\<ordfeminine>q = enqueue_lift \<ordmasculine>q (NatValue a)\<rrangle>, enqueue_lvals_term\<rangle>
 \<ge>\<^sub>I (buffer_at (*w_lve)) := Constant (NatValue a) ;
    w_lve := Unary circ_buf_pointer_increment (*w_lve) open[{|q|}]\<close>

This is equivalent to Morgan Carrol's open assignment operation which looks something like:

w,x,y,z := 1,?,2,? which assigns 1 to w, 2 to y, and leaves x, z unconstrained.

Our command takes in an fset of all abstract variables at once for ease of use
and reasoning about the independence from the abstract state. We also limit to updates of one
concrete LValue at a time for simplicity.\<close>

definition open_assign ::
  "(('state, 'v) LValueExpr) \<Rightarrow> ('state, 'v) Expr \<Rightarrow>
   ('v LValue) fset \<Rightarrow> 'a"
  ("(_ := _ open[_])" [93, 92, 0] 91)
where
  "lve := e open[G] \<equiv> \<Squnion>lv k. (\<ltort>lve\<rtort>lv \<parallel> \<lblot>e\<rblot>k) ; opt (open_update lv k G) ; idle"

end
end
