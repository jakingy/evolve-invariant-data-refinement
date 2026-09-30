section \<open>Assignment commands\<close>

theory GhostAssignments
  imports Assignments
begin

context frame_state
begin

section \<open>Ghost update\<close>
text\<open>Allows an assignment to be performed on the concrete state, while also allowing an atomic
operation to be performed on the abstract state at the same time in order to maintain an invariant.

This enables removing a coupling invariant from the RHS. Provided the updated LValue is not in
the set of abstract LValues, we see the precise abstract operation that corresponds to the concrete
assignment.

Example:

\<open>  inv I
 \<iinter> rely enqueue_rely_dequeue_guar
 \<iinter> guar\<^sub>\<pi> enqueue_guar_dequeue_rely
 \<iinter> enqueue_lvals:\<^sub>s\<langle>\<llangle>q_has_space \<acute>q\<rrangle>, \<llangle>\<ordfeminine>q = enqueue_lift \<ordmasculine>q (NatValue a)\<rrangle>, enqueue_lvals_term\<rangle>
 \<ge> (buffer_at (*w_lve)) := Constant (NatValue a) ;
    w_lve := Unary circ_buf_pointer_increment (*w_lve) ghost[G] \<llangle>\<ordfeminine>q = enqueue_lift \<ordmasculine>q (NatValue a)\<rrangle>\<close>

A non UNIV g is probably not useful for our data refinement strategy though, since we require
independence from the abstract state (cannot constrain the abstract state at all) and we also
keep the invariant on both sides.

What is more useful is the special case where we let g be UNIV. All LValues in G are unconstrained.
This is necessary to use assignments while maintaining independence from the abstract state.
This is equivalent to Morgan Carrol's open assignment operation which looks something like:

w,x,y,z := 1,?,2,? which assigns 1 to w, 2 to y, and leaves x, z unconstrained.

Our command takes in an fset of all abstract variables at once for ease of use
and reasoning about the independence from the abstract state. We also limit to updates of one
concrete LValue at a time for simplicity.\<close>
definition ghost_update :: "'v LValue \<Rightarrow> 'v \<Rightarrow> ('v LValue) fset \<Rightarrow> 'state rel \<Rightarrow> 'state rel" where
"ghost_update lv k G g \<equiv> (id_bar G \<inter> g) O (update lv k)"

text\<open>There must exist some state between \<sigma> and \<sigma>', s, such that \<sigma>' = set lv k s.
and \<sigma> s in (id_bar G \<inter> g). Furthermore, all variables that are not lv remain
unchanged between s and \<sigma>'.\<close>
lemma ghost_update_intermediate_step:
  assumes step: "(\<sigma>, \<sigma>') \<in> ghost_update lv k G g"
  obtains s where "(\<sigma>, s) \<in> id_bar G \<inter> g"
    and "\<sigma>' = set lv k s"
    and "\<And>v. v \<noteq> lv \<longrightarrow> get v \<sigma>' = get v s"
  using step by (auto simp: ghost_update_def update_def relcomp_unfold get_set_neq)

text\<open>The value of lv after a ghost update is k.\<close>
lemma ghost_update_eq:
  assumes step: "(\<sigma>, \<sigma>') \<in> ghost_update lv k G g"
  shows "get lv \<sigma>' = k"
proof -
  obtain s where "(\<sigma>, s) \<in> id_bar G \<inter> g" and "\<sigma>' = set lv k s"
    using ghost_update_intermediate_step[OF step] by auto
  then show ?thesis
    by (simp add: get_set_eq)
qed

text\<open>If v not in G and it not equal to lv, v is unchanged.\<close>
lemma ghost_update_unchanged_lval:
  assumes step: "(\<sigma>, \<sigma>') \<in> ghost_update lv k G g"
  assumes v_notin_G: "v |\<notin>| G"
  assumes v_ne_lv: "v \<noteq> lv"
  shows "get v \<sigma>' = get v \<sigma>"
proof -
  obtain s where ghost_step: "(\<sigma>, s) \<in> id_bar G \<inter> g"
    and post: "\<sigma>' = set lv k s"
    using ghost_update_intermediate_step[OF step] by auto
  have ghost_unchanged: "get v s = get v \<sigma>"
    using ghost_step v_notin_G
    by (auto simp: id_bar_def id_bar_pred_def)
  show ?thesis
    using post ghost_unchanged v_ne_lv
    by (simp add: get_set_neq)
qed

definition ghost_assign ::
  "(('state, 'v) LValueExpr) \<Rightarrow> ('state, 'v) Expr \<Rightarrow>
   ('v LValue) fset \<Rightarrow> 'state rel \<Rightarrow> 'a"
  ("(_ := _ ghost[_] _)" [93, 92, 0, 0] 91)
where
  "lve := e ghost[G] g \<equiv> \<Squnion>lv k. (\<ltort>lve\<rtort>lv \<parallel> \<lblot>e\<rblot>k) ; opt (ghost_update lv k G g) ; idle"

section \<open>Open update\<close>

text\<open>An open update is the useful special case of a ghost update: the l-values in
\<open>G\<close> are unconstrained, while \<open>lv\<close> is assigned \<open>k\<close>. All other l-values are preserved.\<close>
definition open_update ::
  "'v LValue \<Rightarrow> 'v \<Rightarrow> ('v LValue) fset \<Rightarrow> 'state rel"
where
  "open_update lv k G \<equiv> ghost_update lv k G UNIV"


end
end
