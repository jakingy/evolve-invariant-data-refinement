(* Extracts from isabelle/new_rg_algebra/Rely_Guarantee/State_Relations.thy. *)
(* These are source excerpts, not a standalone buildable theory. *)

(* Original lines 68-95. *)
text \<open>To support expressions the concurrent refinement algebra is extended with
functions \<open>get\<close> and \<open>set\<close> to access and update the state.
These are given the standard lens axioms.\<close>
locale frame_state = constrained_aczel_cra "(;)" nil "(\<parallel>)" skip "(\<iinter>)" chaos \<tau> aczel_atom 
    exists exists_first exists_last +
  cylindric_combined exists exists_first exists_last 
    exists_bool exists_bool_first exists_bool_last exists_sets
  for seq :: "'a::complete_distrib_lattice \<Rightarrow> 'a \<Rightarrow> 'a"  (infixl \<open>;\<close> 77)
  and nil :: "'a"
  and par :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixl \<open>\<parallel>\<close> 70)
  and skip :: "'a"
  and conj :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixl \<open>\<iinter>\<close> 75)
  and chaos :: "'a"
  and test :: "'state set \<Rightarrow> 'a"  (\<open>\<tau>\<close>)
  and aczel_atom :: "('state rel \<times> 'state rel) \<Rightarrow> 'a"
  and exists :: "('v::has_values LValue) \<Rightarrow> 'a \<Rightarrow> 'a"  (\<open>\<exists>\<^sup>C_. _\<close> [999, 999] 999)
  and exists_first :: "('v LValue) \<Rightarrow> 'a \<Rightarrow> 'a"  (\<open>F\<^sup>C_. _\<close> [999, 999] 999)
  and exists_last :: "('v LValue) \<Rightarrow> 'a \<Rightarrow> 'a"  (\<open>L\<^sup>C_. _\<close> [999, 999] 999) 
  and exists_bool :: "('v LValue) \<Rightarrow> 'state rel \<Rightarrow> 'state rel"  (\<open>\<exists>\<^sup>B_. _\<close> [999, 999] 999)
  and exists_bool_first :: "('v LValue) \<Rightarrow> 'state rel \<Rightarrow> 'state rel"  (\<open>F\<^sup>B_. _\<close> [999, 999] 999)
  and exists_bool_last :: "('v LValue) \<Rightarrow> 'state rel \<Rightarrow> 'state rel"  (\<open>L\<^sup>B_. _\<close> [999, 999] 999)
  and exists_sets :: "('v LValue) \<Rightarrow> 'state set \<Rightarrow> 'state set" ("\<exists>\<^sup>S_. _" [999, 999] 999)
  and get :: "('v LValue) \<Rightarrow> 'state \<Rightarrow> 'v::has_values"
  and set :: "('v LValue) \<Rightarrow> 'v \<Rightarrow> 'state \<Rightarrow> 'state" +
  assumes get_set_eq: "get lv (set lv k \<sigma>) = k" 
  assumes set_set_eq: "set lv k2 (set lv k1 \<sigma>) = set lv k2 \<sigma>" 
  assumes set_set_neq: "lv1 \<noteq> lv2 \<Longrightarrow> set lv1 k1 (set lv2 k2 \<sigma>) = set lv2 k2 (set lv1 k1 \<sigma>)" 
  assumes set_get_eq: "set lv (get lv \<sigma>) \<sigma> = \<sigma>" 


(* Original lines 108-109. *)
definition id_bar_pred :: "('v LValue) fset \<Rightarrow> ('state \<times> 'state \<Rightarrow> bool)" where
"id_bar_pred vs = \<guillemotleft>\<forall>x :: ('v LValue). x|\<notin>|vs \<longrightarrow> (get x) \<acute>fst = (get x) \<acute>snd\<guillemotright>"


(* Original lines 111-118. *)
definition id_bar :: "('v LValue) fset \<Rightarrow> 'state rel" where
"id_bar vs \<equiv> {s. id_bar_pred vs s}"

(*definition id_bar_pred :: "('state \<Rightarrow> 'b) fset \<Rightarrow> ('state \<times> 'state \<Rightarrow> bool)"
  where "id_bar_pred vs \<equiv> \<guillemotleft>\<forall>x :: ('state \<Rightarrow> 'b). x|\<notin>|vs \<longrightarrow> x \<acute>fst = x \<acute>snd\<guillemotright>"

definition id_bar :: "('state \<Rightarrow> 'b) fset \<Rightarrow> 'state rel"
where "id_bar vs \<equiv> \<llangle>\<acute>(id_bar_pred vs)\<rrangle>" (*\<llangle>\<forall>x. x|\<notin>|xs \<longrightarrow> \<ordmasculine>x = \<ordfeminine>x\<rrangle>*)*)


(* Original lines 176-198. *)
lemma id_bar_narrow:
  assumes "X |\<subseteq>| Y"
  shows "id_bar X \<subseteq> id_bar Y"
proof 
  fix s
  assume not_X: "s \<in> id_bar X"
  have a: "s \<in> {(\<sigma>,\<sigma>'). (\<forall>x :: 'v LValue. x |\<notin>| X \<longrightarrow> get x \<sigma> = get x \<sigma>')}" 
    using assms id_bar_def id_bar_pred_def not_X by auto  
  have b: "\<dots> \<subseteq> {(\<sigma>,\<sigma>'). (\<forall>x :: 'v LValue. x |\<notin>| Y \<longrightarrow> get x \<sigma> = get x \<sigma>')}" 
    using assms by auto
  have  c: "\<dots> = id_bar Y" using id_bar_def 
    using id_bar_def id_bar_pred_def by force
  show "s \<in> id_bar Y" 
    using a b c by auto
qed

(*proof -
  have a: "id_bar X = {(\<sigma>,\<sigma>'). \<forall>x::'varname. x |\<notin>| X \<longrightarrow> get_var x \<sigma> = get_var x \<sigma>'}"
    using id_bar_def by presburger
  have b: "\<dots> \<subseteq> {(\<sigma>,\<sigma>'). \<forall>x::'varname. x |\<notin>| Y \<longrightarrow> get_var x \<sigma> = get_var x \<sigma>'}" 
    using assms by auto
  show ?thesis using a b id_bar_def by presburger
qed*)


(* Original lines 200-201. *)
lemma id_bar_ge_Id: "id_bar vars \<ge> Id"
  by (auto simp: id_bar_def id_bar_pred_def)


(* Original lines 203-206. *)
text \<open>Add a frame of $vars$ to a command $c$.\<close>
(*definition var_frame_set :: "('v LValue) fset \<Rightarrow> 'a \<Rightarrow> 'a" (infix ":\<^sub>s" 95)*)
definition var_frame_set :: "('v LValue) fset \<Rightarrow> 'a \<Rightarrow> 'a" (infix ":\<^sub>s" 95)
  where "var_frame_set vars c \<equiv> guar\<^sub>\<pi> (id_bar vars) \<iinter> c"


(* Original lines 208-210. *)
lemma idbar_int: "(id_bar X) \<inter> (id_bar Y) = id_bar (X |\<inter>| Y)"
  unfolding id_bar_def id_bar_pred_def
  by auto


(* Original lines 212-220. *)
lemma var_frame_set_merge: "X:\<^sub>s(Y:\<^sub>sc) = (X |\<inter>| Y):\<^sub>sc"
proof -
  have guar_merge:
    "guar\<^sub>\<pi> (id_bar X) \<iinter> guar\<^sub>\<pi> (id_bar Y) =
      guar\<^sub>\<pi> (id_bar (X |\<inter>| Y))"
    by (simp add: pgm_guar_conj_pgm_guar idbar_int)
  show ?thesis
    using guar_merge by (metis seq_conj.sync_assoc var_frame_set_def)
qed


(* Original lines 222-223. *)
lemma var_frame_set_swap: "X:\<^sub>s(Y:\<^sub>sc) = Y:\<^sub>s(X:\<^sub>sc)"
  by (simp add: var_frame_set_merge finter_commute)


(* Original lines 225-228. *)
lemma var_frame_set_subset_merge:
  assumes "Y |\<subseteq>| X"
  shows "X:\<^sub>s(Y:\<^sub>sc) = Y:\<^sub>sc"
  by (simp add: assms finter_absorb1 var_frame_set_merge)


(* Original lines 230-233. *)
lemma var_frame_set_seq:
  "X:\<^sub>s(c ; d) = (X:\<^sub>sc) ; (X:\<^sub>sd)"
  unfolding var_frame_set_def
  by (rule pgm_guar_conj_seq)


(* Original lines 235-237. *)
lemma var_frame_set_assert:
  "vars:\<^sub>s\<lbrace>p\<rbrace> = \<lbrace>p\<rbrace>"
  by (metis local.conj.commute pgm_guar_conj_assert var_frame_set_def)


(* Original lines 239-247. *)
lemma var_frame_set_extract_assert_left:
  "vars:\<^sub>s(\<lbrace>p\<rbrace> ; c) = \<lbrace>p\<rbrace> ; vars:\<^sub>sc"
proof -
  have "vars:\<^sub>s(\<lbrace>p\<rbrace> ; c) = vars:\<^sub>s\<lbrace>p\<rbrace> ; vars:\<^sub>sc"
    by (rule var_frame_set_seq)
  also have "\<dots> = \<lbrace>p\<rbrace> ; vars:\<^sub>sc"
    by (simp add: var_frame_set_assert)
  finally show ?thesis .
qed


(* Original lines 249-257. *)
lemma var_frame_set_extract_assert_right:
  "vars:\<^sub>s(c ; \<lbrace>p\<rbrace>) = vars:\<^sub>sc ; \<lbrace>p\<rbrace>"
proof -
  have "vars:\<^sub>s(c ; \<lbrace>p\<rbrace>) = vars:\<^sub>sc ; vars:\<^sub>s\<lbrace>p\<rbrace>"
    by (rule var_frame_set_seq)
  also have "\<dots> = vars:\<^sub>sc ; \<lbrace>p\<rbrace>"
    by (simp add: var_frame_set_assert)
  finally show ?thesis .
qed


(* Original lines 259-261. *)
lemma rely_conj_var_frame_set:
  "rely r \<iinter> vars:\<^sub>sc = vars:\<^sub>s(rely r \<iinter> c)"
  by (metis local.conj.commute seq_conj.sync_assoc var_frame_set_def)


(* Original lines 263-266. *)
lemma var_frame_set_par:
  "X:\<^sub>s(c \<parallel> d) = (X:\<^sub>sc) \<parallel> (X:\<^sub>sd)"
  unfolding var_frame_set_def
  by (rule pgm_guar_distrib_par)


(* Original lines 268-271. *)
lemma var_frame_set_Sup:
  "X:\<^sub>s(\<Squnion>j\<in>J. c j) = (\<Squnion>j\<in>J. X:\<^sub>s(c j))"
  unfolding var_frame_set_def
  by (rule pgm_guar_conj_Sup)


(* Original lines 273-276. *)
lemma var_frame_set_finite_iter:
  "X:\<^sub>s(c*) = (X:\<^sub>sc)*"
  unfolding var_frame_set_def
  by (rule pgm_guar_conj_finite_iter)


(* Original lines 278-281. *)
lemma var_frame_set_iter:
  "X:\<^sub>s(c\<^sup>\<omega>) = (X:\<^sub>sc)\<^sup>\<omega>"
  unfolding var_frame_set_def
  by (rule pgm_guar_conj_iter)


(* Original lines 283-286. *)
text \<open>Add a frame of a single variable $x$ to a command $c$.\<close>
(*definition var_frame :: "'varname \<Rightarrow> 'a \<Rightarrow> 'a" (infix ":\<^sub>f" 95)*)
definition var_frame :: "'v LValue \<Rightarrow> 'a \<Rightarrow> 'a" (infix ":\<^sub>f" 95)
  where "var_frame x c \<equiv> {|x|}:\<^sub>sc"


(* Original lines 294-295. *)
definition var_eq_pred :: "'v LValue \<Rightarrow> 'v \<Rightarrow> ('state \<Rightarrow> bool)" 
  where "var_eq_pred var value \<equiv> \<guillemotleft>\<acute>(get var) = value\<guillemotright>"


(* Original lines 297-302. *)
text \<open>Set of states in which variable $var$ equals $value$.\<close>
definition var_eq :: "'v LValue \<Rightarrow> 'v \<Rightarrow> 'state set"
  where "var_eq var value \<equiv> \<llangle>\<acute>(var_eq_pred var value)\<rrangle>"

(*definition var_eq :: "'varname => 'v \<Rightarrow> 'state set"
  where "var_eq var value \<equiv> {s. get_var var s = value}" *)


(* Original lines 304-305. *)
definition id_set_pred :: "('v LValue) fset \<Rightarrow> ('state*'state \<Rightarrow> bool)"
  where "id_set_pred vars = \<guillemotleft>\<forall>x::('v LValue). x |\<in>| vars \<longrightarrow> (get x) \<acute>fst = (get x) \<acute>snd\<guillemotright>"


(* Original lines 307-311. *)
definition id_set :: "('v LValue) fset \<Rightarrow> 'state rel"
  where "id_set vars = \<llangle>\<acute>(id_set_pred vars)\<rrangle>"

(*definition id_set :: "'varname fset \<Rightarrow> 'state rel"
  where "id_set vars = {(\<sigma>,\<sigma>'). \<forall>x::'varname. x |\<in>| vars \<longrightarrow> get_var x \<sigma> = get_var x \<sigma>'}"*)


(* Original lines 318-337. *)
lemma id_set_narrow:
  assumes "X |\<subseteq>| Y"
  shows "id_set Y \<subseteq> id_set X"
proof -
  have a: "id_set Y = \<llangle>\<forall>x::('v LValue). x |\<in>| Y \<longrightarrow> (get x) \<acute>fst = (get x) \<acute>snd\<rrangle>"
    using id_set_def id_set_pred_def
    by auto 
  have b: "\<dots> \<subseteq> \<llangle>\<forall>x::('v LValue). x |\<in>| X \<longrightarrow> (get x) \<acute>fst = (get x) \<acute>snd\<rrangle>" 
    using assms by force
  have c: "\<dots> = id_set X" using id_set_def id_set_pred_def
    by simp
  show ?thesis using a b c by auto
qed
(*proof -
  have a: "id_set Y = {(\<sigma>,\<sigma>'). \<forall>x::'varname. x |\<in>| Y \<longrightarrow> get_var x \<sigma> = get_var x \<sigma>'}"
    using id_set_def by presburger
  have b: "\<dots> \<subseteq> {(\<sigma>,\<sigma>'). \<forall>x::'varname. x |\<in>| X \<longrightarrow> get_var x \<sigma> = get_var x \<sigma>'}" 
    using assms by auto
  show ?thesis using a b id_set_def by presburger
qed*)


(* Original lines 339-340. *)
definition id_pred :: "('state \<Rightarrow> 'v) \<Rightarrow> ('state*'state \<Rightarrow> bool)"
  where "id_pred x = \<guillemotleft>\<ordmasculine>x = \<ordfeminine>x\<guillemotright>"


(* Original lines 342-346. *)
definition id :: "('v LValue) \<Rightarrow> 'state rel"
  where "id x = \<llangle>\<acute>(id_pred (get x))\<rrangle>"

(*definition id :: "'varname \<Rightarrow> 'state rel"
  where "id x = {(\<sigma>,\<sigma>'). get_var x \<sigma> = get_var x \<sigma>'}"*)


(* Original lines 348-391. *)
lemma id_consistent : "id(x) = id_set {|x|}"
  using id_set_def local.id_def 
  by (smt (verit) Collect_cong fsingleton_iff id_set_pred_def id_pred_def)

(*
lemma id_univ : "id(x) O id_bar({|x|}) = UNIV"
proof -
  have "id(x) O id_bar({|x|}) = \<llangle>\<ordmasculine>x = \<ordfeminine>x\<rrangle> O 
      \<llangle>\<forall>x'::('state \<Rightarrow> 'b). x' |\<notin>| {|x|} \<longrightarrow> x' \<acute>fst = x' \<acute>snd\<rrangle>"
    unfolding id_def id_bar_def 
    by (simp add: id_bar_pred_def id_pred_def)
  also have "... = {(\<sigma>, \<sigma>'). (\<exists>\<sigma>''. (\<sigma>, \<sigma>'') \<in> \<llangle>\<ordmasculine>x = \<ordfeminine>x\<rrangle> \<and>
      (\<sigma>'', \<sigma>') \<in> \<llangle>\<forall>x'. x' \<noteq> x \<longrightarrow> x' \<acute>fst = x' \<acute>snd\<rrangle>)}"
    by (simp add: relcomp_unfold)
  also have "... = {(\<sigma>, \<sigma>'). True}"
  proof -
    have "\<forall>\<sigma> \<sigma>'. \<exists>\<sigma>''. \<guillemotleft>\<ordfeminine>x = \<ordmasculine>x\<guillemotright> (\<sigma>, \<sigma>'') \<and> \<guillemotleft>\<forall>x' :: ('state \<Rightarrow> 'b). (x' \<noteq> x \<longrightarrow> \<ordfeminine>x' = \<ordmasculine>x')\<guillemotright> (\<sigma>'', \<sigma>')"
    proof -
      fix \<sigma> \<sigma>' \<sigma>''
      (*cannot complete this without constructing the record*)
      (*define \<sigma>'' :: 'state where "\<sigma>'' = setvar x (getvar x \<sigma>) \<sigma>'"*)
      have "\<guillemotleft>\<ordfeminine>x = \<ordmasculine>x\<guillemotright> (\<sigma>, \<sigma>'') \<and> \<guillemotleft>\<forall>x' :: ('state \<Rightarrow> 'b). (x' \<noteq> x \<longrightarrow> \<ordfeminine>x' = \<ordmasculine>x')\<guillemotright> (\<sigma>'', \<sigma>')" 
        sorry
      thus ?thesis sorry
    qed
    then show ?thesis sorry
  qed
  finally show ?thesis by simp
qed*)
(*proof -
  have "id(x) O id_bar({|x|}) = {(\<sigma>,\<sigma>'). get_var x \<sigma> = get_var x \<sigma>'} O 
      {(\<sigma>,\<sigma>'). \<forall>x'::'varname. x' |\<notin>| {|x|} \<longrightarrow> get_var x' \<sigma> = get_var x' \<sigma>'}"
    unfolding id_def id_bar_def by simp
  also have "... = {(\<sigma>, \<sigma>'). (\<exists>\<sigma>''. (\<sigma>, \<sigma>'') \<in> {(\<sigma>,\<sigma>'). get_var x \<sigma> = get_var x \<sigma>'} \<and>
      (\<sigma>'', \<sigma>') \<in> {(\<sigma>,\<sigma>'). \<forall>x'::'varname. x' \<noteq> x \<longrightarrow> get_var x' \<sigma> = get_var x' \<sigma>'})}"
    by (simp add: relcomp_unfold)
  also have "... = {(\<sigma>, \<sigma>'). True}"
  proof -
    have "\<exists>\<sigma>''. (\<sigma>,\<sigma>'') \<in> {(\<sigma>,\<sigma>'). get_var x \<sigma> = get_var x \<sigma>'} \<and> (\<sigma>'',\<sigma>') \<in> {(\<sigma>,\<sigma>'). \<forall>x'. (x' \<noteq> x \<longrightarrow> get_var x' \<sigma> = get_var x' \<sigma>')}" for \<sigma> \<sigma>'
      by (intro exI[of _ "set_var x (get_var x \<sigma>) \<sigma>'"]) (simp add: get_set1 get_set2)
    then show ?thesis by auto
  qed
  finally show ?thesis by simp
qed*)


(* Original lines 449-501. *)
lemma frame_restrict:
  assumes restrict_set: "Z |\<subseteq>| X"
  assumes nochange_Y: "Y |\<inter>| X = {||}"
  assumes rely_nochange_Y: "r \<subseteq> id_set Y"
  shows "rely r \<iinter> X:\<^sub>s\<lparr>q \<inter> (id_set Y)\<rparr> \<ge> rely r \<iinter> Z:\<^sub>s\<lparr>q\<rparr>"
proof -            
  have r_nochange_Y: "r = r \<inter> (id_set Y)" 
    using rely_nochange_Y by blast 
  have Y_in_Xbar: "\<And>v. v |\<in>| Y \<longrightarrow> v |\<notin>| X"
    using nochange_Y by blast 
  have g_nochange_Y: "id_bar X \<subseteq> id_set Y"
  proof(rule subsetI)
    fix s
    assume asm: "s \<in> id_bar X"

    have "id_bar_pred X s"
      using asm id_bar_def by auto
    then have "id_set_pred Y s" 
      using id_set_pred_def id_bar_pred_def by (simp add: Y_in_Xbar)
    then show "s \<in> id_set Y"
      by (simp add: id_set_def)
  qed
  have g_nochange_Ya: "id_set Y \<inter> id_bar X = id_bar X"
    using g_nochange_Y by blast 
  have bar_X_Z: "id_bar Z \<subseteq> id_bar X"
    using restrict_set id_bar_narrow by auto
  have "rely r \<iinter> X:\<^sub>s\<lparr>q \<inter> (id_set Y)\<rparr> = rely r \<iinter> guar\<^sub>\<pi>(id_bar X) \<iinter> \<lparr>q \<inter> (id_set Y)\<rparr>" 
    by (simp add: seq_conj.sync_assoc var_frame_set_def)
  also have "\<dots> = rely(r \<inter> (id_set Y)) \<iinter> guar\<^sub>\<pi>(id_bar X) \<iinter> \<lparr>q \<inter> (id_set Y)\<rparr>"
    using r_nochange_Y by presburger
  also have "\<dots> = rely r \<iinter> rely(id_set Y) \<iinter> guar\<^sub>\<pi>(id_bar X) \<iinter> \<lparr>q \<inter> (id_set Y)\<rparr>" 
    using rely_conj_rely by presburger 
  also have "\<dots> = rely r \<iinter> rely(id_set Y) \<iinter> guar\<^sub>\<pi>(id_set Y \<inter> id_bar X) \<iinter> \<lparr>q \<inter> (id_set Y)\<rparr>" 
    using g_nochange_Ya by presburger 
  also have "\<dots> = rely r \<iinter> rely(id_set Y) \<iinter> guar\<^sub>\<pi>(id_set Y) \<iinter> guar\<^sub>\<pi>(id_bar X) \<iinter> \<lparr>q \<inter> (id_set Y)\<rparr>" 
    using pgm_guar_conj_pgm_guar seq_conj.sync_assoc by presburger
  also have "\<dots> = rely r \<iinter> guar\<^sub>\<pi>(id_bar X) \<iinter> (rely(id_set Y) \<iinter> guar\<^sub>\<pi>(id_set Y) \<iinter> \<lparr>q \<inter> (id_set Y)\<rparr>)" 
    using conj.left_commute seq_conj.sync_assoc by presburger
  also have "\<dots> = rely r \<iinter> guar\<^sub>\<pi>(id_bar X) \<iinter> (rely(id_set Y) \<iinter> guar\<^sub>\<pi>(id_set Y) \<iinter> \<lparr>q \<inter> (id_set Y)\<^sup>*\<rparr>)"
    using id_set_trans by metis 
  also have "\<dots> = rely r \<iinter> guar\<^sub>\<pi>(id_bar X) \<iinter> (rely(id_set Y) \<iinter> guar\<^sub>\<pi>(id_set Y) \<iinter> \<lparr>q\<rparr>)"  
    using spec_trading[where r = "id_set Y" and g = "id_set Y"] 
    by (simp add: seq.sup_inf_biq.commute)
  also have "\<dots> = rely r \<iinter> rely(id_set Y) \<iinter> guar\<^sub>\<pi>(id_set Y) \<iinter> guar\<^sub>\<pi>(id_bar X) \<iinter> \<lparr>q\<rparr>" 
    using conj.left_commute seq_conj.sync_assoc by presburger
  also have "\<dots> = rely(r \<inter> id_set Y) \<iinter> guar\<^sub>\<pi>(id_set Y \<inter> id_bar X) \<iinter> \<lparr>q\<rparr>" 
    using pgm_guar_conj_pgm_guar rely_conj_rely seq_conj.sync_assoc by presburger
  also have "\<dots> = rely r \<iinter> guar\<^sub>\<pi>(id_bar X) \<iinter> \<lparr>q\<rparr>"
    using r_nochange_Y g_nochange_Ya by presburger
  also have "\<dots> \<ge> rely r \<iinter> guar\<^sub>\<pi>(id_bar Z) \<iinter> \<lparr>q\<rparr>" 
    using bar_X_Z pgm_guar_strengthen seq_conj.sync_mono by auto
  finally show ?thesis by (simp add: seq_conj.sync_assoc var_frame_set_def)
qed
