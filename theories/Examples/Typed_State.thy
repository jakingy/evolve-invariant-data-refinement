section \<open>Typed instance of state for example\<close>

theory Typed_State
  imports "HOL-Library.Word" "HOL-Eisbach.Eisbach" Queue Commands.Open_Assignments
  keywords "define_var" :: thy_decl
begin

no_notation Sublist.parallel (infixl "\<parallel>" 50)
declare [[typedef_overloaded]]

named_theorems simp_vars
  "generated simplification rules for variables declared with define_var"

datatype typed_value =
    NatSetValue "nat set"
  | NatQueueValue "nat queue"
  | Word64Value "64 word"
  | NatValue nat
  | IntValue int
  | BoolValue bool
  | UndefValue

instantiation typed_value :: has_values
begin

definition true_typed_value :: "typed_value" where
  "true_typed_value = BoolValue True"

definition false_typed_value :: "typed_value" where
  "false_typed_value = BoolValue False"

definition undef_typed_value :: "typed_value" where
  "undef_typed_value = UndefValue"

instance
  by standard
     (simp_all add: true_typed_value_def false_typed_value_def undef_typed_value_def)

end

lemma undef_eq_UndefValue [simp]:
  "(undef :: typed_value) = UndefValue"
  by (simp add: undef_typed_value_def)

text\<open>Can lift operations from regular types into \<open>typed_value\<close> compatible,
but need to specify param types and result type.\<close>
fun as_nat_set :: "typed_value \<Rightarrow> nat set option" where
  "as_nat_set (NatSetValue S) = Some S" |
  "as_nat_set _ = None"

fun as_nat_queue :: "typed_value \<Rightarrow> nat queue option" where
  "as_nat_queue (NatQueueValue Q) = Some Q" |
  "as_nat_queue _ = None"

fun as_word64 :: "typed_value \<Rightarrow> 64 word option" where
  "as_word64 (Word64Value W) = Some W" |
  "as_word64 _ = None"

fun as_nat :: "typed_value \<Rightarrow> nat option" where
  "as_nat (NatValue i) = Some i" |
  "as_nat _ = None"

fun as_int :: "typed_value \<Rightarrow> int option" where
  "as_int (IntValue i) = Some i" |
  "as_int _ = None"

fun as_bool :: "typed_value \<Rightarrow> bool option" where
  "as_bool (BoolValue b) = Some b" |
  "as_bool _ = None"

fun lift1_helper ::
  "('z \<Rightarrow> 'v::has_values) \<Rightarrow>
   ('x  \<Rightarrow> 'z) \<Rightarrow>
   'x option \<Rightarrow>
   'v"
where
  "lift1_helper put f (Some a) = put(f a)" |
  "lift1_helper put f _ = undef"

fun lift1 ::
  "('v::has_values \<Rightarrow> 'x option) \<Rightarrow>
   ('z \<Rightarrow> 'v) \<Rightarrow>
   ('x \<Rightarrow> 'z) \<Rightarrow>
   'v  \<Rightarrow> 'v"
where
  "lift1 get put f x = lift1_helper put f (get x)"

fun lift2_helper ::
  "('z \<Rightarrow> 'v::has_values) \<Rightarrow>
   ('x \<Rightarrow> 'y \<Rightarrow> 'z) \<Rightarrow>
   'x option \<Rightarrow>
   'y option \<Rightarrow>
   'v"
where
  "lift2_helper put f (Some a) (Some b) = put(f a b)" |
  "lift2_helper put f _ _ = undef"

fun lift2 ::
  "('v::has_values \<Rightarrow> 'x option) \<Rightarrow>
   ('v \<Rightarrow> 'y option) \<Rightarrow>
   ('z \<Rightarrow> 'v) \<Rightarrow>
   ('x \<Rightarrow> 'y \<Rightarrow> 'z) \<Rightarrow>
   'v \<Rightarrow> 'v \<Rightarrow> 'v"
where
  "lift2 get1 get2 put f x y = lift2_helper put f (get1 x) (get2 y)"

text\<open>Fancy eisbach method magic to simplify value type work. Can prove a lemma with assumed
datatypes of \<open>typed_value\<close> and it will then do all the undefined cases automatically.

For example:
\<open>have case_with_expected_datatypes: "set_member (SetValue xv) (NatValue yv)"
  by ...

show "\<open>set_member\<close> x y"
by (cases x; cases y; auto_undefined_types
      defined_case: case_with_expected_datatypes)
\<close>
Also see \<open>removal_equivalence\<close> lemma for another example which doesn't use \<open>defined_case\<close>, but instead
auto proves all undefined subgoals leaving only the important one.

\<open>  apply (cases wo; auto_undefined_types)
   ... only have to worry about wo = WordValue W from here onwards
\<close>\<close>
method auto_undefined_types uses defined_case add =
  (solves \<open>simp only: defined_case\<close> | solves \<open>simp add:add\<close> | -)

locale typed_frame_state =
  frame_state seq nil par skip conj chaos test aczel_atom
    exists exists_first exists_last exists_bool exists_bool_first exists_bool_last exists_sets get set
  for seq :: "'a::complete_distrib_lattice \<Rightarrow> 'a \<Rightarrow> 'a"  (infixl \<open>;\<close> 77)
  and nil :: "'a"
  and par :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixl \<open>\<parallel>\<close> 70)
  and skip :: "'a"
  and conj :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixl \<open>\<iinter>\<close> 75)
  and chaos :: "'a"
  and test :: "'state set \<Rightarrow> 'a"  (\<open>\<tau>\<close>)
  and aczel_atom :: "('state rel \<times> 'state rel) \<Rightarrow> 'a"
  and exists :: "(typed_value LValue) \<Rightarrow> 'a \<Rightarrow> 'a"
  and exists_first :: "(typed_value LValue) \<Rightarrow> 'a \<Rightarrow> 'a"
  and exists_last :: "(typed_value LValue) \<Rightarrow> 'a \<Rightarrow> 'a"
  and exists_bool :: "(typed_value LValue) \<Rightarrow> 'state rel \<Rightarrow> 'state rel"
  and exists_bool_first :: "(typed_value LValue) \<Rightarrow> 'state rel \<Rightarrow> 'state rel"
  and exists_bool_last :: "(typed_value LValue) \<Rightarrow> 'state rel \<Rightarrow> 'state rel"
  and exists_sets :: "(typed_value LValue) \<Rightarrow> 'state set \<Rightarrow> 'state set"
  and get :: "typed_value LValue \<Rightarrow> 'state \<Rightarrow> typed_value"
  and set :: "typed_value LValue \<Rightarrow> typed_value \<Rightarrow> 'state \<Rightarrow> 'state"
begin

text\<open>Eisbach method to automatically deduce all other l-values have not changed in an update.
Takes two params:
\<open>update_lval\<close> is a theorem showing that the pair of states \<open>(\<sigma>, \<sigma>')\<close> is an element of some \<open>update lv k\<close>; and 
\<open>add\<close> is just like \<open>simp add\<close>.\<close>

method simp_lvals uses update_lval add =
  (simp add: add simp_vars open_update_unchanged_lvals[OF update_lval] update_lval)

end

text \<open>\<open>define_var x\<close> introduces the three names used by the typed
examples: \<open>x\<close> is the state-value getter, \<open>x_lval\<close> is the base
l-value, and \<open>x_lve\<close> is the l-value expression. It also introduces
\<open>x_simps\<close>, containing its definitions and dereference-evaluation
rule \<open>eval_Deref_x\<close>, and adds those facts to \<open>simp_vars\<close>.
The dereference-evaluation rule is not added to the global simplifier.
It is intended for use inside a \<open>typed_frame_state\<close> context.\<close>

ML \<open>
local
  fun define name lthy =
    let
      val base = Binding.name_of name;
      val lve_name = Binding.suffix_name "_lve" name;
      val lval_name = Binding.suffix_name "_lval" name;
      val value_name = name;

      fun define_const binding rhs ctxt =
        Local_Theory.define ((binding, NoSyn),
          ((Binding.suffix_name "_def" binding, []),
          Syntax.read_term ctxt rhs)) ctxt;

      val ((_, (_, lve_def)), lthy1) =
        define_const lve_name
          ("(Var ''" ^ base ^ "'' :: ('state, typed_value) LValueExpr)") lthy;
      val ((_, (_, lval_def)), lthy2) =
        define_const lval_name
          ("(Base ''" ^ base ^ "'' :: typed_value LValue)") lthy1;
      val ((_, (_, value_def)), lthy3) =
        define_const value_name
          ("(\<lambda>\<sigma>. get " ^ base ^ "_lval \<sigma>)") lthy2;

      val eval_prop = Syntax.read_prop lthy3
        ("\<And>\<sigma>. \<lbrakk>Deref " ^ base ^ "_lve\<rbrakk>\<sigma> = " ^
         base ^ " \<sigma>");
      val eval_thm = Goal.prove lthy3 [] [] eval_prop (fn {context, ...} =>
        simp_tac (context |> Simplifier.add_simps [lve_def, lval_def, value_def]) 1);
      val (_, lthy4) = Local_Theory.note
        ((Binding.name ("eval_Deref_" ^ base),
          [Attrib.internal \<^here>
            (K (Named_Theorems.add @{named_theorems simp_vars}))]),
         [eval_thm]) lthy3;
      val (_, lthy5) = Local_Theory.note
        ((Binding.suffix_name "_simps" name,
         [Attrib.internal \<^here>
            (K (Named_Theorems.add @{named_theorems simp_vars}))]),
         [eval_thm, value_def, lval_def, lve_def]) lthy4;
    in lthy5 end;
in
  val _ = Outer_Syntax.local_theory \<^command_keyword>\<open>define_var\<close>
    "define a typed base variable, its l-value, and its value getter"
    (Parse.binding >> define)
end
\<close>

end
