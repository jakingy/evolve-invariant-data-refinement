(* Extracts from isabelle/new_rg_algebra/Rely_Guarantee/Termination.thy. *)
(* These are source excerpts, not a standalone buildable theory. *)

(* Original lines 170-172. *)
lemma rely_guar_term:
  shows "rely r \<iinter> guar\<^sub>\<pi> g \<iinter> terminate = (\<pi> g \<squnion> \<epsilon> r)* ; (\<epsilon> r)\<^sup>\<omega> ; (nil \<squnion> \<epsilon>(-r) ; \<top>)" 
  using rely_guar_terminate by blast 


(* Original lines 174-187. *)
lemma atomic_terminating: "terminate \<ge> Aczel_top"
proof -
  have "terminate = (\<pi> \<top> \<squnion> \<epsilon> \<top>)* ; (\<epsilon> \<top>)\<^sup>\<omega>" 
    using guar_basis_top terminate_def by argo
  also have "... \<ge> (\<pi> \<top> \<squnion> \<epsilon> \<top>)* ; nil" (is "_ \<ge> ?rhs") 
    using seq.iter_to_0 seq_par.seq_mono_right by blast
  also have "?rhs = (\<pi> \<top> \<squnion> \<epsilon> \<top>)*"
    by simp
  also have "\<dots> \<ge> \<pi> \<top> \<squnion> \<epsilon> \<top>" (is "_ \<ge> ?rhs") 
    by (simp add: seq.finite_iter_to_1)
  also have "?rhs \<ge> Aczel_top" 
    using guar_basis_top by order
  finally show ?thesis .
qed


(* Original lines 189-198. *)
lemma pgm_terminates: "\<pi> g \<le> terminate"
proof -
  have "\<pi> g \<le> \<pi> UNIV"
    by (rule pgm_mono) auto
  also have "\<dots> \<le> \<A>"
    by (simp add: Atomic_def2)
  also have "\<dots> \<le> terminate"
    by (rule atomic_terminating)
  finally show ?thesis .
qed


(* Original lines 200-209. *)
lemma env_terminates: "\<epsilon> r \<le> terminate"
proof -
  have "\<epsilon> r \<le> \<epsilon> UNIV"
    using env.hom_mono by auto
  also have "\<dots> \<le> \<A>"
    by (simp add: Atomic_def2)
  also have "\<dots> \<le> terminate"
    by (rule atomic_terminating)
  finally show ?thesis .
qed


(* Original lines 211-218. *)
lemma test_terminates: "\<tau> p \<le> terminate"
proof -
  have "\<tau> p \<le> nil"
    by (simp add: seq.image_is_test seq.test_top)
  also have "\<dots> \<le> terminate"
    by (rule terminate_nil)
  finally show ?thesis .
qed


(* Original lines 220-224. *)
lemma terminate_seq:
  assumes "a \<le> terminate"
  assumes "b \<le> terminate"
  shows "a ; b \<le> terminate"
  using assms seq_terminate_terminate by (simp add: seq.op_idem_mono)
