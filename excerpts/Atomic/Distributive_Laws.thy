(* Extracts from isabelle/new_rg_algebra/Atomic/Distributive_Laws.thy. *)
(* These are source excerpts, not a standalone buildable theory. *)

(* Original lines 582-622. *)
lemma atom_iter_sync_infinite_iter_non_test:
  assumes decomposes: "\<And>c. decomposes c" 
  assumes non_test: "nil \<otimes> c = pre c ; \<bottom>"
  assumes a: "a \<in> Atom"
  shows "a\<^sup>\<omega> \<otimes> c\<^sup>\<infinity> = (a\<^sup>\<omega> \<otimes> c)\<^sup>\<infinity>" 
proof (rule antisym)
  show "a\<^sup>\<omega> \<otimes> c\<^sup>\<infinity> \<le> (a\<^sup>\<omega> \<otimes> c)\<^sup>\<infinity>" 
  proof -
    have hyp: "(a\<^sup>\<omega> \<otimes> c) ; (a\<^sup>\<omega> \<otimes> c\<^sup>\<infinity>) = a\<^sup>\<omega> \<otimes> c\<^sup>\<infinity>" 
    proof -
      have "(a\<^sup>\<omega> \<otimes> c) ; (a\<^sup>\<omega> \<otimes> c\<^sup>\<infinity>) = a\<^sup>\<omega> \<otimes> (c ; c\<^sup>\<infinity>)" 
        by (simp add: a afp_sync_seq atomic_iter_is_afp decomposes) 
      also have "\<dots> = a\<^sup>\<omega> \<otimes> c\<^sup>\<infinity>" 
        using op1.infinite_iter_unfold by simp 
      finally show ?thesis .
    qed 
    then show ?thesis using op1.infinite_iter_induct by simp 
  qed
  show "a\<^sup>\<omega> \<otimes> c\<^sup>\<infinity> \<ge> (a\<^sup>\<omega> \<otimes> c)\<^sup>\<infinity>" 
  proof -
    have "a\<^sup>\<omega> \<otimes> c\<^sup>\<infinity> = (a ; a\<^sup>\<omega>)\<^sup>\<omega> \<otimes> c\<^sup>\<infinity>" 
      using op_iter_iter by simp 
    also have "\<dots> \<ge> (a ; a\<^sup>\<omega> \<otimes> c)\<^sup>\<infinity>" (is "_ \<ge> ?rhs")
      by (simp add: iter_infinite_iter_interchange) 
    also have "?rhs = (a\<^sup>\<omega> \<otimes> c)\<^sup>\<infinity>" 
    proof -
      have "a\<^sup>\<omega> \<otimes> c = nil \<otimes> c \<squnion> a ; a\<^sup>\<omega> \<otimes> c" 
        by (metis sup_sync op1.iter_unfold) 
      also have "\<dots> = pre c ; \<bottom> \<squnion> a ; a\<^sup>\<omega> \<otimes> c" 
        by (simp add: non_test)
      also have "\<dots> = pre c ; (a ; a\<^sup>\<omega> \<otimes> c)" 
        by (simp add: pre_seq_sup) 
      also have "\<dots> = a ; a\<^sup>\<omega> \<otimes> pre c ; c" 
        by (simp add: pre_seq_sync) 
      also have "\<dots> = a ; a\<^sup>\<omega> \<otimes> c" 
        using pre_seq by presburger 
      finally show ?thesis by simp 
    qed
    finally show ?thesis .
  qed
qed


(* Original lines 624-638. *)
text \<open>This lemma follows from the previous two.\<close>
lemma atom_iter_sync_iter_non_test:
  assumes decomposes: "\<And>c. decomposes c" 
  assumes non_test: "nil \<otimes> c = pre c ; \<bottom>"
  assumes "a \<in> Atom"
  shows "a\<^sup>\<omega> \<otimes> c\<^sup>\<omega> = (a\<^sup>\<omega> \<otimes> c)\<^sup>\<omega>" 
proof -
  have "a\<^sup>\<omega> \<otimes> c\<^sup>\<omega> = a\<^sup>\<omega> \<otimes> c* \<squnion> a\<^sup>\<omega> \<otimes> c\<^sup>\<infinity>" 
    by (simp add: iter_isolation sync_sup) 
  also have z2: "\<dots> = (a\<^sup>\<omega> \<otimes> c)* \<squnion> (a\<^sup>\<omega> \<otimes> c)\<^sup>\<infinity>" 
    by (simp add: assms atom_iter_sync_finite_iter atom_iter_sync_infinite_iter_non_test)
  also have z3: "\<dots> = (a\<^sup>\<omega> \<otimes> c)\<^sup>\<omega>" 
    using iter_isolation by auto 
  finally show ?thesis .
qed


(* Original lines 640-660. *)
text \<open>The non-test side condition above can be discharged for an arbitrary command
by first separating its immediate behaviour.\<close>
lemma sync_neut_is_assert_test:
  obtains p t where "c \<otimes> nil = \<lbrace>p\<rbrace> ; \<tau> t"
proof -
  obtain p where pre_c: "pre c = \<lbrace>p\<rbrace>"
    using pre_is_assert by blast
  obtain t where test_c: "c \<sqinter> nil = \<tau> t"
    using neut_sync_is_test obtain_test by (metis inf_commute)

  have "c \<otimes> nil = nil \<otimes> c"
    by (rule sync_commute)
  also have "\<dots> = pre c ; (nil \<sqinter> c)"
    by (rule neut_sync_to_pre)
  also have "\<dots> = \<lbrace>p\<rbrace> ; (c \<sqinter> nil)"
    by (metis pre_c inf_commute)
  also have "\<dots> = \<lbrace>p\<rbrace> ; \<tau> t"
    by (simp only: test_c)
  finally show ?thesis
    by (simp add: that)
qed


(* Original lines 662-677. *)
text \<open>The immediate behaviour of a command is sequentially idempotent.\<close>
lemma sync_neut_idem: "(c \<otimes> nil) ; (c \<otimes> nil) = c \<otimes> nil"
proof -
  obtain p t where z: "c \<otimes> nil = \<lbrace>p\<rbrace> ; \<tau> t"
    using sync_neut_is_assert_test by auto

  have "(c \<otimes> nil) ; (c \<otimes> nil) = \<lbrace>p\<rbrace> ; \<tau> t ; \<lbrace>p\<rbrace> ; \<tau> t"
    by (simp add: z seq_assoc)
  also have "\<dots> = \<lbrace>p\<rbrace> ; \<tau> t ; \<tau> t"
    by (simp add: assert_op_test_op_assert)
  also have "\<dots> = \<lbrace>p\<rbrace> ; \<tau> t"
    by (simp add: image_is_test test_seq_idem seq_assoc)
  also have "\<dots> = c \<otimes> nil"
    by (simp only: z)
  finally show ?thesis .
qed


(* Original lines 679-704. *)
lemma sync_neut_iter:
  "(c \<otimes> nil)\<^sup>\<omega> = nil \<squnion> (c \<otimes> nil) ; \<top>"
proof (rule antisym)
  show "(c \<otimes> nil)\<^sup>\<omega> \<le> nil \<squnion> (c \<otimes> nil) ; \<top>"
  proof -
    have "(c \<otimes> nil)\<^sup>\<omega> = nil \<squnion> (c \<otimes> nil) ; (c \<otimes> nil)\<^sup>\<omega>"
      using op1.iter_unfold by auto
    also have "\<dots> \<le> nil \<squnion> (c \<otimes> nil) ; \<top>"
      by (meson seq_mono_right sup_mono_right top_greatest)
    finally show ?thesis .
  qed
  show "(c \<otimes> nil)\<^sup>\<omega> \<ge> nil \<squnion> (c \<otimes> nil) ; \<top>"
  proof -
    have "nil \<squnion> (c \<otimes> nil) ; (nil \<squnion> (c \<otimes> nil) ; \<top>) =
        nil \<squnion> ((c \<otimes> nil) ; nil \<squnion>
        (c \<otimes> nil) ; (c \<otimes> nil) ; \<top>)"
      by (simp add: seq_assoc seq_sup)
    also have z: "\<dots> = nil \<squnion> (c \<otimes> nil) \<squnion> (c \<otimes> nil) ; \<top>"
      by (simp add: sync_neut_idem sup_assoc)
    have "nil \<squnion> (c \<otimes> nil) \<squnion> (c \<otimes> nil) ; \<top> \<ge>
        nil \<squnion> (c \<otimes> nil) ; \<top>"
      by (meson sup.cobounded1 sup_mono_left)
    then show ?thesis
      using calculation op1.iter_induct z by presburger
  qed
qed


(* Original lines 706-728. *)
text \<open>The possibly infinite arbitrary iteration of a command synced with nil
is an assert.\<close>
lemma sync_neut_iter_is_assert:
  obtains p where "(c \<otimes> nil)\<^sup>\<omega> = \<lbrace>p\<rbrace>"
proof -
  obtain p1 t1 where z: "c \<otimes> nil = \<lbrace>p1\<rbrace> ; \<tau> t1"
    using sync_neut_is_assert_test by auto

  have partial_assert: "nil \<squnion> \<tau> t1 ; \<top> = \<lbrace>-t1\<rbrace>"
    by (simp add: assert_def image_is_test not_not test_negate)

  have "(c \<otimes> nil)\<^sup>\<omega> = nil \<squnion> (c \<otimes> nil) ; \<top>"
    by (simp add: sync_neut_iter)
  also have "\<dots> = nil \<squnion> \<lbrace>p1\<rbrace> ; \<tau> t1 ; \<top>"
    by (simp add: z)
  also have "\<dots> = \<lbrace>p1\<rbrace> ; (nil \<squnion> \<tau> t1 ; \<top>)"
    by (simp add: assert_op_sup_right seq_assoc)
  also have "\<dots> = \<lbrace>p1\<rbrace> ; \<lbrace>-t1\<rbrace>"
    by (simp add: partial_assert)
  also have "\<dots> = \<lbrace>p1 \<sqinter> -t1\<rbrace>"
    by (simp add: assert_op_assert)
  finally show ?thesis ..
qed


(* Original lines 730-732. *)
text \<open>magic sync nil is magic.\<close>
lemma magic_sync_neut: "\<bottom> = \<bottom> \<otimes> nil"
  using bot_compat neut_sync_atom sync_commute by auto


(* Original lines 734-746. *)
text \<open>An atomic iter sync an assert is the assert.\<close>
lemma atom_iter_sync_assert:
  assumes a_atom: "a \<in> Atom"
  shows "a\<^sup>\<omega> \<otimes> \<lbrace>p\<rbrace> = \<lbrace>p\<rbrace>"
proof -
  have "a\<^sup>\<omega> \<otimes> \<lbrace>p\<rbrace> = a\<^sup>\<omega> \<otimes> (\<lbrace>p\<rbrace> ; nil)"
    by simp
  also have "\<dots> = \<lbrace>p\<rbrace> ; (a\<^sup>\<omega> \<otimes> nil)"
    using assert_op_sync_right by blast
  also have "\<dots> = \<lbrace>p\<rbrace>"
    by (simp add: a_atom op2.commute neut_sync_atom_iter)
  finally show ?thesis .
qed


(* Original lines 748-758. *)
text \<open>Syncing with an atomic iter does not effect immediate behaviour.\<close>
lemma atom_iter_sync_neut_right:
  assumes a_atom: "a \<in> Atom"
  shows "a\<^sup>\<omega> \<otimes> c \<otimes> nil = c \<otimes> nil"
proof -
  have "a\<^sup>\<omega> \<otimes> c \<otimes> nil = c \<otimes> (nil \<otimes> a\<^sup>\<omega>)"
    by (simp add: op2.left_commute sync_commute)
  also have "\<dots> = c \<otimes> nil"
    by (simp add: a_atom neut_sync_atom_iter)
  finally show ?thesis .
qed


(* Original lines 760-763. *)
text \<open>A command can be rewritten as arbitrary choice between immediately terminating
behaviour and behaviour with at least one step. Immediately aborting behaviour is on both sides.\<close>
lemma split_immed_behaviour: "c = (c \<otimes> nil) \<squnion> (c \<otimes> \<iota> ; \<gamma>)"
  by (metis op1.iter_unfold op2.right_neutral sync_neut sync_sup)


(* Original lines 765-869. *)
text \<open>An atomic iter distributes into iter.\<close>
lemma atom_iter_sync_iter:
  assumes decomposes: "\<And>c. decomposes c"
  assumes a_atom: "a \<in> Atom"
  shows "a\<^sup>\<omega> \<otimes> c\<^sup>\<omega> = (a\<^sup>\<omega> \<otimes> c)\<^sup>\<omega>"
proof -
  obtain p where z: "(c \<otimes> nil)\<^sup>\<omega> = \<lbrace>p\<rbrace>"
    using sync_neut_iter_is_assert by auto

  have c_iter:
    "c\<^sup>\<omega> = \<lbrace>p\<rbrace> ; ((c \<otimes> \<iota> ; \<gamma>) ; \<lbrace>p\<rbrace>)\<^sup>\<omega>"
  proof -
    have "c\<^sup>\<omega> = ((c \<otimes> nil) \<squnion> (c \<otimes> \<iota> ; \<gamma>))\<^sup>\<omega>"
      using split_immed_behaviour by auto
    also have "\<dots> = (c \<otimes> nil)\<^sup>\<omega> ;
        ((c \<otimes> \<iota> ; \<gamma>) ; (c \<otimes> nil)\<^sup>\<omega>)\<^sup>\<omega>"
      by (simp add: iter_sup_decomposition)
    also have "\<dots> = \<lbrace>p\<rbrace> ; ((c \<otimes> \<iota> ; \<gamma>) ; \<lbrace>p\<rbrace>)\<^sup>\<omega>"
      by (simp add: z)
    finally show ?thesis .
  qed

  have non_test_step:
    "(c \<otimes> (nil \<otimes> \<iota>) ; (nil \<otimes> \<gamma>)) ; \<lbrace>p\<rbrace> =
     (c \<otimes> \<bottom> ; nil) ; \<lbrace>p\<rbrace>"
    by (simp add: iota_is_compat neut_sync_atom)
  have non_test_lhs:
    "(c \<otimes> \<bottom> ; nil) ; \<lbrace>p\<rbrace> = pre c ; \<bottom>"
    by (metis op2.commute bot_annihilates_left pre_seq_magic seq_assoc)

  have non_test:
    "nil \<otimes> ((c \<otimes> \<iota> ; \<gamma>) ; \<lbrace>p\<rbrace>) =
     pre ((c \<otimes> \<iota> ; \<gamma>) ; \<lbrace>p\<rbrace>) ; \<bottom>"
  proof -
    have "\<bottom> = \<bottom> \<otimes> nil"
      by (rule magic_sync_neut)
    then show ?thesis
      using neut_sync_assert[of p] neut_sync_seq[of \<iota> \<gamma>] neut_sync_seq[of "\<iota> ; \<gamma> \<otimes> c" "\<lbrace>p\<rbrace>"]
        non_test_lhs non_test_step pre_seq[of "\<bottom>"] pre_seq_magic[of "(c \<otimes> \<iota> ; \<gamma>) ; \<lbrace>p\<rbrace>"]
        pre_seq_magic[of c] pre_seq_magic[of "\<bottom>"] sync_assoc[of nil "\<iota> ; \<gamma>" c]
        sync_assoc[of "\<bottom>" nil "(c \<otimes> \<iota> ; \<gamma>) ; \<lbrace>p\<rbrace>"] sync_assoc[of "\<bottom>" "\<bottom>" c]
        sync_commute[of c "\<iota> ; \<gamma>"] sync_commute[of c "nil \<otimes> \<iota> ; \<gamma>"] by argo
  qed

  have iter_sync_iter:
    "a\<^sup>\<omega> \<otimes> ((c \<otimes> \<iota> ; \<gamma>) ; \<lbrace>p\<rbrace>)\<^sup>\<omega> =
     (a\<^sup>\<omega> \<otimes> ((c \<otimes> \<iota> ; \<gamma>) ; \<lbrace>p\<rbrace>))\<^sup>\<omega>"
    using a_atom non_test decomposes atom_iter_sync_iter_non_test
    by simp

  have a_sync_step:
    "a\<^sup>\<omega> \<otimes> ((c \<otimes> \<iota> ; \<gamma>) ; \<lbrace>p\<rbrace>) =
     (a\<^sup>\<omega> \<otimes> c \<otimes> \<iota> ; \<gamma>) ; \<lbrace>p\<rbrace>"
  proof -
    have "a\<^sup>\<omega> \<otimes> ((c \<otimes> \<iota> ; \<gamma>) ; \<lbrace>p\<rbrace>) =
        (a\<^sup>\<omega> \<otimes> (c \<otimes> \<iota> ; \<gamma>)) ;
        (a\<^sup>\<omega> \<otimes> \<lbrace>p\<rbrace>)"
      using a_atom decomposes afp_sync_seq atomic_iter_is_afp by blast
    also have "\<dots> = (a\<^sup>\<omega> \<otimes> c \<otimes> \<iota> ; \<gamma>) ; \<lbrace>p\<rbrace>"
      by (simp add: atom_iter_sync_assert a_atom op2.assoc)
    finally show ?thesis .
  qed

  have lhs:
    "a\<^sup>\<omega> \<otimes> c\<^sup>\<omega> =
     \<lbrace>p\<rbrace> ;
       (a\<^sup>\<omega> \<otimes> ((c \<otimes> \<iota> ; \<gamma>) ; \<lbrace>p\<rbrace>))\<^sup>\<omega>"
  proof -
    have "a\<^sup>\<omega> \<otimes> c\<^sup>\<omega> =
        a\<^sup>\<omega> \<otimes> (\<lbrace>p\<rbrace> ; ((c \<otimes> \<iota> ; \<gamma>) ; \<lbrace>p\<rbrace>)\<^sup>\<omega>)"
      using c_iter by simp
    also have "\<dots> = \<lbrace>p\<rbrace> ;
        (a\<^sup>\<omega> \<otimes> ((c \<otimes> \<iota> ; \<gamma>) ; \<lbrace>p\<rbrace>)\<^sup>\<omega>)"
      by (simp add: assert_op_sync_right)
    also have "\<dots> = \<lbrace>p\<rbrace> ;
        (a\<^sup>\<omega> \<otimes> ((c \<otimes> \<iota> ; \<gamma>) ; \<lbrace>p\<rbrace>))\<^sup>\<omega>"
      using iter_sync_iter by simp
    finally show ?thesis .
  qed

  have rhs:
    "(a\<^sup>\<omega> \<otimes> c)\<^sup>\<omega> =
     \<lbrace>p\<rbrace> ;
       (a\<^sup>\<omega> \<otimes> ((c \<otimes> \<iota> ; \<gamma>) ; \<lbrace>p\<rbrace>))\<^sup>\<omega>"
  proof -
    have "(a\<^sup>\<omega> \<otimes> c)\<^sup>\<omega> =
        ((a\<^sup>\<omega> \<otimes> c \<otimes> nil) \<squnion>
         (a\<^sup>\<omega> \<otimes> c \<otimes> \<iota> ; \<gamma>))\<^sup>\<omega>"
      by (metis op1.iter_unfold op2.right_neutral sync_neut sync_sup)
    also have "\<dots> = (a\<^sup>\<omega> \<otimes> c \<otimes> nil)\<^sup>\<omega> ;
        ((a\<^sup>\<omega> \<otimes> c \<otimes> \<iota> ; \<gamma>) ;
         (a\<^sup>\<omega> \<otimes> c \<otimes> nil)\<^sup>\<omega>)\<^sup>\<omega>"
      by (simp add: iter_sup_decomposition)
    also have "\<dots> = \<lbrace>p\<rbrace> ;
        ((a\<^sup>\<omega> \<otimes> c \<otimes> \<iota> ; \<gamma>) ; \<lbrace>p\<rbrace>)\<^sup>\<omega>"
      by (simp add: atom_iter_sync_neut_right a_atom z)
    also have "\<dots> = \<lbrace>p\<rbrace> ;
        (a\<^sup>\<omega> \<otimes> ((c \<otimes> \<iota> ; \<gamma>) ; \<lbrace>p\<rbrace>))\<^sup>\<omega>"
      by (simp add: a_sync_step)
    finally show ?thesis .
  qed

  show ?thesis
    using lhs rhs by simp
qed


(* Original lines 871-885. *)
text \<open>An atomic iter distributes into infinite iter.\<close>
lemma atom_iter_sync_infinite_iter:
  assumes decomposes: "\<And>c. decomposes c"
  assumes a_atom: "a \<in> Atom"
  shows "a\<^sup>\<omega> \<otimes> c\<^sup>\<infinity> = (a\<^sup>\<omega> \<otimes> c)\<^sup>\<infinity>"
proof -
  have "a\<^sup>\<omega> \<otimes> c\<^sup>\<infinity> = a\<^sup>\<omega> \<otimes> c\<^sup>\<omega> ; \<bottom>"
    by (simp add: iter_op_bot)
  also have "\<dots> = (a\<^sup>\<omega> \<otimes> c\<^sup>\<omega>) ; \<tau> \<bottom>"
    by (simp add: sync_op_test test.bot_compat test_bot)
  also have "\<dots> = (a\<^sup>\<omega> \<otimes> c)\<^sup>\<omega> ; \<bottom>"
    using a_atom decomposes test_bot atom_iter_sync_iter by presburger
  finally show ?thesis
    by (simp add: iter_op_bot)
qed
