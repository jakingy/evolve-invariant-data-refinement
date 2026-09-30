(* Extracts from isabelle/new_rg_algebra/Rely_Guarantee/Guarantee.thy. *)
(* These are source excerpts, not a standalone buildable theory. *)

(* Original lines 150-153. *)
lemma guar_conj_iter: 
  shows "guar(g,r) \<iinter> c\<^sup>\<omega> = (guar(g,r) \<iinter> c)\<^sup>\<omega>" 
  using aczel_atom_alt decomposes guar_basis_is_atom guar_def seq_conj.atom_iter_sync_iter 
  by presburger


(* Original lines 155-159. *)
lemma guar_par_iter: 
  shows "guar(g,r) \<parallel> c\<^sup>\<omega> = (guar(g,r) \<parallel> c)\<^sup>\<omega>" 
  unfolding guar_def 
  using seq_par.atom_iter_sync_iter[where a = "aczel_atom (fst (g, r), snd (g, r))" and c = c] 
  by (metis aczel_atom_alt decomposes guar_basis_is_atom) 


(* Original lines 326-328. *)
lemma pgm_guar_conj_iter: 
  shows "guar\<^sub>\<pi> g \<iinter> c\<^sup>\<omega> = (guar\<^sub>\<pi> g \<iinter> c)\<^sup>\<omega>" 
  using pgm_guar_def guar_conj_iter by auto
