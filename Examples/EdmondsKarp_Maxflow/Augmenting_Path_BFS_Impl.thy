theory Augmenting_Path_BFS_Impl
imports Augmenting_Path_BFS
begin


subsection \<open>Imperative Implementation\<close>

  context Impl_Succ begin
    definition op_bfs :: "'ga \<Rightarrow> node \<Rightarrow> node \<Rightarrow> path option nres" 
      where [simp]: "op_bfs c s t \<equiv> Graph.bfs2 (absG c) (succ c) s t"
  
    lemma pat_op_dfs[pat_rules]: 
      "Graph.bfs2$(absG$c)$(succ$c)$s$t \<equiv> UNPROTECT op_bfs$c$s$t" by simp 
  
    sepref_register "PR_CONST op_bfs" 
      :: "'ig \<Rightarrow> node \<Rightarrow> node \<Rightarrow> path option nres"  
  
    type_synonym ibfs_state 
      = "bool \<times> (node,node) i_map \<times> node set \<times> node set \<times> nat"

    sepref_register Graph.init_state :: "node \<Rightarrow> ibfs_state nres"
    schematic_goal init_state_impl:
      fixes src :: nat
      notes [id_rules] = 
        itypeI[Pure.of src "TYPE(nat)"]
      shows "hn_refine (hn_val nat_rel src srci) 
        (?c::?'c Heap) ?\<Gamma>' ?R (Graph.init_state src)"
      using [[id_debug, goals_limit = 1]]
      unfolding Graph.init_state_def
      apply (rewrite in "[src\<mapsto>src]" iam.fold_custom_empty)
      apply (subst ls.fold_custom_empty)
      apply (subst ls.fold_custom_empty)
      apply (rewrite in "insert src _" fold_set_insert_dj)
      apply (rewrite in "_(\<hole>\<mapsto>src)" fold_COPY)
      apply sepref
      done
    concrete_definition (in -) init_state_impl uses Impl_Succ.init_state_impl
    lemmas [sepref_fr_rules] = init_state_impl.refine[OF this_loc,to_hfref]

    schematic_goal bfs_impl:
      (*notes [sepref_opt_simps del] = imp_nfoldli_def 
          -- \<open>Prevent the foreach-loop to be unfolded to a fixed-point, 
              to produce more readable code for presentation purposes.\<close>*)
      notes [sepref_opt_simps] = heap_WHILET_def
      fixes s t :: nat
      notes [id_rules] = 
        itypeI[Pure.of s "TYPE(nat)"]
        itypeI[Pure.of t "TYPE(nat)"]
        itypeI[Pure.of c "TYPE('ig)"]
        \<comment> \<open>Declare parameters to operation identification\<close>
      shows "hn_refine (
        hn_ctxt (isG) c ci 
      * hn_val nat_rel s si 
      * hn_val nat_rel t ti) (?c::?'c Heap) ?\<Gamma>' ?R (PR_CONST op_bfs c s t)"
      unfolding op_bfs_def PR_CONST_def
      unfolding Graph.bfs2_def Graph.pre_bfs2_def 
        Graph.inner_loop2_def Graph.extract_rpath_def
      unfolding nres_monad_laws  
      apply (rewrite in "nfoldli _ _ \<hole> _" fold_set_insert_dj)
      apply (subst HOL_list.fold_custom_empty)+
      apply (rewrite in "let N={} in _" ls.fold_custom_empty)
      using [[id_debug, goals_limit = 1]]
      apply sepref
      done
    
    concrete_definition (in -) bfs_impl uses Impl_Succ.bfs_impl
      \<comment> \<open>Extract generated implementation into constant\<close>
    prepare_code_thms (in -) bfs_impl_def
   
    lemmas bfs_impl_fr_rule = bfs_impl.refine[OF this_loc,to_hfref]  
  
  end

  export_code bfs_impl checking SML_imp

end