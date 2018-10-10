theory Augmenting_Path_BFS_Impl
  imports
          "../../Refine_Imperative_HOL/IICF/Impl/IICF_Rbt_Set"
          "../../Refine_Imperative_HOL/IICF/Impl/IICF_RbtMap_Map"
          Augmenting_Path_BFS 
begin


subsection \<open>Imperative Implementation\<close>

term Augmenting_Path_BFS.bfs2

context Impl_Succ begin

    abbreviation "init_state_time == 3 + rbt_insert_logN 1 + rbt_insert_logN 1"
    abbreviation "set_pick_time == 1"


    abbreviation "bfs2 cf SS s t == Augmenting_Path_BFS.bfs2 cf
                       set_insert_time map_dom_member_time  set_delete_time  map_update_time
                      set_pick_time list_append_time map_lookup_time set_empty_time set_isempty_time init_state_time SS s t"

    definition op_bfs :: "'ga \<Rightarrow> node \<Rightarrow> node \<Rightarrow> path option nrest"
      where [simp]: "op_bfs c s t \<equiv> bfs2 (absG c) (succ c) s t"
  
   (* lemma pat_op_dfs[pat_rules]: 
      "bfs2$(absG$c)$(succ$c)$s$t \<equiv> UNPROTECT op_bfs$c$s$t" by simp 
  *)
    sepref_register "PR_CONST op_bfs" 
      :: "'ig \<Rightarrow> node \<Rightarrow> node \<Rightarrow> path option nrest"  


    type_synonym ibfs_state 
      = "bool \<times> (node,node) i_map \<times> node set \<times> node set \<times> nat"

    term Pre_BFS_Impl.init_state
    thm Pre_BFS_Impl.init_state_def


    lemma P: "Pre_BFS_Impl set_pick_time" unfolding Pre_BFS_Impl_def by simp

    definition "init_state = Pre_BFS_Impl.init_state init_state_time"

definition init_state1 :: "nat \<Rightarrow> (bool \<times> (nat \<Rightarrow> nat option) \<times> nat set \<times> nat set \<times> nat) nrest" where
  "init_state1 src = do {
        m \<leftarrow> mop_map_empty 1;
        m \<leftarrow> mop_map_update (\<lambda>M. rbt_insert_logN (sizeM1' M)) m src src;
        C \<leftarrow> mop_set_empty 1;
        C \<leftarrow> mop_set_insert (\<lambda>_. rbt_insert_logN (card C + 1)) src C;
        N \<leftarrow> mop_set_empty 1;
        RETURNT (False, m, C, N, 0)
      }"

  
  
  lemma "init_state1 src \<le> init_state src"
    unfolding init_state1_def init_state_def 
    unfolding Pre_BFS_Impl.init_state_def[OF P]
    apply(rule T_specifies_I) unfolding mop_map_empty_def mop_map_update_def mop_set_empty_def
        mop_set_insert_def
      apply(vcg' \<open>clarsimp\<close>  ) by (simp add: sizeM1'_def) 




    sepref_register init_state :: "node \<Rightarrow> ibfs_state nrest"

    schematic_goal init_state_impl:
      fixes src :: nat
      notes [id_rules] = 
        itypeI[Pure.of src "TYPE(nat)"]
      shows "hn_refine (hn_val nat_rel src srci) 
        (?c::?'c Heap) ?\<Gamma>' ?R (init_state1 src)"
      using [[id_debug, goals_limit = 1]]
      unfolding init_state1_def   
      apply sepref 
      done
      concrete_definition (in -) init_state_impl uses Impl_Succ.init_state_impl

      thm init_state_impl_def
(*
    lemmas [sepref_fr_rules] = init_state_impl.refine[OF this_loc,to_hfref]
*)


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