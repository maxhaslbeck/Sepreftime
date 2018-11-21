theory Augmenting_Path_BFS_Impl
  imports
          "../../Refine_Imperative_HOL/IICF/Impl/IICF_Rbt_Set"
          "../../Refine_Imperative_HOL/IICF/Impl/IICF_RbtMap_Map"
          Augmenting_Path_BFS 
begin


definition  "oappend x' xs' = return (x'#xs')" 

lemma mop_lookup_list_as_array_rule[sepref_fr_rules]:
  "\<And>R. 1 \<le> t xs \<Longrightarrow>  
    hn_refine (hn_ctxt (list_assn R) xs xs' * hn_ctxt R x x')
     (oappend x' xs')
     (hn_invalid (list_assn R) xs xs' * hn_invalid R x x') (list_assn R) ( PR_CONST (mop_append t) $  x $ xs)"
  unfolding autoref_tag_defs mop_append_def oappend_def
  unfolding hn_refine_def
  apply (auto simp: execute_return pure_def hn_ctxt_def invalid_assn_def relH_def top_assn_rule)
  apply(rule exI[where x=1] ) apply auto
  subgoal    
    by (metis mod_star_trueI pf) 
  subgoal using mod_starD by auto 
  subgoal using mod_starD by blast
  done


subsection \<open>Imperative Implementation\<close>

term Augmenting_Path_BFS.bfs2
               
context Impl_Succ begin

    abbreviation "init_state_time == 3 + rbt_insert_logN 1 + rbt_insert_logN 1"


    definition "set_pick_time = (10::nat)"

    lemma [simp]: "set_pick_time > (0::nat)" unfolding set_pick_time_def by auto

definition "map_lookup_time vcf = rbt_search_time_logN (1 +  vcf) + 1" 
lemma [simp]: "map_lookup_time cf > 0" unfolding map_lookup_time_def by simp
 
 



definition init_state :: "nat \<Rightarrow> (bool \<times> (nat \<Rightarrow> nat option) \<times> nat set \<times> nat set \<times> nat) nrest" where
  "init_state src = do {
        m \<leftarrow> mop_map_empty (1::nat);
        m \<leftarrow> mop_map_update (\<lambda>M. rbt_insert_logN (sizeM1' M)) m src src;
        C \<leftarrow> mop_set_empty (1::nat);
        C \<leftarrow> mop_set_insert (\<lambda>_. rbt_insert_logN (card C + 1)) src C;
        N \<leftarrow> mop_set_empty (1::nat);
        RETURNT (False, m, C, N, 0::nat)
      }"
    
    term mop_set_insert
    definition "set_insert_time vcf = rbt_insert_logN (vcf + 1)"
    definition "set_delete_time vcf = rbt_delete_time_logN (vcf + 1)"
    definition "map_dom_member_time vcf = rbt_search_time_logN (1 + vcf) + 1"
    definition "map_update_time vcf = rbt_insert_logN (1 + vcf)" 
    definition "set_isempty_time = (10::nat)"
    definition "set_empty_time = (10::nat)"
    definition "list_append_time = (1::nat)"

    abbreviation "bfs2 cf SS IS s t == Augmenting_Path_BFS.bfs2 cf
                       (set_insert_time (card (Graph.V cf))) (map_dom_member_time (card (Graph.V cf)))  (set_delete_time (card (Graph.V cf))) (map_update_time (card (Graph.V cf)))
                      set_pick_time list_append_time (map_lookup_time (card (Graph.V cf))) set_empty_time set_isempty_time SS IS s t"


    definition op_bfs :: "'ga \<Rightarrow> node \<Rightarrow> node \<Rightarrow> path option nrest"
      where [simp]: "op_bfs c s t \<equiv> bfs2 (absG c) (succ c) init_state s t"
  
   (* lemma pat_op_dfs[pat_rules]: 
      "bfs2$(absG$c)$(succ$c)$s$t \<equiv> UNPROTECT op_bfs$c$s$t" by simp 
  *)
    sepref_register "PR_CONST op_bfs" 
      :: "'ig \<Rightarrow> node \<Rightarrow> node \<Rightarrow> path option nrest"  


    type_synonym ibfs_state 
      = "bool \<times> (node \<rightharpoonup> node) \<times> node set \<times> node set \<times> nat"
 


    lemma P: "Pre_BFS_Impl set_pick_time" unfolding Pre_BFS_Impl_def by simp
 

  
  
  lemma init_state_correct: "init_state src \<le> SPECT [ (False,[src\<mapsto>src],{src},{},0::nat) \<mapsto> init_state_time ]"
    unfolding init_state_def   
    apply(rule T_specifies_I) unfolding mop_map_empty_def mop_map_update_def mop_set_empty_def
        mop_set_insert_def
    by(vcg' \<open>clarsimp\<close>  ) 




    sepref_register init_state :: "node \<Rightarrow> ibfs_state nrest"

    schematic_goal init_state_impl:
      fixes src :: nat
      notes [id_rules] = 
        itypeI[Pure.of src "TYPE(nat)"]
      shows "hn_refine (hn_val nat_rel src srci) 
        (?c::?'c Heap) ?\<Gamma>' ?R (init_state src)"
      using [[id_debug, goals_limit = 1]]
      unfolding init_state_def   
      apply sepref 
      done
      concrete_definition (in -) init_state_impl uses Impl_Succ.init_state_impl

      thm init_state_impl_def

      lemmas [sepref_fr_rules] = init_state_impl.refine[OF this_loc,to_hfref]
 


      thm Pre_BFS_Impl.pre_bfs2_def 
lemma PP: "Pre_BFS_Impl set_pick_time" by(simp add: Pre_BFS_Impl_def)


lemma (in -) hn_refine_Some[sepref_fr_rules]: " hn_refine (hn_val Id s' s)
           (ureturn (Some s))
       (hn_val Id s' s)
       (pure Id) (RETURNT $ (Some $ s'))"
  unfolding hn_refine_def apply (auto simp:   mult.assoc  execute_ureturn pure_def hn_ctxt_def)
  by (auto simp: top_assn_rule zero_enat_def relH_def  elim: pureD )
 


 


declare rbt_search_time_logN_mono [intro]
declare rbt_insert_logN_mono [intro]
declare rbt_delete_time_logN_mono [intro]

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
      shows

  "hn_refine (
        hn_ctxt (isG) c ci 
      * hn_val nat_rel s si 
      * hn_val nat_rel t ti) (?c::?'c Heap) ?\<Gamma>' ?R (PR_CONST op_bfs c s t)"
      unfolding op_bfs_def PR_CONST_def      
      apply(subst Augmenting_Path_BFS.bfs2_def) apply(simp add: Augmenting_Path_BFS_def)
      unfolding Pre_BFS_Impl.pre_bfs2_def[OF PP]
      unfolding Pre_BFS_Impl.inner_loop_def[OF PP]  unfolding  extract_rpath_def nfoldliIE_def nfoldli_def 
      using [[id_debug, goals_limit = 2]]
      unfolding monadic_WHILE_aux Pre_BFS_Impl.loopguard_def[OF PP] 
      unfolding set_pick_time_def set_isempty_time_def set_delete_time_def map_dom_member_time_def
          map_update_time_def set_insert_time_def set_empty_time_def map_lookup_time_def list_append_time_def

  apply sepref_dbg_preproc
  apply sepref_dbg_cons_init
  apply sepref_dbg_id 
     apply sepref_dbg_monadify

     apply sepref_dbg_opt_init
                                        
  apply sepref_dbg_trans_keep 

  apply sepref_dbg_opt
  apply sepref_dbg_cons_solve \<comment> \<open>Frame rule, recovering the invalidated list 
    or pure elements, propagating recovery over the list structure\<close>
  apply sepref_dbg_cons_solve \<comment> \<open>Trivial frame rule\<close>
  apply sepref_dbg_constraints
      done
    
    concrete_definition (in -) bfs_impl uses Impl_Succ.bfs_impl
      \<comment> \<open>Extract generated implementation into constant\<close>
    prepare_code_thms (in -) bfs_impl_def
   
    lemmas bfs_impl_fr_rule = bfs_impl.refine[OF this_loc,to_hfref]  
  
  end

(*  export_code bfs_impl checking SML_imp *)

end