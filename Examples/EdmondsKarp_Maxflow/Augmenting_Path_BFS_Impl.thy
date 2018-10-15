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


lemma A: "Augmenting_Path_BFS set_pick_time map_lookup_time"
  unfolding Augmenting_Path_BFS_def by simp
    thm Augmenting_Path_BFS.bfs2_def




definition init_state :: "nat \<Rightarrow> (bool \<times> (nat \<Rightarrow> nat option) \<times> nat set \<times> nat set \<times> nat) nrest" where
  "init_state src = do {
        m \<leftarrow> mop_map_empty (1::nat);
        m \<leftarrow> mop_map_update (\<lambda>M. rbt_insert_logN (sizeM1' M)) m src src;
        C \<leftarrow> mop_set_empty (1::nat);
        C \<leftarrow> mop_set_insert (\<lambda>_. rbt_insert_logN (card C + 1)) src C;
        N \<leftarrow> mop_set_empty (1::nat);
        RETURNT (False, m, C, N, 0::nat)
      }"

    abbreviation "bfs2 cf SS IS s t == Augmenting_Path_BFS.bfs2 cf
                       set_insert_time map_dom_member_time  set_delete_time  map_update_time
                      set_pick_time list_append_time map_lookup_time set_empty_time set_isempty_time SS IS s t"

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
 

  
  
  lemma "init_state src \<le> SPECT [ (False,[src\<mapsto>src],{src},{},0::nat) \<mapsto> init_state_time ]"
    unfolding init_state_def   
    apply(rule T_specifies_I) unfolding mop_map_empty_def mop_map_update_def mop_set_empty_def
        mop_set_insert_def
      apply(vcg' \<open>clarsimp\<close>  ) by (simp add: sizeM1'_def) 




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

lemma (in -) hn_refine_Some_list[sepref_fr_rules]: " hn_refine (hn_ctxt (list_assn S) s' s)
           (ureturn (Some s))
       (hn_invalid (list_assn S) s' s)
       ((option_assn (list_assn S))) (RETURNT $ (Some $ s'))" (*
  unfolding hn_refine_def apply (auto simp:   mult.assoc  execute_ureturn pure_def hn_ctxt_def)
  apply (auto simp: top_assn_rule zero_enat_def relH_def  elim: pureD )    
  by (simp add: mod_star_trueI) *) sorry

term mop_append

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
"hn_refine (hn_ctxt isG c ci * hn_val nat_rel s si * hn_val nat_rel t ti) ?c ?\<Gamma>' ?R
     (if s = t then RETURNT (Some [])
      else (init_state s \<bind>
            (\<lambda>sa. whileT (\<lambda>(f, PRED, C, N, d). f = False \<and> C \<noteq> {})
                    (\<lambda>(f, PRED, C, N, d).
                        ASSERT (C \<noteq> {}) \<bind>
                        (\<lambda>_. mop_set_pick (Pre_BFS_Impl.setpickt set_pick_time) C \<bind>
                              (\<lambda>v. mop_set_del (Pre_BFS_Impl.setdelt set_delete_time) C v \<bind>
                                    (\<lambda>C. ASSERT (v \<in> Graph.V (absG c)) \<bind>
                                          (\<lambda>_. succ c v \<bind>
                                                (\<lambda>sl. RECT (\<lambda>D (l, s).
case l of [] \<Rightarrow> RETURNT s
| x # ls \<Rightarrow>
    if case s of (f, PRED, N) \<Rightarrow> \<not> f
    then (case s of
          (f, PRED, N) \<Rightarrow>
            mop_map_dom_member (\<lambda>_. map_dom_member_time) PRED x \<bind>
            (\<lambda>b. if b then SPECT [(f, PRED, N) \<mapsto> enat 1]
                  else mop_map_update (\<lambda>_. map_update_time) PRED x v \<bind>
                       (\<lambda>PRED.
                           ASSERT (x \<notin> N) \<bind>
                           (\<lambda>_. mop_set_insert (\<lambda>_. set_insert_time) x N \<bind> (\<lambda>N. RETURNT (x = t, PRED, N)))))) \<bind>
         (\<lambda>s. D (ls, s))
    else RETURNT s)
                                                        (sl, False, PRED, N) \<bind>
                                                       (\<lambda>(f, PRED, N).
                                                           if f then RETURNT (f, PRED, C, N, d + 1)
                                                           else ASSERT
 (case (f, PRED, C, N, d) of (f, PRED, C, N, d) \<Rightarrow> \<not> f \<and> nf_invar' (absG c) s t PRED C N d) \<bind>
(\<lambda>_. mop_set_isempty (\<lambda>_. set_isempty_time) C \<bind>
      (\<lambda>b. if b
            then RETURNT N \<bind> (\<lambda>C. mop_set_empty set_empty_time \<bind> (\<lambda>N. RETURNT (d + 1) \<bind> (\<lambda>d. RETURNT (f, PRED, C, N, d))))
            else RETURNT (f, PRED, C, N, d))))))))))
                    sa \<bind>
                   (\<lambda>(f, PRED, ttt, tt, d). if f then RETURNT (Some (d, PRED)) else RETURNT None))) \<bind>
           (\<lambda>br.  case br of None \<Rightarrow> RETURNT None
                  | Some (d, PRED) \<Rightarrow>  
                      (whileT (\<lambda>(v, p). v \<noteq> s)
                        (\<lambda>(v, p).
                            ASSERT (v \<in> dom PRED) \<bind>
                            (\<lambda>_. mop_map_lookup (\<lambda>_. map_lookup_time) PRED v \<bind> (\<lambda>u. 
                                   mop_append (\<lambda>_. list_append_time) (u, v) p \<bind>  (\<lambda>p.  
                                         RETURNT u \<bind> (\<lambda>v. RETURNT (v, p)))))
              )  
                        (t, ([]::((nat*nat) list))) \<bind>
                       (\<lambda>(d, p). RETURNT p)) \<bind>
                      (\<lambda>p. RETURNT (Some p))))   "

      using [[id_debug, goals_limit = 2]]
  apply sepref_dbg_preproc
  apply sepref_dbg_cons_init
  apply sepref_dbg_id_keep 
     apply sepref_dbg_monadify
     apply sepref_dbg_opt_init
                                              
  apply sepref_dbg_trans_step                 
  apply sepref_dbg_trans_step                 
  apply sepref_dbg_trans_step                 
  apply sepref_dbg_trans_step                 
  apply sepref_dbg_trans_step                 
  apply sepref_dbg_trans_step                 
  apply sepref_dbg_trans_step_keep oops                 
  apply sepref_dbg_trans_step                 
  apply sepref_dbg_trans_step                 
  apply sepref_dbg_trans_step                 
  apply sepref_dbg_trans_step                 
  apply sepref_dbg_trans_step                 
  apply sepref_dbg_trans_step                 
  apply sepref_dbg_trans_step                 
  apply sepref_dbg_trans_step                 
  apply sepref_dbg_trans_step                 
  apply sepref_dbg_trans_step                 
  apply sepref_dbg_trans_step                 
  apply sepref_dbg_trans_step                
  apply sepref_dbg_trans_step_keep
      oops
  "hn_refine (
        hn_ctxt (isG) c ci 
      * hn_val nat_rel s si 
      * hn_val nat_rel t ti) (?c::?'c Heap) ?\<Gamma>' ?R (PR_CONST op_bfs c s t)"
      unfolding op_bfs_def PR_CONST_def
      unfolding Augmenting_Path_BFS.bfs2_def[OF A] unfolding Pre_BFS_Impl.pre_bfs2_def[OF PP]
      unfolding Pre_BFS_Impl.inner_loop_def[OF PP]  unfolding  extract_rpath_def nfoldliIE_def nfoldli_def 
      using [[id_debug, goals_limit = 2]]

  apply sepref_dbg_preproc
  apply sepref_dbg_cons_init
  apply sepref_dbg_id_keep 
     apply sepref_dbg_monadify

     apply sepref_dbg_opt_init
                                              
  apply sepref_dbg_trans_step+ 

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

  export_code bfs_impl checking SML_imp

end