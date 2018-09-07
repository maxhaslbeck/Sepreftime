theory Example_Automatic
  imports "Refine_Imperative_HOL/Sepref" "SepLogicTime_RBTreeBasic.RBTree_Impl"
    Set_Impl2  
begin


(*
lemma set_mem_hnr_abs[sepref_fr_rules]:
  "hn_refine (hn_ctxt rbt_set_assn S p * hn_val Id x x')
     (rbt_search (x'::nat) p)
     (hn_ctxt rbt_set_assn S p * hn_val Id x x') Y' ( (set_mem_SPEC $ x $ S))"
  sorry *)
 
definition rd_impl1 :: "nat list \<Rightarrow> (nat list) nrest" where
  "rd_impl1 as = do {
          ys \<leftarrow> RETURNT [];
          S \<leftarrow> mop_empty_set 1;
          zs \<leftarrow> RETURNT as;
          (zs,ys,S) \<leftarrow> whileT (\<lambda>(xs,ys,S). length xs > 0)
            (\<lambda>(xs,ys,S). do {                          
                          ASSERT (length xs > 0);
                          ASSERT (length xs + length ys \<le> length as);
                          ASSERT (card S \<le> length ys);
                          x \<leftarrow> RETURNT (hd xs);
                          xs \<leftarrow> RETURNT (tl xs);
                          b \<leftarrow> mop_mem_set (\<lambda>S. rbt_search_time_logN (length as + 1) + 1) x S;
                          (if b
  then  RETURNT (xs,ys,S)
  else do { S \<leftarrow> mop_insert_set (\<lambda>S. rbt_insert_logN (length as + 1)) x S;
            ys \<leftarrow> RETURNT (x#ys);  
            RETURNT (xs,ys,S)
  } ) }) (zs,ys,S);
          RETURNT ys
      }"

(* library *) 
 
 
lemma hn_refine_Zero[sepref_fr_rules]: " hn_refine emp
           (ureturn (0::nat)) emp
       (pure Id) (RETURNT $ (0::nat))"
  unfolding hn_refine_def apply (auto simp:   mult.assoc  execute_ureturn pure_def hn_ctxt_def)
   apply(rule exI[where x=0]) apply (auto simp: zero_enat_def relH_def )      
    using models_in_range top_assn_rule  
    by (metis (full_types) mod_false  )  
  

lemma hn_refine_length[sepref_fr_rules]: " hn_refine (hn_val Id xs' xs)
           (ureturn (length xs))
       (hn_val Id xs' xs)
       (pure Id) (RETURNT $ (length $ xs'))"
  unfolding hn_refine_def apply (auto simp:   mult.assoc  execute_ureturn pure_def hn_ctxt_def)
   apply(rule exI[where x=0]) by (auto simp: top_assn_rule zero_enat_def relH_def elim: pureD  )      
 

lemma hn_refine_hd[sepref_fr_rules]: " hn_refine (hn_val Id s' s)
           (ureturn (hd s))
       (hn_val Id s' s)
       (pure Id) (RETURNT $ (hd $ s'))"
  unfolding hn_refine_def apply (auto simp:   mult.assoc  execute_ureturn pure_def hn_ctxt_def)
     by (auto simp: top_assn_rule zero_enat_def relH_def  elim: pureD )      
 

lemma hn_refine_tl[sepref_fr_rules]: " hn_refine (hn_val Id s' s)
           (ureturn (tl s))
       (hn_val Id s' s)
       (pure Id) (RETURNT $ (tl $ s'))"
  unfolding hn_refine_def apply (auto simp:   mult.assoc  execute_ureturn pure_def hn_ctxt_def)
     by (auto simp: top_assn_rule zero_enat_def relH_def  elim: pureD )      




(* synthesize *) 

context 
  fixes as::"nat list"
  notes [[sepref_register_adhoc as]]
  notes [sepref_import_param] = IdI[of as] 
begin

declare rbt_search_time_logN_mono [intro]
declare rbt_insert_logN_mono [intro]

sepref_definition test is "uncurry0 (rd_impl1 as)" :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a list_assn nat_assn"
  unfolding rd_impl1_def
  apply sepref 
  done
print_theorems
term test
thm test_def 
thm test.refine[to_hnr] 

(*

schematic_goal synth_rd: "hn_refine emp (?C::?'a Heap) ?\<Gamma>' ?R (rd_impl1 as)" using [[goals_limit = 3]]
  unfolding rd_impl1_def

  apply sepref_dbg_preproc
  apply sepref_dbg_cons_init
  apply sepref_dbg_id 
     apply sepref_dbg_monadify

     apply sepref_dbg_opt_init
                                              
  apply sepref_dbg_trans_step+ 

  apply sepref_dbg_opt
  apply sepref_dbg_cons_solve \<comment> \<open>Frame rule, recovering the invalidated list 
    or pure elements, propagating recovery over the list structure\<close>
  apply sepref_dbg_cons_solve \<comment> \<open>Trivial frame rule\<close>
  apply sepref_dbg_constraints
  done

thm synth_rd[to_hfref]


concrete_definition rd_impl uses synth_rd is "hn_refine _ (?c ) _ _ _"

thm rd_impl_def
term rd_impl
*)
end


end