theory Example_Automatic
  imports "Refine_Imperative_HOL/Sepref" "SepLogicTime_RBTreeBasic.RBTree_Impl"
    Set_Impl2 Example_DynamicArray RefineMonadicVCG
begin


(*
lemma set_mem_hnr_abs[sepref_fr_rules]:
  "hn_refine (hn_ctxt rbt_set_assn S p * hn_val Id x x')
     (rbt_search (x'::nat) p)
     (hn_ctxt rbt_set_assn S p * hn_val Id x x') Y' ( (set_mem_SPEC $ x $ S))"
  sorry *)
        
term remdups

definition rd_impl1 :: "nat list \<Rightarrow> (nat list) nrest" where
"rd_impl1 as = do {
  ys \<leftarrow> mop_empty_list 12;
  S \<leftarrow> mop_empty_set 1;
  zs \<leftarrow> RETURNT as;
  (zs,ys,S) \<leftarrow> whileT (\<lambda>(xs,ys,S). length xs > 0) (\<lambda>(xs,ys,S). do {                          
    ASSERT (length xs > 0);
    ASSERT (length xs + length ys \<le> length as);
    ASSERT (card S \<le> length ys);
    x \<leftarrow> RETURNT (hd xs);
    xs \<leftarrow> RETURNT (tl xs);
    b \<leftarrow> mop_mem_set (\<lambda>S. rbt_search_time_logN (length as + 1) + 1) x S;
    if b then
      RETURNT (xs,ys,S)
    else do {
      S \<leftarrow> mop_insert_set (\<lambda>S. rbt_insert_logN (length as + 1)) x S;
      ys \<leftarrow> mop_push_list (\<lambda>_. 23) x ys;  
      RETURNT (xs,ys,S)
    } 
  }) (zs,ys,S);
  RETURNT ys
  }"

term emb

definition body_time :: "nat \<Rightarrow> nat" where 
  "body_time n = 60 + rbt_search_time_logN (n+1) + rbt_insert_logN (n+1)"

definition "remdups_time (n::nat) = n * body_time n + 20"



lemma enat_neq_Z_iff[simp]: "enat x \<noteq> 0 \<longleftrightarrow> x\<noteq>0"
  by (auto simp: zero_enat_def)

lemma rd_impl1_correct: "rd_impl1 as \<le> REST (emb (\<lambda>ys. set as = set ys \<and> distinct ys)
                   ( remdups_time (length as) ))"
  unfolding rd_impl1_def mop_empty_list_def mop_empty_set_def mop_mem_set_def mop_insert_set_def mop_push_list_def
  (*apply(subst whileTI_def[symmetric, where I="I"
                                    and R="R"])*)
  apply(rule T_specifies_I)
  apply (vcg' \<open>simp\<close>)

  apply (rule T_conseq4)
   apply (rule whileT_rule'''[OF refl, where I="(\<lambda>(xs,ys,S). if (\<exists>zs. as = zs@xs \<and> S = set ys \<and> distinct ys \<and> set zs = set ys) 
                then Some (length xs * body_time (length as)) else None)"])
  supply [simp] = neq_Nil_conv distinct_length_le card_length
     apply (vcg' \<open>auto simp: body_time_def remdups_time_def \<close> rules: TrueI)
  done
 



find_theorems "Some _ \<le> TTT _ (REST _)"


thm whileT_rule''

lemma "remdups_time \<in> \<Theta>(\<lambda>n. n * ln n)"
  unfolding remdups_time_def body_time_def
  by auto2 



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



lemma ran_emb': "c \<in> ran (emb' Q t) \<longleftrightarrow> (\<exists>s'. Q s' \<and> t s' = c)"
  by(auto simp: emb'_def ran_def)

lemma ran_emb_conv: "Ex Q \<Longrightarrow>  ran (emb Q t) = {t}"
  by (auto simp: ran_emb')

lemma in_ran_emb_special_case: "c\<in>ran (emb Q t) \<Longrightarrow> c\<le>t"
  apply (cases "Ex Q")
   apply (auto simp: ran_emb_conv)
  apply (auto simp: emb'_def)
  done

lemma dom_emb'_eq[simp]: "dom (emb' Q f) = Collect Q"
  by(auto simp: emb'_def split: if_splits)

(* synthesize *) 

context 
  fixes as::"nat list"
  notes [[sepref_register_adhoc as]]
  notes [sepref_import_param] = IdI[of as] 
begin

declare rbt_search_time_logN_mono [intro]
declare rbt_insert_logN_mono [intro]




sepref_definition remdups_impl is "uncurry0 (rd_impl1 as)" :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a dyn_array"
  unfolding rd_impl1_def
  apply sepref_dbg_keep 
  done
print_theorems
term remdups_impl
thm remdups_impl_def 
thm remdups_impl.refine[to_hnr]
thm  hnr_refine[OF rd_impl1_correct  remdups_impl.refine[to_hnr],to_hfref] 
thm extract_cost_ub[OF hnr_refine[OF rd_impl1_correct  remdups_impl.refine[to_hnr]], where Cost_ub="remdups_time (length as)", simplified in_ran_emb_special_case,   simplified ]


lemma "<$ (remdups_time (length as))> 
          remdups_impl 
        <\<lambda>r. \<exists>\<^sub>Ara. dyn_array ra r * \<up> (set as = set ra \<and> distinct ra)>\<^sub>t"
  using  extract_cost_ub[OF hnr_refine[OF rd_impl1_correct  remdups_impl.refine[to_hnr]], where Cost_ub="remdups_time (length as)", simplified in_ran_emb_special_case,   simplified ]
  by auto
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