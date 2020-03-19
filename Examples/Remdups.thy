theory Remdups
  imports "../Refine_Imperative_HOL/Sepref"
    "SepLogicTime_RBTreeBasic.RBTree_Impl"
    "../Refine_Imperative_HOL/IICF/Impl/IICF_Rbt_Set"  
    "../Refine_Imperative_HOL/IICF/Impl/IICF_DArray_List" 
    "NREST.RefineMonadicVCG"
    "../Refine_Foreach"
begin
        

definition "rd_inv as \<equiv> (\<lambda>(xs,ys,S). (\<exists>zs. as = zs@xs \<and> S = set ys \<and> distinct ys \<and> set zs = set ys))"

definition body_time :: "nat \<Rightarrow> nat" where 
  "body_time n = 60 + rbt_search_time_logN (n+1) + rbt_insert_logN (n+1)"

definition "rd_ta as = (\<lambda>(xs,ys,S). length xs * body_time (length as))"

definition rd_impl1 :: "('a::{heap,linorder}) list \<Rightarrow> ('a list) nrest" where
"rd_impl1 as = do {
  ys \<leftarrow> mop_empty_list 12;
  S \<leftarrow> mop_set_empty 1;
  zs \<leftarrow> RETURNT as;
  (zs,ys,S) \<leftarrow> whileIET (rd_inv as) (rd_ta as) (\<lambda>(xs,ys,S). length xs > 0) (\<lambda>(xs,ys,S). do {                          
    ASSERT (length xs > 0);
    ASSERT (length xs + length ys \<le> length as);
    ASSERT (card S \<le> length ys);
    x \<leftarrow> RETURNT (hd xs);
    xs \<leftarrow> RETURNT (tl xs);
    b \<leftarrow> mop_set_member (\<lambda>_. rbt_search_time_logN (length as + 1) + 1) x S;
    if b then
      RETURNT (xs,ys,S)
    else do {
      S \<leftarrow> mop_set_insert (\<lambda>S. rbt_insert_logN (length as + 1)) x S;
      ys \<leftarrow> mop_push_list (\<lambda>_. 23) x ys;  
      RETURNT (xs,ys,S)
    } 
  }) (zs,ys,S);
  RETURNT ys
  }"
 
definition "remdups_time (n::nat) = n * body_time n + 20"

definition "remdups_spec as = REST (emb (\<lambda>ys. set as = set ys \<and> distinct ys)
                   ( remdups_time (length as) ))"

lemma enat_neq_Z_iff[simp]: "enat x \<noteq> 0 \<longleftrightarrow> x\<noteq>0"
  by (auto simp: zero_enat_def)

lemma rd_impl1_correct: "rd_impl1 as \<le> remdups_spec as"
  unfolding remdups_spec_def
  unfolding rd_impl1_def mop_empty_list_def mop_set_empty_def mop_set_member_def mop_set_insert_def mop_push_list_def
      rd_ta_def rd_inv_def
  apply(rule T_specifies_I)
  apply (vcg' \<open>simp\<close> )  
    unfolding Some_le_emb'_conv Some_eq_emb'_conv 
  supply [simp] = neq_Nil_conv distinct_length_le card_length
        apply (auto simp:
              Some_le_mm3_Some_conv
          body_time_def remdups_time_def)
    done
 
(*
definition rd_impl2 :: "('a::{heap,linorder}) list \<Rightarrow> ('a list) nrest" where
"rd_impl2 as = do {
  ys \<leftarrow> mop_empty_list 12;
  S \<leftarrow> mop_set_empty 1;
  zs \<leftarrow> RETURNT as;
  nfoldli as (\<lambda>_. True) (\<lambda>x (ys,S). do {    
    ASSERT (length ys \<le> length as);
    ASSERT (card S \<le> length ys);
    b \<leftarrow> mop_set_member (\<lambda>S. rbt_search_time_logN (length as + 1) + 1) x S;
    if b then
      RETURNT (ys,S)
    else do {
      S \<leftarrow> mop_set_insert (\<lambda>S. rbt_insert_logN (length as + 1)) x S;
      ys \<leftarrow> mop_push_list (\<lambda>_. 23) x ys;  
      RETURNT (ys,S)
    } 
  }) (ys,S);
  RETURNT ys
  }"



lemma rd_impl2_correct: "rd_impl2 as \<le> remdups_spec as"
  unfolding remdups_spec_def
  unfolding rd_impl2_def mop_empty_list_def mop_set_empty_def mop_set_member_def mop_set_insert_def mop_push_list_def
      rd_ta_def rd_inv_def
  apply(rule T_specifies_I)
  apply (vcg' \<open>simp\<close> )
  unfolding nfoldliIE_def[where E="2*rbt_search_time_logN (length as + 1) + 24"
                            and I="\<lambda>l1 l2 (bs,S). set l1 = S \<and> set bs = S \<and> distinct bs", symmetric] 
  apply(rule nfoldliIE_rule[  THEN T_specifies_rev, THEN T_conseq4]) 
  apply (vcg' \<open>simp\<close> rules: nfoldliIE_rule[  THEN T_specifies_rev, THEN T_conseq4])
  apply(rule T_specifies_I)
      apply (vcg' \<open>simp\<close>) 
    unfolding Some_le_emb'_conv Some_eq_emb'_conv 
  supply [simp] = neq_Nil_conv distinct_length_le card_length
        apply (a uto simp:
              Some_le_mm3_Some_conv
          body_time_def remdups_time_def)
  done
*)
 
lemma remdups_time_nln[asym_bound]: "remdups_time \<in> \<Theta>(\<lambda>n. n * ln n)"
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



(* synthesize *) 

context 
  fixes as::"('a::{heap,linorder,zero}) list"
  notes [[sepref_register_adhoc as]]
  notes [sepref_import_param] = IdI[of as] 
begin

declare rbt_search_time_logN_mono [intro]
declare rbt_insert_logN_mono [intro]

sepref_definition remdups_impl is "uncurry0 (rd_impl1 as)" :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a da_assn id_assn"
  unfolding rd_impl1_def whileIET_def    
  apply sepref_dbg_keep 
  done
print_theorems
term remdups_impl
thm remdups_impl_def 
thm remdups_impl.refine[to_hnr]
thm  hnr_refine[OF rd_impl1_correct  remdups_impl.refine[to_hnr],to_hfref] 
thm extract_cost_ub[OF hnr_refine[OF rd_impl1_correct[unfolded remdups_spec_def]  remdups_impl.refine[to_hnr]], where Cost_ub="remdups_time (length as)", simplified in_ran_emb_special_case,   simplified ]


lemma remdups_rule: "<$ (remdups_time (length as))> 
          remdups_impl 
        <\<lambda>r. \<exists>\<^sub>Ara. da_assn id_assn ra r * \<up> (set as = set ra \<and> distinct ra)>\<^sub>t"
  using  extract_cost_ub[OF hnr_refine[OF rd_impl1_correct[unfolded remdups_spec_def]  remdups_impl.refine[to_hnr]], where Cost_ub="remdups_time (length as)", simplified in_ran_emb_special_case,   simplified ]
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