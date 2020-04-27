theory Remdups_Impl 
  imports Remdups
    Flatten_Currencies
   "Imperative_HOL_Time.SLTC"  
  "SeprefTime.Sepref"
    "SeprefTime.IICF_Rbt_Set"  
    "SeprefTime.IICF_DArray_List" 
begin


section  \<open>Flatten mops\<close>


lemma flatCurrs_mop_set_insert:
  "(\<And>x. g x = f x ()) \<Longrightarrow> flatCurrs (Remdups.mop_set_insert f x C) = mop_set_insert g x C"
  unfolding Remdups.mop_set_insert_def mop_set_insert_def by(simp add: flatCurrs_SPECT)
lemma flatCurrs_mop_set_member:
  "(\<And>x. g x = f x ()) \<Longrightarrow> flatCurrs (Remdups.mop_set_member f x C) = mop_set_member g x C"
  unfolding Remdups.mop_set_member_def mop_set_member_def by(simp add: flatCurrs_SPECT)
lemma flatCurrs_mop_push_list:
  "(\<And>x. g x = f x ()) \<Longrightarrow> flatCurrs (Remdups.mop_push_list f x xs) = mop_push_list g x xs"
  unfolding Remdups.mop_push_list_def mop_push_list_def by(simp add: flatCurrs_SPECT)
lemma flatCurrs_mop_set_empty:
  "(\<And>x. g x = f x ()) \<Longrightarrow> flatCurrs (Remdups.mop_set_empty f    ) = mop_set_empty g    "
  unfolding Remdups.mop_set_empty_def mop_set_empty_def by(simp add: flatCurrs_SPECT)
lemma flatCurrs_mop_empty_list:
  "(\<And>x. g x = f x ()) \<Longrightarrow> flatCurrs (Remdups.mop_empty_list f    ) = mop_empty_list g    "
  unfolding Remdups.mop_empty_list_def mop_empty_list_def by(simp add: flatCurrs_SPECT)

lemmas mops = flatCurrs_mop_set_insert flatCurrs_mop_set_member flatCurrs_mop_push_list
            flatCurrs_mop_set_empty flatCurrs_mop_empty_list
            flatCurrs_RETURNT

section  \<open>Flatten Remdups\<close>

lemma flatted_rd_impl3: "flatCurrs (rd_impl3 as) = do {
  ys \<leftarrow> mop_empty_list (\<lambda>_. 12);
  S \<leftarrow> mop_set_empty 1;
  zs \<leftarrow> RETURNT as;
  (zs,ys,S) \<leftarrow> whileT  (\<lambda>(xs,ys,S). length xs > 0) (\<lambda>(xs,ys,S). do {                          
    ASSERT (length xs > 0);
    x \<leftarrow> RETURNT (hd xs);
    xs \<leftarrow> RETURNT (tl xs);
    ASSERT (card S \<le> length as);
    b \<leftarrow> mop_set_member (\<lambda>(x,S). rbt_search_time_logN (card S + 1) + 1) x S;
    if b then
      RETURNT (xs,ys,S)
    else do {
      ASSERT (card S \<le> length as);
      S \<leftarrow> mop_set_insert (\<lambda>(x,S). rbt_insert_logN (card S + 1)) x S;
      ys \<leftarrow> mop_push_list (\<lambda>_. 23) x ys;  
      RETURNT (xs,ys,S)
    } 
  }) (zs,ys,S);
  RETURNT ys
  }"
  unfolding rd_impl3_def 
  apply(rule flatCurrs_bindTI)
   apply(rule mops) apply (simp add: one_enat_def)  
  apply(rule flatCurrs_bindTI)
   apply(rule mops) apply (simp add: one_enat_def)
  apply(rule flatCurrs_bindTI)
   apply(rule mops)
  apply(rule flatCurrs_bindTI)
  subgoal
    apply(rule flatCurrs_whileT) 
    subgoal
      by (refine_mono)       
    subgoal
      by (refine_mono)  
  apply(rule flatCurrs_prod)
  apply(rule flatCurrs_prod) 
   apply(rule flatCurrs_bindTI)
   apply(rule flatCurrs_ASSERT)
   apply(rule flatCurrs_bindTI)
   apply(rule mops)
    apply (simp add: one_enat_def)
   apply(rule flatCurrs_ASSERT flatCurrs_bindTI)+
   apply(rule mops)
    apply (auto simp:  )[1] 
   apply(rule flatCurrs_If)
   apply(rule mops)
   apply(rule flatCurrs_ASSERT flatCurrs_bindTI)+
   apply(rule mops)
    apply (auto simp: one_enat_def)[1] 
   apply(rule flatCurrs_ASSERT flatCurrs_bindTI)+
   apply(rule mops)
    apply (auto simp: one_enat_def  numeral_eq_enat)[1] 
    apply(rule mops) done
  apply(rule flatCurrs_prod)
  apply(rule flatCurrs_prod)
  apply(rule mops)
  done



(* library *)  
lemma hn_refine_Zero: " hn_refine emp
           (ureturn (0::nat)) emp
       (pure Id) (APP RETURNT   (0::nat))"
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

sepref_definition remdups_impl is "uncurry0 (flatCurrs (rd_impl3 as) )" :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a da_assn id_assn"
  unfolding flatted_rd_impl3 whileIET_def    
  by sepref

term remdups_impl
thm remdups_impl_def 
thm remdups_impl.refine[to_hnr]

thm hnr_refine[OF flatCurrs_mono[OF rd_impl3_correct] remdups_impl.refine[to_hnr]]

lemma Tada: "hn_refine emp local.remdups_impl emp (da_assn id_assn)
 (SPECT (emb (\<lambda>ys. set as = set ys \<and> distinct ys) (enat (TT_time (length as)))))"
proof -
  have "hn_refine emp local.remdups_impl emp (da_assn id_assn)
 (flatCurrs (aSPECT (AbstractSepreftime.emb (\<lambda>ys. set as = set ys \<and> distinct ys) (\<lambda>x. enat (TT_time (length as))))))"
    apply(fact hnr_refine[OF flatCurrs_mono[OF rd_impl3_correct] remdups_impl.refine[to_hnr]]) done
  moreover have "(flatCurrs (aSPECT (AbstractSepreftime.emb (\<lambda>ys. set as = set ys \<and> distinct ys) (\<lambda>x. enat (TT_time (length as))))))
      = 
 (SPECT (emb (\<lambda>ys. set as = set ys \<and> distinct ys) (enat (TT_time (length as)))))"
    unfolding flatCurrs_def by (auto simp add: AbstractSepreftime.emb'_def emb'_def)
  ultimately show ?thesis
    by simp
qed

thm extract_cost_ub[OF Tada, where Cost_ub="TT_time (length as)", simplified in_ran_emb_special_case,   simplified ]

lemma remdups_rule: "<$ (TT_time (length as))> 
          remdups_impl 
        <\<lambda>r. \<exists>\<^sub>Ara. da_assn id_assn ra r * \<up> (set as = set ra \<and> distinct ra)>\<^sub>t"
  using  extract_cost_ub[OF Tada, where Cost_ub="TT_time (length as)", simplified in_ran_emb_special_case,   simplified ]
  by auto

end 

end