section "Implementing List Interface with DynamicArrays"
theory IICF_DArray_List  
  imports "../Intf/IICF_List" "SepLogicTime_RBTreeBasic.DynamicArray2"
begin


definition "da_assn R \<equiv> hr_comp dyn_array (\<langle>the_pure R\<rangle>list_rel)"

lemma hn_refine_ex: "(\<And>b. hn_refine (R b) c Q RR a) \<Longrightarrow> hn_refine (\<exists>\<^sub>Ab. R b) c Q RR a" 
   unfolding hn_refine_def mod_ex_dist by blast

context 
  notes [intro!] = hfrefb_to_hoare_triple
  notes [simp] = pure_def hn_ctxt_def invalid_assn_def uncurry_t_def
                noparam_t_def oneparam_t_def
begin  

  lemma mop_list_empty_rule_aux:
    "(uncurry0 dyn_array_new, noparam_t mop_empty_list)
         \<in> [\<lambda>_. True, \<lambda>_. 12]\<^sub>b unit_assn\<^sup>k \<rightarrow> (da_assn (R))"
    by (sep_auto heap: dyn_array_new_rule
                simp: mop_empty_list_def da_assn_def hr_comp_def)

  lemmas mop_list_empty_rule[sepref_fr_rules] = mop_list_empty_rule_aux[hfb_to_hnr]


  lemma models_impl_elem_in_is_pure:
    "is_pure R \<Longrightarrow> h1 \<Turnstile> R aa a \<Longrightarrow> (a, aa) \<in> the_pure R"
    by (metis pure_assn_rule pure_def pure_the_pure)

  lemma mop_list_push_rule_aux: "(uncurry push_array, uncurry_t mop_push_list)
       \<in> [\<lambda>_. CONSTRAINT is_pure R, \<lambda>_. 23]\<^sub>b (R\<^sup>k *\<^sub>a (da_assn (R))\<^sup>d) \<rightarrow> (da_assn (R))"
    supply param_append' = param_append[THEN fun_relD, THEN fun_relD]
    by (sep_auto heap: push_array_rule dest!: mod_starD
                    simp:  da_assn_def hr_comp_def  mop_push_list_def
                    intro!: models_impl_elem_in_is_pure param_append')
    
  lemmas mop_list_push_rule[sepref_fr_rules] = mop_list_push_rule_aux[hfb_to_hnr]


end 

lemma dyn_da: "dyn_array = da_assn (pure Id)" unfolding da_assn_def by auto

declare da_assn_def[symmetric, fcomp_norm_unfold]

subsection "casting functions by tags"

thm mop_list_empty_rule[to_hfref,to_hnr]
thm mop_list_empty_rule[to_hfref]
thm mop_list_push_rule[to_hfref,to_hnr]
thm mop_list_push_rule[to_hfref]


subsection "synthesize some programs"

experiment
begin

sepref_definition test is "uncurry0 (do { xs \<leftarrow>mop_empty_list (\<lambda>_. 7);  mop_push_list (\<lambda>_. 10) (0::nat) xs })" :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a da_assn (pure Id)"
  apply sepref_dbg_keep                   
  apply sepref_dbg_trans_keep                  
        apply sepref_dbg_trans_step_keep oops

sepref_definition test is "uncurry0 (do { xs \<leftarrow>mop_empty_list (\<lambda>_. 12);  mop_push_list (\<lambda>_. 23) (0::nat) xs })" :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a da_assn (pure Id)"
  apply sepref_dbg_keep   done

end



subsection "combined with relation"


definition "dyn_array_assn R xs' p = (\<exists>\<^sub>Axs. dyn_array xs p * list_assn R xs' xs)"

lemma [simp]: "dyn_array_assn R [] r = dyn_array [] r"
  unfolding dyn_array_assn_def apply (rule ent_iffI)
  subgoal by (simp add: entails_def)
  subgoal apply(rule ent_ex_postI[where x="[]"]) by simp
  done

   
end