theory IICF_DArray_List  
  imports "../Intf/IICF_List" "SepLogicTime_RBTreeBasic.DynamicArray2"
begin

section "Implementing List Interface with DynamicArrays"


lemma new[sepref_fr_rules]: "12 \<le> n \<Longrightarrow> 
      hn_refine emp dyn_array_new emp dyn_array (PR_CONST (mop_empty_list n))"
  unfolding mop_empty_list_def autoref_tag_defs
  apply (rule extract_cost_otherway[OF _ dyn_array_new_rule, where Cost_lb=7 and F=emp])
    apply auto
  apply(rule ent_ex_postI[where x="[]"]) by simp




(* concrete and abstract operations have to have the same order of parameters *)
                         
lemma push[sepref_fr_rules]:  "23  \<le> t xs' ==> hn_refine (hn_ctxt dyn_array xs' p * hn_ctxt (pure Id) x' x) (push_array x p)
         (hn_invalid dyn_array xs' p * hn_ctxt (pure Id) x' x)  
             dyn_array (PR_CONST (mop_push_list t) $  x' $   xs')" 
  unfolding mop_push_list_def autoref_tag_defs
  apply (rule extract_cost_otherway[OF _ push_array_rule, where F="hn_val Id x' x * hn_invalid dyn_array xs' p" ])
    apply(simp add: mult.assoc) apply rotater apply rotater apply rotater apply (taker) apply (rule isolate_first)
  apply (simp add: gr_def hn_ctxt_def)   apply(rule invalidate_clone) apply rotater apply(rule entails_triv)
  apply auto
  apply(rule ent_ex_postI[where x="xs' @ [x]"]) apply (auto simp: hn_ctxt_def pure_def)
  apply(simp only: mult.assoc)
  apply rotatel apply (rule match_first) apply rotatel apply rotater  
  by (auto simp: invalid_assn_def)   


subsection "get parametricity in element for 'free'"
thm param
term REST
lemma [param]: "(REST,REST) \<in> (A \<rightarrow> Id) \<rightarrow> \<langle>A\<rangle>nrest_rel" sorry           (* ? gilt das ? *)                                                                
lemma pl_param: "(PR_CONST (mop_push_list n),PR_CONST (mop_push_list n)) \<in> A \<rightarrow> \<langle>A\<rangle>list_rel \<rightarrow> \<langle>\<langle>A\<rangle>list_rel\<rangle>nrest_rel"
  unfolding mop_push_list_def autoref_tag_defs apply parametricity sorry


thm pl_param[to_fref]
definition "da_assn R \<equiv> hr_comp dyn_array (\<langle>the_pure R\<rangle>list_rel)"

declare da_assn_def[symmetric, fcomp_norm_unfold]
(* thm push[FCOMP pl_param] *)




subsection "casting functions by tags"

thm push[to_hfref,to_hnr]
thm push[to_hfref]
thm new[to_hfref,to_hnr]
thm new[to_hfref]


subsection "synthesize some programs"

sepref_definition test is "uncurry0 (do { xs \<leftarrow>mop_empty_list 7;  mop_push_list (\<lambda>_. 10) (0::nat) xs })" :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a dyn_array"
  apply sepref_dbg_keep                   
  apply sepref_dbg_trans_keep                  
        apply sepref_dbg_trans_step_keep oops

sepref_definition test is "uncurry0 (do { xs \<leftarrow>mop_empty_list 12;  mop_push_list (\<lambda>_. 23) (0::nat) xs })" :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a dyn_array"
  apply sepref_dbg_keep   done
 



subsection "combined with relation"


definition "dyn_array_assn R xs' p = (\<exists>\<^sub>Axs. dyn_array xs p * list_assn R xs' xs)"

lemma [simp]: "dyn_array_assn R [] r = dyn_array [] r"
  unfolding dyn_array_assn_def apply (rule ent_iffI)
  subgoal by (simp add: entails_def)
  subgoal apply(rule ent_ex_postI[where x="[]"]) by simp
  done

thm new

(*

lemma  "hn_refine emp dyn_array_new emp (dyn_array_assn R) (mop_empty_list)"
  unfolding mop_empty_list_def
  apply (rule extract_cost_otherway[OF _ dyn_array_new_rule, where Cost_lb=7 and F=emp])
    apply auto
  apply(rule ent_ex_postI[where x="[]"]) by simp

                         
lemma   "hn_refine (dyn_array_assn R xs' p * hn_ctxt R x' x) (push_array x p)
         (hn_invalid (dyn_array_assn R) xs' p * hn_invalid R x' x)  
             (dyn_array_assn R) (mop_push_list xs' x')"
  unfolding mop_push_list_def
  apply (rule extract_cost_otherway[OF _ push_array_rule, where Cost_lb=23 ]) 
  unfolding dyn_array_assn_def  apply (simp add: mult.assoc) apply(rule ent_ex_preI)
  apply(rule match_first) 
  apply(rule ent_ex_postI[where x="[]"]) sorry *)
end