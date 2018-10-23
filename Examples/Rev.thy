theory Rev
  imports "../Refine_Imperative_HOL/Sepref" 
 "../RefineMonadicVCG"
begin


context
  fixes t ::  "'c list \<Rightarrow> nat"
begin

  definition "mop_append x xs = SPECT [ (x#xs) \<mapsto> t xs]"

  lemma progress_mop_append[progress_rules]: "t xs > 0 \<Longrightarrow> progress (mop_append x xs)"
      unfolding mop_append_def by (progress\<open>simp add:   zero_enat_def\<close>) 

  lemma mop_append: "tt \<le> TTT Q (SPECT [ (x#xs) \<mapsto> t xs]) \<Longrightarrow> tt
           \<le> TTT Q (mop_append x xs)" unfolding mop_append_def by simp

  sepref_register "mop_append" 
end



definition myfun :: "nat list \<Rightarrow> nat list \<Rightarrow> nat list nrest" where
      "myfun as bs = RECT (\<lambda>fw (as,bs). (case as of [] \<Rightarrow> RETURNT bs
                  | a#as \<Rightarrow> fw (as,a#bs) )) (as,bs)"



lemma myfun_simps:
  "myfun [] bs           = RETURNT bs"
  "myfun (a#as) bs        = myfun as (a#bs)" 
  unfolding myfun_def by (subst RECT_unfold, refine_mono, auto)+


definition myfun2 :: "nat \<Rightarrow> nat list \<Rightarrow> nat list nrest" where
      "myfun2 n bs = RECT (\<lambda>fw (n,bs). (if n = 0 then RETURNT bs
                  else do {
                      bs'\<leftarrow> mop_append (%_. 1) 0 bs;
                      fw (n-1,bs') } )) (n,bs)"
 

lemma myfun2_simps:
  "myfun2 0  bs       = RETURNT bs"
  "myfun2 (Suc n) bs       = do {
                      bs' \<leftarrow> mop_append (%_. 1) 0 bs;
                      myfun2  n bs' }" 
  unfolding myfun2_def  by (subst RECT_unfold, refine_mono, auto)+

definition "oappend x' xs' = return (x'#xs')" 

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

   



lemma hn_refine_hd[sepref_fr_rules]: " hn_refine (hn_val Id s' s)
           (ureturn (hd s))
       (hn_val Id s' s)
       (pure Id) (RETURNT $ (hd $ s'))"
  unfolding hn_refine_def apply (auto simp:   mult.assoc  execute_ureturn pure_def hn_ctxt_def)
     by (auto simp: top_assn_rule zero_enat_def relH_def  elim: pureD )   

context 
  fixes n::"nat"
  notes [[sepref_register_adhoc n]]
  notes [sepref_import_param] = IdI[of n] 
begin 

lemma ff: "hn_ctxt (list_assn nat_assn) a c \<Longrightarrow>\<^sub>t hn_val Id a c"
  unfolding hn_ctxt_def   
  by (simp add: list_assn_pure_conv)  

sepref_definition synth_myfun is "uncurry0 (myfun2 n [])" :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a pure Id" 
  using [[goals_limit = 3]]
  unfolding myfun2_def

  apply sepref_dbg_preproc
  apply sepref_dbg_cons_init
  apply sepref_dbg_id 
     apply sepref_dbg_monadify

     apply sepref_dbg_opt_init

  thm sepref_fr_rules     
  thm sepref_comb_rules          

  apply sepref_dbg_trans_step+

  apply sepref_dbg_opt 
  apply sepref_dbg_cons_solve \<comment> \<open>Frame rule, recovering the invalidated list 
    or pure elements, propagating recovery over the list structure\<close>
   (* apply sepref_dbg_cons_solve \<comment> \<open>Trivial frame rule\<close> *) apply(rule ff)
  apply sepref_dbg_constraints
  done

context 
  fixes as::"nat list"
  notes [[sepref_register_adhoc as]]
  notes [sepref_import_param] = IdI[of as] 
begin 

sepref_definition synth_myfun is "uncurry0 (myfun as [])" :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a pure Id" 
  using [[goals_limit = 3]]
  unfolding myfun_def

  apply sepref_dbg_preproc
  apply sepref_dbg_cons_init
  apply sepref_dbg_id 
     apply sepref_dbg_monadify

     apply sepref_dbg_opt_init

  thm sepref_fr_rules     
  thm sepref_comb_rules          

  apply sepref_dbg_trans_step+


  apply sepref_dbg_opt
  apply sepref_dbg_cons_solve \<comment> \<open>Frame rule, recovering the invalidated list 
    or pure elements, propagating recovery over the list structure\<close>
  apply sepref_dbg_cons_solve \<comment> \<open>Trivial frame rule\<close>
  apply sepref_dbg_constraints
  done



end