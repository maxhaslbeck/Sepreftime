theory IICF_Misc
imports "../Sepref"
begin





context
  fixes t ::  "nat"
begin
  definition "mop_plus a b =SPECT [a +  b \<mapsto> t]"

  lemma mop_plus: "\<And>tt. tt \<le> TTT Q (SPECT [ a +  b \<mapsto> t]) \<Longrightarrow> tt
           \<le> TTT Q (mop_plus a b)" unfolding mop_plus_def by simp 
 
  sepref_register "mop_plus" 
  print_theorems 
end 
 

 
 
lemma hn_refine_plus[sepref_fr_rules]: " hn_refine (hn_val Id a' a * hn_val Id b' b)
           (ureturn (a +  b))
       (hn_val Id a' a * hn_val Id b' b)
       (pure Id) (((PR_CONST (mop_plus t)) $ a' $ b'))"
  unfolding hn_refine_def apply (auto simp:   mult.assoc  execute_ureturn pure_def hn_ctxt_def)
  by (auto simp: top_assn_rule zero_enat_def relH_def  mop_plus_def elim: pureD ) 
 
context
  fixes t ::  "nat"
begin
  definition "mop_min a b =SPECT [min a b \<mapsto> t]"

  lemma mop_min: "\<And>tt. tt \<le> TTT Q (SPECT [ min a b \<mapsto> t]) \<Longrightarrow> tt
           \<le> TTT Q (mop_min a b)" unfolding mop_min_def by simp 
 
  sepref_register "mop_min" 
  print_theorems 
end 
 

 
 
lemma hn_refine_min[sepref_fr_rules]: " hn_refine (hn_val Id a' a * hn_val Id b' b)
           (ureturn (min a b))
       (hn_val Id a' a * hn_val Id b' b)
       (pure Id) (((PR_CONST (mop_min t)) $ a' $ b'))"
  unfolding hn_refine_def apply (auto simp:   mult.assoc  execute_ureturn pure_def hn_ctxt_def)
  by (auto simp: top_assn_rule zero_enat_def relH_def  mop_min_def elim: pureD ) 
 
           
context
  fixes t ::  "nat"
begin
  definition "mop_swap e =SPECT [prod.swap e \<mapsto> t]"

  lemma mop_swap: "\<And>tt. tt \<le> TTT Q (SPECT [ prod.swap e \<mapsto> t]) \<Longrightarrow> tt
           \<le> TTT Q (mop_swap e)" unfolding mop_swap_def by simp 
 
  sepref_register "mop_swap" 
  print_theorems 
end 
 

 
 
lemma hn_refine_swap[sepref_fr_rules]: " hn_refine (hn_ctxt (nat_assn \<times>\<^sub>a nat_assn) e' e)
           (ureturn (prod.swap e))
       (hn_ctxt (nat_assn \<times>\<^sub>a nat_assn) e' e)
       (nat_assn \<times>\<^sub>a nat_assn) (((PR_CONST (mop_swap t)) $ e'))"
  unfolding hn_refine_def apply (auto simp:      execute_ureturn    )
   apply (auto simp: top_assn_rule zero_enat_def relH_def prod.swap_def mop_swap_def elim: pureD ) 
  apply(rule exI[where x=0]) apply auto  
  by (smt BNF_Greatest_Fixpoint.IdD IdI entails_def entails_true hn_ctxt_def mult.left_neutral pure_assn_rule pure_def pure_true)  
  

end