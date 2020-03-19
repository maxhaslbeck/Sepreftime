theory Fib  
  imports "../Refine_Imperative_HOL/Sepref"
    "SepLogicTime_RBTreeBasic.RBTree_Impl"
begin


definition "op_zero = SPECT [(0::nat) \<mapsto> 1]"

definition "op_one = SPECT [1::nat \<mapsto> 1]"

definition op_plus :: "nat \<Rightarrow> nat \<Rightarrow> nat nrest" where
  "op_plus a b = SPECT [a+b \<mapsto> 1]"

definition myfun :: "nat \<Rightarrow> nat nrest" where
      "myfun n = RECT (\<lambda>fw n. if n = 0
                                       then op_zero
                                   else 
                                    (if n = 1 
                                        then op_one
                                        else do { a \<leftarrow> fw (n-2); b \<leftarrow> fw (n-1); RETURNT (a + b) } )) n"

lemma myfun_simps:
  "myfun 0              = op_zero"
  "myfun (Suc 0)        = op_one"
  "myfun (Suc (Suc n))  = do { a \<leftarrow> myfun (n); b \<leftarrow> myfun (n+1); RETURNT (a + b) }"
  unfolding myfun_def by (subst RECT_unfold, refine_mono, auto split: nat.split)+

fun fib where
  "fib 0 = 0"
|  "fib (Suc 0) = 1"
| "fib (Suc (Suc n)) = fib n + fib (Suc n)"

fun fib_time :: "nat \<Rightarrow> nat" where
  "fib_time 0 = 1"
| "fib_time (Suc 0) = 1"
| "fib_time (Suc (Suc n)) = fib_time n + fib_time (Suc n) + 1"

definition "fib_SPEC n \<equiv> SPECT [fib n \<mapsto> fib_time n]"

lemma spec: "myfun n \<le> fib_SPEC n"
  apply(induction n rule: fib.induct)
    apply (auto simp: fib_SPEC_def myfun_simps op_one_def zero_enat_def one_enat_def op_zero_def op_plus_def pw_le_iff refine_pw_simps)
  subgoal for n r' t' t'' r''
  proof (goal_cases)
    case 1 
    from 1(2,5) obtain t1 where t1: "t1\<ge>enat t'" and "(if r' = fib n then Some (enat (fib_time n)) else None) = Some t1" by blast
    then have A: "r'= fib n" "t1 = fib_time n" by (auto split: if_splits)

    from 1(4,6) obtain t2 where t2: "t2\<ge>enat t''" and "(if r'' = fib (Suc n) then Some (enat (fib_time (Suc n))) else None) = Some t2" by blast
    then have B: "r'' = fib (Suc n)" "t2 = fib_time (Suc n)" by (auto split: if_splits)

    from A B t1 t2 show ?case by simp
  qed
      
  subgoal 
    by (metis option.simps(3)) 
  done

 

lemma hn_refine_op_plus[sepref_fr_rules]: " hn_refine
     (hn_val nat_rel y' y * hn_val nat_rel x' x)
     (ureturn (y + x))
     (hn_val nat_rel y' y * hn_val nat_rel x' x)
     (pure nat_rel) ( (op_plus $ y' $ x'))"
  unfolding hn_refine_def apply (auto simp: op_plus_def mult.assoc  execute_ureturn pure_def hn_ctxt_def )
   apply(rule exI[where x=0]) by (auto simp: top_assn_rule zero_enat_def one_enat_def relH_def  elim: pureD )      
 

lemma hn_refine_zero[sepref_fr_rules]: " hn_refine
     (emp)
     (ureturn (0))
     (emp)
     (pure nat_rel) ( (op_zero))"
  unfolding hn_refine_def
  using models_in_range top_assn_rule 
  by (auto simp: execute_ureturn pure_def op_zero_def one_enat_def relH_def
              elim: pureD )      


lemma hn_refine_one[sepref_fr_rules]: " hn_refine
     (emp)
     (ureturn (1))
     (emp)
     (pure nat_rel) ( (op_one))"
  unfolding hn_refine_def    
  using models_in_range top_assn_rule
  by (auto simp: execute_ureturn pure_def op_one_def one_enat_def relH_def
              elim: pureD )

(*

lemma hn_refine_PR2[sepref_fr_rules]: " hn_refine emp
           (ureturn (2::nat)) emp
       (pure Id) (RETURNT $ (PR_CONST (2::nat)))"
  unfolding hn_refine_def apply (auto simp: zuf mult.assoc  execute_ureturn pure_def hn_ctxt_def)
   apply(rule exI[where x=0]) apply (auto simp: zero_enat_def relH_def )      
    using models_in_range top_assn_rule  
    by (metis (full_types) mod_false zuf)  

lemma hn_refine_PR1[sepref_fr_rules]: " hn_refine emp
           (ureturn (1::nat)) emp
       (pure Id) (RETURNT $ (PR_CONST (1::nat)))"
  unfolding hn_refine_def apply (auto simp: zuf mult.assoc  execute_ureturn pure_def hn_ctxt_def)
   apply(rule exI[where x=0]) apply (auto simp: zero_enat_def relH_def )      
    using models_in_range top_assn_rule  
    by (metis (full_types) mod_false zuf)  

lemma hn_refine_Zero[sepref_fr_rules]: " hn_refine emp
           (ureturn (0::nat)) emp
       (pure Id) (RETURNT $ (0::nat))"
  unfolding hn_refine_def apply (auto simp: zuf mult.assoc  execute_ureturn pure_def hn_ctxt_def)
   apply(rule exI[where x=0]) apply (auto simp: zero_enat_def relH_def )      
    using models_in_range top_assn_rule  
    by (metis (full_types) mod_false zuf)  

lemma hn_refine_One[sepref_fr_rules]: " hn_refine emp
           (ureturn (1::nat)) emp
       (pure Id) (RETURNT $ (1::nat))"
  unfolding hn_refine_def apply (auto simp: zuf mult.assoc  execute_ureturn pure_def hn_ctxt_def)
   apply(rule exI[where x=0]) apply (auto simp: zero_enat_def relH_def )      
    using models_in_range top_assn_rule  
    by (metis (full_types) mod_false zuf)  

lemma hn_refine_eq[sepref_fr_rules]: " hn_refine
     (hn_val nat_rel x' x * hn_val nat_rel y' y)
     (ureturn (y = x))
     (hn_val nat_rel y' y * hn_val nat_rel x' x)
     (pure bool_rel) (RETURNT $ ((=) $ y' $ x'))"
  unfolding hn_refine_def apply (auto simp: zuf mult.assoc  execute_ureturn pure_def hn_ctxt_def )
   by (auto simp:top_assn_rule  zero_enat_def relH_def  elim: pureD )      
  *)

context 
  fixes n::"nat"
  notes [[sepref_register_adhoc n]]
  notes [sepref_import_param] = IdI[of n] 
begin 

schematic_goal synth_myfun: "hn_refine emp (?C::nat Heap) ?\<Gamma>' ?R (myfun n)"
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

thm synth_myfun
concrete_definition myfun_impl uses synth_myfun is "hn_refine _ (?c n) _ _ _"


thm myfun_impl_def
thm extract_cost_ub[OF   hnr_refine[OF spec synth_myfun, unfolded fib_SPEC_def]]
lemma "<$ (fib_time n)>
         myfun_impl n
       <\<lambda>r. (\<exists>\<^sub>Ara. id_assn ra r * \<up> (ra \<in> dom [fib n \<mapsto> enat (fib_time n)]))>\<^sub>t"
  unfolding myfun_impl_def
  apply(rule extract_cost_ub'[where Cost_ub="fib_time n", OF hnr_refine[OF spec synth_myfun, unfolded fib_SPEC_def]])
  by sep_auto+


  


end


end
