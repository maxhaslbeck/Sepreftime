theory Fib  
  imports "../Refine_Imperative_HOL/Sepref"
    "Imperative_HOL_Time.RBTree_Impl" "NREST.RefineMonadicVCG"
begin
hide_const R B

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
proof (induction n rule: fib.induct)
  case (3 n)
  note IH = 3[unfolded fib_SPEC_def, THEN T_specifies_rev, THEN T_conseq4]
  show ?case
    apply(simp add: fib_SPEC_def myfun_simps)
    apply(rule T_specifies_I)
    apply(vcg' \<open>-\<close> rules: IH )
    by (auto split: if_splits)
qed (auto simp: fib_SPEC_def myfun_simps one_enat_def op_zero_def
                     op_one_def) 

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

context 
  fixes n::"nat"
  notes [[sepref_register_adhoc n]]
  notes [sepref_import_param] = IdI[of n] 
begin 

schematic_goal synth_myfun: "hn_refine emp (?C::nat Heap) ?\<Gamma>' ?R (myfun n)"
  using [[goals_limit = 3]]
  unfolding myfun_def
  by sepref

concrete_definition myfun_impl uses synth_myfun is "hn_refine _ (?c n) _ _ _"


lemma "<$ (fib_time n)>
         myfun_impl n
       <\<lambda>r. (\<exists>\<^sub>Ara. id_assn ra r * \<up> (ra \<in> dom [fib n \<mapsto> enat (fib_time n)]))>\<^sub>t"
  unfolding myfun_impl_def
  apply(rule extract_cost_ub'[where Cost_ub="fib_time n", OF hnr_refine[OF spec synth_myfun, unfolded fib_SPEC_def]])
  by sep_auto+

end


end
