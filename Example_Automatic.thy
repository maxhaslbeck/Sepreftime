theory Example_Automatic
  imports "Refine_Imperative_HOL/Sepref_Tool" "SepLogicTime_RBTreeBasic.RBTree_Impl"
    Set_Impl2  
begin
 

lemma set_init_hnr'_short[sepref_fr_rules]:
  "hn_refine (emp) set_empty emp rbt_set_assn (set_init_SPEC)"
  sorry

lemma set_ins_hnr_abs[sepref_fr_rules]:
  "hn_refine (hn_ctxt rbt_set_assn S p * hn_val Id x x')
       (rbt_set_insert x' p)
       (hn_invalid rbt_set_assn S p * hn_val Id x x') rbt_set_assn (set_ins_SPEC $ x $ S)"
  sorry

(*
lemma set_mem_hnr_abs[sepref_fr_rules]:
  "hn_refine (hn_ctxt rbt_set_assn S p * hn_val Id x x')
     (rbt_search (x'::nat) p)
     (hn_ctxt rbt_set_assn S p * hn_val Id x x') Y' ( (set_mem_SPEC $ x $ S))"
  sorry *)

definition rbt_mem :: "nat \<Rightarrow> (nat, unit) rbt_node ref option \<Rightarrow> bool Heap" where 
  "rbt_mem x p = do {
      f \<leftarrow> rbt_search x p;
      ureturn (f = Some ()) }"

lemma set_mem_hnr [sepref_fr_rules]:
  "hn_refine (hn_ctxt rbt_set_assn S p * hn_val Id x x')
     (rbt_mem (x'::nat) p)
     (hn_ctxt rbt_set_assn S p * hn_val Id x x') id_assn ( (set_mem_SPEC $ x $ S))"
  sorry


definition rd_impl1 :: "nat list \<Rightarrow> (nat list) nrest" where
  "rd_impl1 as = do {
          ys \<leftarrow> RETURNT [];
          S \<leftarrow> set_init_SPEC;
          zs \<leftarrow> RETURNT as;
          (zs,ys,S) \<leftarrow> whileT (\<lambda>(xs,ys,S). length xs > 0)
            (\<lambda>(xs,ys,S). do {                          
                          ASSERT (length xs > 0);
                          ASSERT (length xs + length ys \<le> length as);
                          ASSERT (card S \<le> length ys);
                          x \<leftarrow> RETURNT (hd xs);
                          xs \<leftarrow> RETURNT (tl xs);
                          b \<leftarrow> set_mem_SPEC x S;
                          (if b
  then  RETURNT (xs,ys,S)
  else do { S \<leftarrow> set_ins_SPEC x S;
            ys \<leftarrow> RETURNT (x#ys);  
            RETURNT (xs,ys,S)
  } ) }) (zs,ys,S);
          RETURNT ys
      }"

(* library *) 

lemma zuf: "\<up> True * true =  true"  
  by (simp add: abel_semigroup.commute assn_ext mult.abel_semigroup_axioms)  


fun list_assn :: "('a \<Rightarrow> 'c \<Rightarrow> assn) \<Rightarrow> 'a list \<Rightarrow> 'c list \<Rightarrow> assn" where
  "list_assn P [] [] = emp"
| "list_assn P (a#as) (c#cs) = P a c * list_assn P as cs"
| "list_assn _ _ _ = false"

lemma hn_refine_Zero[sepref_fr_rules]: " hn_refine emp
           (ureturn (0::nat)) emp
       (pure Id) (RETURNT $ (0::nat))"
  unfolding hn_refine_def apply (auto simp: zuf mult.assoc  execute_ureturn pure_def hn_ctxt_def)
   apply(rule exI[where x=0]) apply (auto simp: zero_enat_def relH_def )      
    using models_in_range top_assn_rule  
    by (metis (full_types) mod_false zuf)  

lemma hn_refine_Nil[sepref_fr_rules]: " hn_refine emp
           (ureturn []) emp
       (list_assn P) (RETURNT $ [])"
  unfolding hn_refine_def apply (auto simp: zuf mult.assoc  execute_ureturn pure_def hn_ctxt_def)
   apply(rule exI[where x=0]) apply (auto simp: zero_enat_def relH_def )      
    using models_in_range top_assn_rule  
    by (metis (full_types) mod_false zuf)  
 

lemma hn_refine_less[sepref_fr_rules]: " hn_refine
     (hn_val nat_rel x' x * hn_val nat_rel y' y)
     (ureturn (y < x))
     (hn_val nat_rel y' y * hn_val nat_rel x' x)
     (pure bool_rel) (RETURNT $ ((<) $ y' $ x'))"
  unfolding hn_refine_def apply (auto simp: zuf mult.assoc  execute_ureturn pure_def hn_ctxt_def )
   apply(rule exI[where x=0]) apply (auto simp: zero_enat_def relH_def  elim: pureD )      
    using models_in_range top_assn_rule   
    by (metis (full_types) SepLogic_Misc.mod_pure_star_dist assn_times_comm)+

lemma hn_Pair[sepref_fr_rules]: "hn_refine 
  (hn_ctxt P1 x1 x1' * hn_ctxt P2 x2 x2')
  (ureturn (x1',x2'))
  (hn_invalid P1 x1 x1' * hn_invalid P2 x2 x2')
  (prod_assn P1 P2)
  (RETURNT$(Pair$x1$x2))"
  unfolding hn_refine_def apply (auto simp: zuf mult.assoc  execute_ureturn pure_def hn_ctxt_def)
   apply(rule exI[where x=0]) apply (auto simp: zero_enat_def relH_def )      
  apply(rule entailsD)  prefer 2 apply auto
  sorry

lemma hn_refine_length[sepref_fr_rules]: " hn_refine (hn_val Id xs' xs)
           (ureturn (length xs))
       (hn_val Id xs' xs)
       (pure Id) (RETURNT $ (length $ xs'))"
  unfolding hn_refine_def apply (auto simp: zuf mult.assoc  execute_ureturn pure_def hn_ctxt_def)
   apply(rule exI[where x=0]) apply (auto simp: zero_enat_def relH_def elim: pureD  )      
    using models_in_range top_assn_rule  
    by (metis (full_types) mod_false)+  

lemma hn_refine_hd[sepref_fr_rules]: " hn_refine (hn_val Id s' s)
           (ureturn (hd s))
       (hn_val Id s' s)
       (pure Id) (RETURNT $ (hd $ s'))"
  unfolding hn_refine_def apply (auto simp: zuf mult.assoc  execute_ureturn pure_def hn_ctxt_def)
   apply(rule exI[where x=0]) apply (auto simp: zero_enat_def relH_def  elim: pureD )      
    using models_in_range top_assn_rule  
    by (metis (full_types) mod_false zuf)+
  

lemma hn_refine_tl[sepref_fr_rules]: " hn_refine (hn_val Id s' s)
           (ureturn (tl s))
       (hn_val Id s' s)
       (pure Id) (RETURNT $ (tl $ s'))"
  unfolding hn_refine_def apply (auto simp: zuf mult.assoc  execute_ureturn pure_def hn_ctxt_def)
   apply(rule exI[where x=0]) apply (auto simp: zero_enat_def relH_def  elim: pureD )      
    using models_in_range top_assn_rule  
    by (metis (full_types) mod_false zuf)+

 

lemma hn_if[sepref_comb_rules]:
  assumes P: "\<Gamma> \<Longrightarrow>\<^sub>t \<Gamma>1 * hn_val bool_rel a a'"
  assumes RT: "a \<Longrightarrow> hn_refine (\<Gamma>1 * hn_val bool_rel a a') b' \<Gamma>2b R b"
  assumes RE: "\<not>a \<Longrightarrow> hn_refine (\<Gamma>1 * hn_val bool_rel a a') c' \<Gamma>2c R c"
  assumes IMP: "TERM If \<Longrightarrow> \<Gamma>2b \<or>\<^sub>A \<Gamma>2c \<Longrightarrow>\<^sub>t \<Gamma>'"
  shows "hn_refine \<Gamma> (if a' then b' else c') \<Gamma>' R (If$a$b$c)"
  using P RT RE IMP[OF TERMI]
  unfolding APP_def PROTECT2_def 
  by (rule hnr_If)


lemma hnr_cons_rule[sepref_fr_rules]: " hn_refine (hn_ctxt (list_assn P) xs' xs * hn_ctxt P x' x)
           (ureturn (x#xs))
       (hn_invalid (list_assn P) xs' xs * hn_invalid P x' x)
       (list_assn P) (RETURNT $ (Cons $  x' $ xs'))"
  unfolding hn_refine_def apply (auto simp: zuf mult.assoc  execute_ureturn pure_def hn_ctxt_def)
   apply(rule exI[where x=0]) apply (auto simp: zero_enat_def relH_def )      
  using models_in_range top_assn_rule        sorry

lemma prod_assn_ctxt: "prod_assn A1 A2 x y = z \<Longrightarrow> hn_ctxt (prod_assn A1 A2) x y = z"
  by (simp add: hn_ctxt_def)
lemma hn_case_prod'[sepref_prep_comb_rule,sepref_comb_rules]:
  assumes FR: "\<Gamma>\<Longrightarrow>\<^sub>thn_ctxt (prod_assn P1 P2) p' p * \<Gamma>1"
  assumes Pair: "\<And>a1 a2 a1' a2'. \<lbrakk>p'=(a1',a2')\<rbrakk> 
    \<Longrightarrow> hn_refine (hn_ctxt P1 a1' a1 * hn_ctxt P2 a2' a2 * \<Gamma>1 * hn_invalid (prod_assn P1 P2) p' p) (f a1 a2) 
          (hn_ctxt P1' a1' a1 * hn_ctxt P2' a2' a2 * hn_ctxt XX1 p' p * \<Gamma>1') R (f' a1' a2')"
  shows "hn_refine \<Gamma> (case_prod f p) (hn_ctxt (prod_assn P1' P2') p' p * \<Gamma>1')
    R (case_prod$(\<lambda>\<^sub>2a b. f' a b)$p')" (is "?G \<Gamma>")
    apply1 (rule hn_refine_cons_pre[OF FR])
    apply1 extract_hnr_invalids
    apply1 (cases p; cases p'; simp add: prod_assn_pair_conv[THEN prod_assn_ctxt])
    apply (rule hn_refine_cons[OF _ Pair _ entt_refl])
  subgoal
    apply (simp add: hn_ctxt_def entailst_def)
          apply(rule ent_true_drop(2))
          apply(rule ent_true_drop(2)) apply(rule entails_triv) done
    applyS simp
      subgoal
        apply  (simp add: hn_ctxt_def entailst_def mult.assoc)
    apply(rule match_first)
    apply(rule match_first) apply(rotatel)
    apply(rule match_first)  by simp
      done
 

context 
  fixes as::"nat list"
  notes [[sepref_register_adhoc as]]
  notes [sepref_import_param] = IdI[of as] 
begin

schematic_goal "hn_refine \<Gamma> (?C::?'a Heap) ?\<Gamma>' ?R (rd_impl1 as)" using [[goals_limit = 3]]
  unfolding rd_impl1_def

  apply sepref_dbg_preproc
  apply sepref_dbg_cons_init
  apply sepref_dbg_id 
     apply sepref_dbg_monadify

     apply sepref_dbg_opt_init
                                              
  apply sepref_dbg_trans_step                
  apply sepref_dbg_trans_step                
  apply sepref_dbg_trans_step                
  apply sepref_dbg_trans_step                
  apply sepref_dbg_trans_step                
  apply sepref_dbg_trans_step                
  apply sepref_dbg_trans_step                   
  apply sepref_dbg_trans_step                
  apply sepref_dbg_trans_step                
  apply sepref_dbg_trans_step                
  apply sepref_dbg_trans_step                
  apply sepref_dbg_trans_step                
  apply sepref_dbg_trans_step                
  apply sepref_dbg_trans_step                   
  apply sepref_dbg_trans_step                
  apply sepref_dbg_trans_step                
  apply sepref_dbg_trans_step                
  apply sepref_dbg_trans_step                
  apply sepref_dbg_trans_step                
  apply sepref_dbg_trans_step                
  apply sepref_dbg_trans_step                   
  apply sepref_dbg_trans_step                
  apply sepref_dbg_trans_step                
  apply sepref_dbg_trans_step                
  apply sepref_dbg_trans_step                
  apply sepref_dbg_trans_step                
  apply sepref_dbg_trans_step                
  apply sepref_dbg_trans_step                   
  apply sepref_dbg_trans_step                
  apply sepref_dbg_trans_step                
  apply sepref_dbg_trans_step                
  apply sepref_dbg_trans_step                
  apply sepref_dbg_trans_step                
  apply sepref_dbg_trans_step                
  apply sepref_dbg_trans_step                    
  apply sepref_dbg_trans_step                
  apply sepref_dbg_trans_step                
  apply sepref_dbg_trans_step                
  apply sepref_dbg_trans_step                
  apply sepref_dbg_trans_step                
  apply sepref_dbg_trans_step                
  apply sepref_dbg_trans_step   (* if *)                
  apply sepref_dbg_trans_step                
  apply sepref_dbg_trans_step                
  apply sepref_dbg_trans_step                
  apply sepref_dbg_trans_step                
  apply sepref_dbg_trans_step                
  apply sepref_dbg_trans_step                
  apply sepref_dbg_trans_step                   
  apply sepref_dbg_trans_step                
  apply sepref_dbg_trans_step                
  apply sepref_dbg_trans_step                
  apply sepref_dbg_trans_step                
  apply sepref_dbg_trans_step                
  apply sepref_dbg_trans_step                
  apply sepref_dbg_trans_step                   
  apply sepref_dbg_trans_step                
  apply sepref_dbg_trans_step                
  apply sepref_dbg_trans_step                
  apply sepref_dbg_trans_step                
  apply sepref_dbg_trans_step                
  apply sepref_dbg_trans_step                
  apply sepref_dbg_trans_step                   
  apply sepref_dbg_trans_step                
  apply sepref_dbg_trans_step                
  apply sepref_dbg_trans_step                
  apply sepref_dbg_trans_step                
  apply sepref_dbg_trans_step                
  apply sepref_dbg_trans_step                
  apply sepref_dbg_trans_step                   
  apply sepref_dbg_trans_step                
  apply sepref_dbg_trans_step                
  apply sepref_dbg_trans_step                
  apply sepref_dbg_trans_step                
  apply sepref_dbg_trans_step                
  apply sepref_dbg_trans_step                
      apply sepref_dbg_trans_step  

  apply sepref_dbg_opt
  apply sepref_dbg_cons_solve \<comment> \<open>Frame rule, recovering the invalidated list 
    or pure elements, propagating recovery over the list structure\<close>
  apply sepref_dbg_cons_solve \<comment> \<open>Trivial frame rule\<close>
  apply sepref_dbg_constraints
  done

 

end


end