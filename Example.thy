theory Example 
imports HNR_While
begin


lemma assumes    "a = (\<lambda>s. SPECT [s-1\<mapsto>1])" 
    shows ex4_ref: "(whileT (\<lambda>s. s>0) (\<lambda>s. RETURNT (s-1)) (S::nat)) \<le> (whileT (\<lambda>s. s>0) a (S::nat))"
  apply(rule whileT_mono)
  unfolding assms 
  by (simp add: RETURNT_def le_fun_def)

lemma k: "(emp \<Longrightarrow>\<^sub>A \<up> (s = S) * true) \<longleftrightarrow> s=S" 
  apply rule
  apply (smt assn_ext entailsD' entailsI mod_false' mult.left_neutral pure_assn_eq_conv)   
  using assn_times_comm entails_pure_post entails_true by fastforce
lemma k2: "(emp \<Longrightarrow>\<^sub>A \<up> (s = S) ) \<longleftrightarrow> s=S" 
  apply rule
  apply (smt assn_ext entailsD' entailsI mod_false' mult.left_neutral pure_assn_eq_conv)   
  using entails_pure' entails_triv by blast 

lemma extr: "pHeap h as n \<Turnstile> \<up>B = (pHeap h as n \<Turnstile> emp \<and> B)"
  using one_assn_rule pure_assn_rule by auto  
 
lemma R: "((s,s') \<in> Rs \<Longrightarrow> hn_refine (emp) (c s) (G s' s) R (a s'))
    \<Longrightarrow> hn_refine (hn_ctxt (pure Rs) s' s) (c s) (G s' s) R (a s')"
  unfolding hn_refine_def by (auto simp: hn_ctxt_def pure_def extr)


thm hnr_uRETURN_pass

lemma moneq: "(\<lambda>s. RETURNT (0 < s)) = (\<lambda>s. RETURNT 0 \<bind> (%c. RETURNT (c < s)))"
  by (auto intro!: pw_eqI)

lemma moneq_min: "(\<lambda>s. RETURNT (s - 1)) = (\<lambda>s. RETURNT 1 \<bind> (%c. RETURNT (s - c)))"
  by (auto intro!: pw_eqI)

lemma x0: "RETURNT x \<le> RETURNT 0 \<longleftrightarrow> x=0"
  by (auto simp: RETURNT_def le_fun_def split: if_splits)  

lemma [simp]: "h\<Turnstile>\<up>b \<longleftrightarrow> (h\<Turnstile>emp \<and> b)" 
  using one_assn_rule pure_assn_rule by auto 

lemma zuf: "\<up> True * true =  true"  
  by (simp add: abel_semigroup.commute assn_ext mult.abel_semigroup_axioms)  

lemma hn_refine_less: " hn_refine (hn_val nat_rel s' s * hn_val nat_rel x' x)
           (ureturn (x < s))
       (hn_val nat_rel s' s * hn_val nat_rel x' x)
       (pure bool_rel) (RETURNT (x' < s'))"
  unfolding hn_refine_def apply (auto simp: zuf mult.assoc  execute_ureturn pure_def hn_ctxt_def)
   apply(rule exI[where x=0]) apply (auto simp: zero_enat_def relH_def )      
    using models_in_range top_assn_rule by blast 


lemma hn_refine_minus: " hn_refine (hn_val nat_rel s' s * hn_val nat_rel x' x)
           (ureturn (x - s))
       (hn_val nat_rel s' s * hn_val nat_rel x' x)
       (pure nat_rel) (RETURNT (x' - s'))"
  unfolding hn_refine_def apply (auto simp: zuf mult.assoc  execute_ureturn pure_def hn_ctxt_def)
   apply(rule exI[where x=0]) apply (auto simp: zero_enat_def relH_def )      
    using models_in_range top_assn_rule by blast 


schematic_goal first:
  assumes "a = (whileT (\<lambda>s. s>0) (\<lambda>s. RETURNT (s-1)) (S::nat))"
  shows "hn_refine emp ?c ?\<Gamma> (pure Id) a"
  unfolding assms 
  apply(subst whileT_I')
  apply(subst WHILEIT_to_monadic) apply(subst moneq)  apply(subst moneq_min)
  apply(rule hn_monadic_WHILE_aux[where \<Gamma>="emp"])
      apply (simp add: hn_ctxt_def pure_def k entailst_def ) 
  
     apply (simp del: nres_bind_left_identity)
     apply(rule hnr_bind)  
       apply(rule hnr_frame[OF hnr_uRETURN_pure[where R=nat_rel]])
        apply simp
       apply (simp add: ) apply(rule entt_refl)
      apply (simp  )  
      apply(rule hn_refine_less)
  apply(simp add: mult.assoc)
  apply(rule match_first) 
     apply(rule match_rest) apply (simp)

  apply(simp add: entailst_def)
    apply(rule match_rest) apply (simp)

   apply (simp del: nres_bind_left_identity)
     apply(rule hnr_bind)  
     apply(rule hnr_frame[OF hnr_uRETURN_pure[where R=nat_rel]])    
        apply simp
       apply (simp add: ) apply(rule entt_refl)
      apply (simp  )  
     apply(rule hn_refine_cons_pre[OF _ hn_refine_minus])
  apply(simp add: entailst_def)
    apply rotatel apply(rule match_first)   apply(rule match_rest) apply simp
   apply rotatel apply(rule match_first) apply (rule match_rest) apply simp
  
  apply (simp add: hn_ctxt_def pure_def k)  
  by (simp add: ent_imp_entt)  

thm first extract_cost_ub hnr_refine


lemma entails_ex': "((\<exists>\<^sub>Ax. P x) \<Longrightarrow>\<^sub>A Q) \<longleftrightarrow> (\<forall>x. (P x \<Longrightarrow>\<^sub>A Q))"
  using entails_ex by blast

thm ex4_ref ex4'
lemma "S \<le> n \<Longrightarrow> <$ n> (heap_WHILET (\<lambda>s. ureturn 0 \<bind> (\<lambda>x'. ureturn (x' < s))) (\<lambda>s. ureturn (Suc 0) \<bind> (\<lambda>x'. ureturn (s - x'))) S) <\<lambda>r. \<up> (r = 0)>\<^sub>t"
proof -
  assume as: "S \<le> n"
  from ex4_ref have "whileT (op < 0) (\<lambda>s. RETURNT (s - 1)) S \<le> whileT (op < 0) (\<lambda>s. SPECT [s - 1 \<mapsto> 1]) S" by auto
  also from as ex4' have "\<dots> \<le> SPECT (\<lambda>s. if s = 0 then Some (enat n) else None) " by simp
  finally have spec: "whileT (op < 0) (\<lambda>s. RETURNT (s - 1)) S \<le> SPECT (\<lambda>s. if s = 0 then Some (enat n) else None)" .

  let ?P= "(heap_WHILET (\<lambda>s. ureturn 0 \<bind> (\<lambda>x'. ureturn (x' < s))) (\<lambda>s. ureturn (Suc 0) \<bind> (\<lambda>x'. ureturn (s - x'))) S)"
  from hnr_refine[OF spec first] have "hn_refine emp ?P (emp * hn_invalid (pure nat_rel) S S) (pure nat_rel)
   (SPECT (\<lambda>s. if s = 0 then Some (enat n) else None))" by auto

  from extract_cost_ub[OF this, where Cost_ub=n] have "< $ n> ?P <\<lambda>r. emp * hn_invalid (pure nat_rel) S S * (\<exists>\<^sub>Ara. pure nat_rel ra r * \<up> (ra \<in> dom (\<lambda>s. if s = 0 then Some (enat n) else None)))>\<^sub>t"
    by simp
  then show "<$ n> ?P <\<lambda>r. \<up> (r = 0)>\<^sub>t"
      apply(rule post_rule)
    apply (simp add: pure_def hn_ctxt_def invalid_assn_def)
       apply (auto simp: )
    apply rotatel apply rotatel apply(simp add: ex_distrib_star[symmetric] entails_ex'  )
    apply auto  
    by (smt SepAuto.mod_pure_star_dist abel_semigroup.commute entails_def entails_true mult.abel_semigroup_axioms pure_conj)
qed
  


thm hnr_refine[OF _ first]


end