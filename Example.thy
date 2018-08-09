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

schematic_goal
  assumes "a = (whileT (\<lambda>s. s>0) (\<lambda>s. RETURNT (s-1)) (S::nat))"
  shows "hn_refine emp ?c ?\<Gamma> (pure Id) a"
  unfolding assms 
  apply(subst WHILEIT_to_monadic) apply(subst moneq)
  apply(rule hn_monadic_WHILE_aux[where \<Gamma>="emp"])
      apply (simp add: hn_ctxt_def pure_def k entailst_def ) 
  
     apply (simp del: nres_bind_left_identity)
     apply(rule hnr_bind) 

     apply(rule hn_refine_cons_pre)
      prefer 2     
     apply(rule hnr_uRETURN_pass)
     apply simp
  apply (simp add: hn_ctxt_def pure_def k) 
  using hnr_uRETURN_pass
  using hnr_uRETURN_pure
  subgoal unfolding hn_ctxt_def
  apply(rule hnr_uRETURN_pure)
  


end