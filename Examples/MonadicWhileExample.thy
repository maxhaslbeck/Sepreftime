theory MonadicWhileExample
imports "../Refine_Imperative_HOL/Sepref" "../RefineMonadicVCG"
    "../Refine_Imperative_HOL/IICF/Impl/IICF_Rbt_Set"   Complex_Main "HOL-Decision_Procs.Approximation"
begin



definition "bodytime = 20+rbt_delete_time_logN (Suc (10))"
definition Prog :: "nat set nrest" where
  "Prog = do {  
          (s::nat set) \<leftarrow> mop_set_empty 10;
          (s::nat set) \<leftarrow> mop_set_insert (\<lambda>x. rbt_insert_logN (card x + 1)) (1::nat) s;                     
          monadic_WHILEIE
              (\<lambda>s. finite s \<and> card (s::nat set) \<le> 10) (\<lambda>s. card (s::nat set) * (bodytime)) 
             (\<lambda>s. do { b \<leftarrow> mop_set_isempty (\<lambda>_. 10) s; RETURNT (~b) })
            (\<lambda>s. do {
                 x \<leftarrow> mop_set_pick (\<lambda>_. 10) s;
                 mop_set_del (\<lambda>s'. rbt_delete_time_logN (card s' + 1)) s x
                }
              ) (s::nat set) }"

term Prog

lemma pff: "x \<in> s \<Longrightarrow> finite s \<Longrightarrow> card s > 0"
  using card_gt_0_iff by blast 

lemma mm2_some_leq: "Some a \<le> mm2 (Some b) (Some c) \<longleftrightarrow> (c \<le> b \<and> a \<le> b - c )"
  unfolding mm2_def by(auto)


lemma F: "160 *  (\<lceil>2 * log 2 11\<rceil> + 1) \<le> 1991"
  by (approximation 10)
lemma G: "10 \<le> 99550 - 8000 * (\<lceil>2 * log 2 11\<rceil> + 1)"
  by (approximation 10)

lemma z: "cs \<le> 10 \<Longrightarrow> rbt_delete_time_logN (Suc cs) \<le> rbt_delete_time_logN (Suc 10)"
  apply(rule rbt_delete_time_logN_mono) by auto

lemma "Prog \<le> SPECT [ {} \<mapsto> enat 100000 ]"
  unfolding Prog_def
  apply(rule T_specifies_I)
  apply (vcg'\<open>-\<close> rules: mop_set_empty mop_set_insert  mop_set_isempty  )  
   apply(split if_split) apply clarsimp
  apply(intro allI impI conjI)
    apply (vcg'\<open>-\<close> rules: mop_set_empty mop_set_pick  mop_set_del ) 
  subgoal  apply (auto simp: card_Diff1_le  dest: pff )
    apply(simp only: Nat.diff_mult_distrib[symmetric])
    apply(subst diff_diff_cancel) subgoal by(auto dest: pff)   
    apply(simp add: bodytime_def )
    apply(frule z) by simp
  subgoal  by (auto )  
  subgoal apply (auto simp: bodytime_def mm2_some_leq rbt_insert_logN_def rbt_delete_time_def btree_del_time_def rbt_delete_time_logN_def rbt_insert_time_def rbt_ins_time_def rbt_absch_def  )
    subgoal 
      using F by simp
    subgoal 
      using G by simp
    done
  subgoal by simp
  done





sepref_definition remdups_impl is "uncurry0 (Prog)" :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a rbt_set_assn"
  unfolding Prog_def monadic_WHILEIE_def monadic_WHILE_aux

  apply sepref_dbg_preproc
  apply sepref_dbg_cons_init
  apply sepref_dbg_id 
     apply sepref_dbg_monadify
     apply sepref_dbg_opt_init                                 
  apply sepref_dbg_trans_step+ 
  apply sepref_dbg_opt
  apply sepref_dbg_cons_solve \<comment> \<open>Frame rule, recovering the invalidated list 
    or pure elements, propagating recovery over the list structure\<close>
  apply sepref_dbg_cons_solve \<comment> \<open>Trivial frame rule\<close>
  apply sepref_dbg_constraints
  done







end