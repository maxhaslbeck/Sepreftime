theory Example 
imports HNR  
begin

subsection "Mono Prover"

  (* Wraps mono-prover of partial-function to erase premises. 
    This is a workaround for mono_tac, which does not accept premises if the case-split rule is applied. *)


ML \<open>
  structure Pf_Mono_Prover = struct
    fun mono_tac ctxt = (REPEAT o eresolve_tac ctxt @{thms thin_rl})
      THEN' Partial_Function.mono_tac ctxt
  end
\<close>

method_setup pf_mono = \<open>Scan.succeed (fn ctxt => SIMPLE_METHOD' (Pf_Mono_Prover.mono_tac ctxt))\<close> \<open>Monotonicity prover of the partial function package\<close>

subsection "While rule for hnr"

definition "monadic_WHILEIT I b f s \<equiv> do {
  Sepreftime.RECT (\<lambda>D s. do {
    ASSERT (I s);
    bv \<leftarrow> b s;
    if bv then do {
      s \<leftarrow> f s;
      D s
    } else do {RETURNT s}
  }) s
}"

definition "heap_WHILET b f s \<equiv> do {
  heap.fixp_fun (\<lambda>D s. do {
    bv \<leftarrow> b s;
    if bv then do {
      s \<leftarrow> f s;
      D s
    } else do {ureturn s}
  }) s
}"

lemma heap_WHILET_unfold[code]: "heap_WHILET b f s = 
  do {
    bv \<leftarrow> b s;
    if bv then do {
      s \<leftarrow> f s;
      heap_WHILET b f s
    } else
      ureturn s
  }"
  unfolding heap_WHILET_def
  apply (subst heap.mono_body_fixp)
  apply pf_mono
  apply simp
  done


definition  WHILEIT :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a nrest) \<Rightarrow> 'a \<Rightarrow> 'a nrest" where
  " WHILEIT I b c = RECT (\<lambda>whileT s. (if I s then (if b s then bindT (c s) whileT else RETURNT s) else FAILT))"
 
lemma WHILEIT_to_monadic: "WHILEIT I b f s = monadic_WHILEIT I (\<lambda>s. RETURNT (b s)) f s"
  unfolding WHILEIT_def monadic_WHILEIT_def
  unfolding whileT_def bind_ASSERT_eq_if
  by (simp cong: if_cong) 

lemma Ra: "A * \<Gamma> \<Longrightarrow>\<^sub>t \<Gamma> * A"  
  by (simp add: assn_times_comm entt_refl)  



lemma left_move_back: "(A \<Longrightarrow>\<^sub>A B * C) \<Longrightarrow> (A \<Longrightarrow>\<^sub>A C * B)"
  by (simp add: assn_times_comm)
lemma right_move_back: "(B * C \<Longrightarrow>\<^sub>A A) \<Longrightarrow> (C * B \<Longrightarrow>\<^sub>A A)"
  by (simp add: assn_times_comm)

lemma pull_forward: "(A \<Longrightarrow>\<^sub>A B * C * D) \<Longrightarrow> (A \<Longrightarrow>\<^sub>A B * (C * D))"
  by (simp add: mult.assoc)

lemma match_first: "A \<Longrightarrow>\<^sub>A B \<Longrightarrow> \<Gamma> * A \<Longrightarrow>\<^sub>A \<Gamma> * B"  
  by (simp add: assn_times_comm entails_frame)  

lemma match_rest: "emp \<Longrightarrow>\<^sub>A B \<Longrightarrow> \<Gamma> \<Longrightarrow>\<^sub>A \<Gamma> * B"  
  using match_first by fastforce 

thm mult.assoc
method rotater = ( (simp add: mult.assoc)? , rule left_move_back , (simp add: mult.assoc)?  )
method rotatel = ( (simp add: mult.assoc)? , rule right_move_back , (simp add: mult.assoc)?  )

lemma "\<And>x y. A \<Longrightarrow>\<^sub>A B x y * C"
  apply rotater
  oops
 
schematic_goal "\<And>x y. A \<Longrightarrow>\<^sub>A B x y * ?C x " 
  apply rotater
  oops

lemma "A \<Longrightarrow>\<^sub>A B * D * E * F"  
  apply rotater
  oops

 


lemma assumes "hn_refine P c Q R a"
    "Q\<Longrightarrow>\<^sub>AQ'*true" shows "hn_refine P c Q' R a"
  apply(rule hn_refine_cons'[OF _ assms]) by (auto simp add: entt_refl') 


text \<open>Weakening the postcondition by converting @{const invalid_assn} to @{term "\<lambda>_ _. true"}\<close>
definition "WEAKEN_HNR_POST \<Gamma> \<Gamma>' \<Gamma>'' \<equiv> (\<exists>h. h\<Turnstile>\<Gamma>) \<longrightarrow> (\<Gamma>'' \<Longrightarrow>\<^sub>t \<Gamma>')"

lemma weaken_hnr_postI:
  assumes "WEAKEN_HNR_POST \<Gamma> \<Gamma>'' \<Gamma>'"
  assumes "hn_refine \<Gamma> c \<Gamma>' R a"
  shows "hn_refine \<Gamma> c \<Gamma>'' R a"
  apply (rule hn_refine_preI)
  apply (rule hn_refine_cons_post)
  apply (rule assms)
  using assms(1) unfolding WEAKEN_HNR_POST_def by blast

lemma weaken_hnr_post_triv: "WEAKEN_HNR_POST \<Gamma> P P"
  unfolding WEAKEN_HNR_POST_def  
  using entt_refl by blast  

lemma weaken_hnr_post:
  "\<lbrakk>WEAKEN_HNR_POST \<Gamma> P P'; WEAKEN_HNR_POST \<Gamma>' Q Q'\<rbrakk> \<Longrightarrow> WEAKEN_HNR_POST (\<Gamma>*\<Gamma>') (P*Q) (P'*Q')"
  "WEAKEN_HNR_POST (hn_ctxt R x y) (hn_ctxt R x y) (hn_ctxt R x y)"
  "WEAKEN_HNR_POST (hn_ctxt R x y) (hn_invalid R x y) (hn_ctxt (\<lambda>_ _. true) x y)"
proof (goal_cases)
  case 1 thus ?case
    unfolding WEAKEN_HNR_POST_def
    apply clarsimp  
  proof -
    fix h :: pheap
    assume a1: "h \<Turnstile> \<Gamma> * \<Gamma>'"
    assume a2: "(\<exists>h. h \<Turnstile> \<Gamma>) \<longrightarrow> (P' \<Longrightarrow>\<^sub>t P)"
    assume a3: "(\<exists>h. h \<Turnstile> \<Gamma>') \<longrightarrow> (Q' \<Longrightarrow>\<^sub>t Q)"
have f4: "\<forall>a. h \<Turnstile> a * (\<Gamma>' * \<up> (h \<Turnstile> \<Gamma> * \<Gamma>')) \<or> (P' \<Longrightarrow>\<^sub>t P)"
  using a2 a1 by (metis (no_types) SepAuto.mod_pure_star_dist assn_times_assoc entailsD' entailsI)
  have f5: "\<forall>b a aa p. p \<Turnstile> aa * a \<or> \<not> p \<Turnstile> aa * (a * \<up> b)"
by (metis (no_types) SepAuto.mod_pure_star_dist assn_times_assoc)
then have f6: "\<forall>b. (P' \<Longrightarrow>\<^sub>t P) \<or> b"
  using f4 by (metis SepAuto.mod_pure_star_dist mult.left_commute)
  then have "h \<Turnstile> \<Gamma> * (\<Gamma>' * \<up> (P' \<Longrightarrow>\<^sub>t P))"
    using a1 by (metis (full_types) SepAuto.mod_pure_star_dist assn_times_assoc)
  then have f7: "Q' \<Longrightarrow>\<^sub>A Q * true"
    using f5 a3 by (metis SepAuto.mod_pure_star_dist entailsD' entailsI entailst_def mult.left_commute)
  have "\<forall>a. true * (a * true) = a * true"
    by (simp add: mult.left_commute)
  then have "P' * Q' \<Longrightarrow>\<^sub>A P * (Q * true)"
using f7 f6 by (metis (no_types) assn_times_assoc ent_star_mono entailst_def)
then show "P' * Q' \<Longrightarrow>\<^sub>t P * Q"
  by (simp add: assn_times_assoc entailst_def)
qed  (* thank you sledgehammer :) *)
next
  case 2 thus ?case by (rule weaken_hnr_post_triv)
next
  case 3 thus ?case 
    unfolding WEAKEN_HNR_POST_def  invalid_assn_def hn_ctxt_def
     
    using assn_times_comm ent_imp_entt entails_pure_post by fastforce   
qed


ML \<open>

  fun weaken_post_tac ctxt = TRADE (fn ctxt =>
    resolve_tac ctxt @{thms weaken_hnr_postI} 
    THEN' SOLVED' (REPEAT_ALL_NEW (DETERM o resolve_tac ctxt @{thms weaken_hnr_post weaken_hnr_post_triv}))
  ) ctxt

\<close>


method_setup weaken_hnr_post = \<open>Scan.succeed (fn ctxt => SIMPLE_METHOD'  (weaken_post_tac ctxt))\<close>
  \<open>Convert "hn_invalid" to "hn_ctxt (\<lambda>_ _. true)" in postcondition of hn_refine goal\<close>


lemma ent_disjE: "\<lbrakk> A\<Longrightarrow>\<^sub>AC; B\<Longrightarrow>\<^sub>AC \<rbrakk> \<Longrightarrow> A\<or>\<^sub>AB \<Longrightarrow>\<^sub>AC"
  unfolding entails_def sorry


lemma merge_true_star_ctx: "true * (true * P) = true * P"
  by (metis assn_times_assoc top_assn_reduce)

lemma pf: "(a::assn) * b = b * a" 
  using assn_times_comm by auto 

lemma ent_true_drop: 
  "P\<Longrightarrow>\<^sub>AQ*true \<Longrightarrow> P*R\<Longrightarrow>\<^sub>AQ*true"
  "P\<Longrightarrow>\<^sub>AQ \<Longrightarrow> P\<Longrightarrow>\<^sub>AQ*true"
  apply (metis assn_times_comm ent_star_mono ent_true merge_true_star_ctx)
  apply (metis assn_one_left ent_star_mono ent_true pf)
  done

lemma hn_monadic_WHILE_aux:
  assumes FR: "P \<Longrightarrow>\<^sub>t \<Gamma> * hn_ctxt Rs s' s"
  assumes b_ref: "\<And>s s'. I s' \<Longrightarrow> hn_refine 
    (\<Gamma> * hn_ctxt Rs s' s)
    (b s)
    (\<Gamma>b s' s)
    (pure bool_rel)
    (b' s')"
  assumes b_fr: "\<And>s' s. \<Gamma>b s' s \<Longrightarrow>\<^sub>t \<Gamma> * hn_ctxt Rs s' s"

  assumes f_ref: "\<And>s' s. \<lbrakk>I s'\<rbrakk> \<Longrightarrow> hn_refine
    (\<Gamma> * hn_ctxt Rs s' s)
    (f s)
    (\<Gamma>f s' s)
    Rs
    (f' s')"
  assumes f_fr: "\<And>s' s. \<Gamma>f s' s \<Longrightarrow>\<^sub>t \<Gamma> * hn_ctxt (\<lambda>_ _. true) s' s"
  (*assumes PREC: "precise Rs"*)
  shows "hn_refine (P) (heap_WHILET b f s) (\<Gamma> * hn_invalid Rs s' s) Rs (monadic_WHILEIT I b' f' s')"
  
  unfolding monadic_WHILEIT_def heap_WHILET_def
  apply1 (rule hn_refine_cons_pre[OF FR]) 
  
  apply weaken_hnr_post

  focus (rule hn_refine_cons_pre[OF _ hnr_RECT])
    applyS (subst mult_ac(2)[of \<Gamma>]; rule entt_refl; fail)

    apply1 (rule hnr_ASSERT)
    focus (rule hnr_bind)
      focus (rule hn_refine_cons[OF _ b_ref b_fr entt_refl])
        applyS (simp add: Ra)
        applyS assumption
      solved  

      focus (rule hnr_If)
        applyS (rule entt_refl)
        focus (rule hnr_bind)
          focus (rule hn_refine_cons[OF _ f_ref f_fr entt_refl])
            subgoal unfolding entailst_def 
              using ent_star_mono entails_triv entails_true by blast 
            apply assumption
          solved
      
          focus (rule hn_refine_frame)
            applyS rprems
            apply  (rule enttI)
            apply(simp add: mult_ac ) 
              apply rotater 
              apply(rule match_first)
              apply(rule match_first)
              apply(rule match_rest) apply simp 
          solved
          
          apply rotatel apply rotatel apply rotater
              apply(rule match_first)  apply rotater
              apply(rule match_rest) apply simp
            solved   
        applyF (auto,rule hn_refine_frame)
          applyS (rule hnr_uRETURN_pass)
          (*apply (tactic {* Sepref_Frame.frame_tac @{context} 1*})*)
          apply (rule enttI)
          apply rotatel  apply rotater  
              apply(rule match_first) apply rotater 
              apply(rule match_rest) apply simp
        solved

        apply (rule entt_refl)
      solved  

            applyF (rule ent_disjE) apply(simp only: hn_ctxt_def)
             apply rotatel apply (rule match_first) apply rotater 
             apply (rule match_rest) apply simp 

            apply(simp only: hn_ctxt_def)

        apply1 (rule ent_true_drop) apply rotatel 
        apply1 (rule match_first) 
             
            apply simp
         
      solved    
    solved
    apply pf_mono
  solved
  done  

(* monotonicity *)
thm bindT_mono

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