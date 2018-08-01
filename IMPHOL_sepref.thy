theory IMPHOL_sepref                             
imports Sepreftime "../Imperative_HOL_Time/SepLogicTime/SepAuto"
begin                                                       

 

text \<open>Straightforward definition of refinement from
      nrest Monad to Imperative HOL (with time!).  \<close>
definition "\<And>T. hn_refineT \<Gamma> c \<Gamma>' R m \<equiv> nofailT m \<longrightarrow> (\<exists>T.
  <\<Gamma> * $T> c <\<lambda>r. \<Gamma>' * (\<exists>\<^sub>Ax. R x r * \<up>(REST [x\<mapsto>T] \<le> m)) >\<^sub>t)" 
(* maybe T should be hidden/existentially quantified *)

lemma "P\<noteq>false \<Longrightarrow> \<not>(<P> c <\<lambda>_. false>)"
  oops
  

lemma "<P> c <\<lambda>r. Q r * \<up>R> \<Longrightarrow> R"
  apply (cases R)
   apply auto
  oops

text \<open>example\<close>
 
declare [[print_trace]]

lemma ent_p: "(b \<Longrightarrow> emp \<Longrightarrow>\<^sub>A P) \<Longrightarrow> (\<up> b \<Longrightarrow>\<^sub>A P)" 
  using entails_pure' by blast  

lemma entails_ex_post': "(P \<Longrightarrow>\<^sub>A Q x) \<Longrightarrow> (P \<Longrightarrow>\<^sub>A (\<exists>\<^sub>Ax. Q x)) " 
  using entails_ex_post by auto 
thm entails_pure_post
lemma entails_pure_post': "P \<Longrightarrow>\<^sub>A Q \<Longrightarrow>  b \<Longrightarrow> (P \<Longrightarrow>\<^sub>A Q * \<up> b)"
  using entails_pure_post by blast 

lemma reor: "\<up> b * true = true * \<up> b"  
  by (simp add: assn_times_comm)
lemma reor2: "\<up> b * \<up> q = \<up> (b \<and> q)"    
  by (simp add: pure_conj)

lemma pullin23: "\<And>P P'.  (\<exists>\<^sub>Ax. P x) * P' = (\<exists>\<^sub>Ax. P x * P') " sorry 

lemma "hn_refineT emp (return 1) emp (\<lambda>x r. emp * \<up>(r=x)) (SPECT [1 \<mapsto> 1])"
  unfolding hn_refineT_def apply auto
  apply(rule exI[where x=1]) 
  apply(rule post_rule)
   apply(rule return_rule)
  apply auto
  apply (auto intro!: ent_p entails_ex_post'   entails_pure_post'  simp: entails_true pullin23 reor reor2 )
  by (auto simp: one_enat_def)

definition "RETURNT1 x = SPECT [x \<mapsto> 1]"
(*

lemma nres_bind_left_identity[simp]: "bindT (RETURNT1 x) f = f x"
  unfolding bindT_def RETURNT_def 
  by(auto split: nrest.split ) 

lemma nres_bind_right_identity[simp]: "bindT M RETURNT = M" 
  by(auto intro!: pw_eqI simp: refine_pw_simps) 

lemma nres_bind_assoc[simp]: "bindT (bindT M (\<lambda>x. f x)) g = bindT M (%x. bindT (f x) g)"
  apply(auto intro!: pw_eqI simp:  refine_pw_simps)  
  using inresT_mono by fastforce+
*)


lemma "hn_refineT emp (return 1) emp (\<lambda>x r. emp * \<up>(r=x)) (SPECT [1 \<mapsto> 1])"
  unfolding hn_refineT_def apply auto
  apply(rule exI[where x=1]) 
  apply(rule post_rule)
   apply(rule return_rule)
  apply auto
 (* apply (auto intro!: ent_p) *)
   by (smt One_nat_def entail_trans2 entails_ex_post entails_pure_post entails_triv entails_true one_enat_def order_mono_setup.refl)
 



text \<open>We tag every refinement assertion with the tag @{text hn_ctxt}, to
  avoid higher-order unification problems when the refinement assertion 
  is schematic.\<close>
definition hn_ctxt :: "('a\<Rightarrow>'c\<Rightarrow>assn) \<Rightarrow> 'a \<Rightarrow> 'c \<Rightarrow> assn" 
  -- {* Tag for refinement assertion *}
  where
  "\<And>P. hn_ctxt P a c \<equiv> P a c"


lemma entailsI: 
  assumes "\<And>h. h\<Turnstile>P \<Longrightarrow> h\<Turnstile>Q"
  shows "P \<Longrightarrow>\<^sub>A Q"            
  using assms unfolding entails_def by auto


lemma mod_star_trueI: "h\<Turnstile>P \<Longrightarrow> h\<Turnstile>P*true"   
  by (metis assn_times_comm entailsD' entails_true mult.left_neutral)

subsubsection \<open>Weak Entails\<close>    
text \<open>Weakening of entails to allow arbitrary unspecified memory in conclusion\<close>
definition entailst :: "assn \<Rightarrow> assn \<Rightarrow> bool" (infix "\<Longrightarrow>\<^sub>t" 10)
  where "entailst A B \<equiv> A \<Longrightarrow>\<^sub>A B * true"

lemma enttI: "A\<Longrightarrow>\<^sub>AB*true \<Longrightarrow> A\<Longrightarrow>\<^sub>tB" unfolding entailst_def .
lemma enttD: "A\<Longrightarrow>\<^sub>tB \<Longrightarrow> A\<Longrightarrow>\<^sub>AB*true" unfolding entailst_def .

lemma entt_refl[simp, intro!]: "entailst A A"
  unfolding entailst_def
  by (simp add: entailsI mod_star_trueI)
 


lemma ent_frame_fwd: fixes P
  assumes R: "P \<Longrightarrow>\<^sub>A R"
  assumes F: "Ps \<Longrightarrow>\<^sub>A P*F"
  assumes I: "R*F \<Longrightarrow>\<^sub>A Q"
  shows "Ps \<Longrightarrow>\<^sub>A Q"
  using assms sorry

term "A \<Longrightarrow>\<^sub>A B"

lemma normalize_rules: "\<And>P. (\<And>x. <P x> f <Q>) \<Longrightarrow> <\<exists>\<^sub>Ax. P x> f <Q>"
  "\<And>P. (b \<Longrightarrow> <P> f <Q>) \<Longrightarrow> <P * \<up> b> f <Q>"
  "(b \<Longrightarrow> <emp> f <Q>) \<Longrightarrow> <\<up> b> f <Q>" sorry

lemma pullin: "\<And>P. <\<exists>\<^sub>Ax. P' * P x> f <Q> \<Longrightarrow> <P' * (\<exists>\<^sub>Ax. P x)> f <Q>" sorry 
lemma pullin2: "\<And>P P'. P' * (\<exists>\<^sub>Ax. P x) = (\<exists>\<^sub>Ax. P' * P x) " sorry 
lemma pullia: "\<And>P. Q * ((\<exists>\<^sub>Ax. P x) * (R::assn)) = (\<exists>\<^sub>Ax. P x) * (Q * (R::assn))" sorry
lemma pullia2: "\<And>P. (Q * (\<exists>\<^sub>Ax. P x)) * (R::assn) = (\<exists>\<^sub>Ax. P x) * (Q * (R::assn))" sorry
lemma pullia3: "\<And>P. (Q * (\<exists>\<^sub>Ax. P x)) * (R::assn) = (Q * (R::assn)) * (\<exists>\<^sub>Ax. P x)" sorry

lemma "\<Gamma>1 * ((\<exists>\<^sub>Axa. Rh xa x * \<up> (SPECT [xa \<mapsto> enat T1] \<le> m)) * (true * $ T2)) = G" 
  apply(simp only: pullia) oops
 
  

lemma "\<Gamma>1 * (\<exists>\<^sub>Axa. Rh xa x * \<up> (SPECT [xa \<mapsto> enat T1] \<le> m)) * true * $ T2 = G" 
  apply(clarsimp simp: pullia3 )  
  apply(clarsimp simp: pullin2) oops

theorem cons_post_rule: "\<And>P. <P> c <Q> \<Longrightarrow> (\<And>x. Q x \<Longrightarrow>\<^sub>A Q' x) \<Longrightarrow> <P> c <Q'>" sorry


lemma bla: "(\<exists>t. inresT (SPECT [x \<mapsto> enat T1]) y t) = (x=y)"
  unfolding inresT_def by auto

lemma aux: "\<And>t::nat. t \<le> T1 + T2 \<Longrightarrow>  \<exists>t'\<le>T1. \<exists>t''\<le>T2. t = t' + t''"
  by presburger

lemma bind_det_aux: "\<lbrakk> SPECT [x \<mapsto> enat T1] \<le> m; SPECT [y \<mapsto> enat T2] \<le> f x \<rbrakk> \<Longrightarrow>  SPECT [y \<mapsto> enat (T1+T2)] \<le> m \<bind> f"
  apply (rule order_trans[rotated])
  apply (rule bindT_mono)
    apply assumption
   apply(simp only: bla)
  apply(simp only: pw_le_iff) apply (auto  simp: refine_pw_simps split: if_splits )   
  using aux by fast+ 


lemma ent_ex_preI: "\<And>P. (\<And>x. P x \<Longrightarrow>\<^sub>A Q) \<Longrightarrow> \<exists>\<^sub>Ax. P x \<Longrightarrow>\<^sub>A Q"
  unfolding entails_def ex_assn_def sorry 

lemma ent_ex_postI: "\<And>P. (P \<Longrightarrow>\<^sub>A Q x) \<Longrightarrow> P \<Longrightarrow>\<^sub>A \<exists>\<^sub>Ax. Q x"
  unfolding entails_def ex_assn_def  sorry

declare [[print_trace]]

(*lemma hnr_bind:
  assumes D1: "hn_refineT \<Gamma> T1 m' \<Gamma>1 Rh m"
  assumes D2: 
    "\<And>x x'. SPECT [x \<mapsto> enat T1] \<le> m \<Longrightarrow> hn_refineT (\<Gamma>1 * hn_ctxt Rh x x') T2 (f' x') (\<Gamma>2 x x') R (f x)"
  assumes IMP: "\<And>x x'. \<Gamma>2 x x' \<Longrightarrow>\<^sub>t \<Gamma>' * hn_ctxt Rx x x'"
  shows "hn_refineT \<Gamma> (T1+T2) (m'\<bind>f') \<Gamma>' R (m\<bind>f)"
  using assms
  unfolding hn_refineT_def
  apply (clarsimp simp add: pw_bindT_nofailT)
  apply(rule SepAuto.bind_rule)
  apply(subst time_credit_add)
  apply(subst assn_times_assoc[symmetric])
  apply(rule frame_rule)
  apply assumption
  apply (clarsimp    simp: hn_ctxt_def)
  apply(clarsimp simp: pullia3 ) apply(clarsimp simp: pullin2) 
  apply(clarsimp intro!: normalize_rules)
  apply(clarsimp simp: assn_times_assoc[symmetric])
  apply(clarsimp intro!: normalize_rules)
proof -
  fix x' x

  have  f: "\<And>r r'. \<Gamma>2 x x' * true * R r' r * \<up> (SPECT [r' \<mapsto> enat T2] \<le> f x)
      = \<Gamma>2 x x' * (true * R r' r * \<up> (SPECT [r' \<mapsto> enat T2] \<le> f x))"
     by (simp add: assn_times_assoc) 

  assume 1: "SPECT [x \<mapsto> enat T1] \<le> m" 
    and "nofailT m" "\<forall>x. (\<exists>t. inresT m x t)  \<longrightarrow> nofailT (f x)"
  hence "nofailT (f x)"   by (auto simp: pw_le_iff split: if_splits)
  moreover assume "\<And>x x'. SPECT [x \<mapsto> enat T1] \<le> m \<Longrightarrow>
           nofailT (f x) \<longrightarrow> <\<Gamma>1 * Rh x x' * $ T2> f' x'
           <\<lambda>r'. \<exists>\<^sub>Ar. \<Gamma>2 x x' * true * R r r' * \<up> (SPECT [r \<mapsto> enat T2] \<le> f x)>"
  ultimately have "\<And>x'. <\<Gamma>1 * Rh x x'* $ T2> f' x'
           <\<lambda>r'. \<exists>\<^sub>Ar. \<Gamma>2 x x' * true * R r r' * \<up> (SPECT [r \<mapsto> enat T2] \<le> f x)>"
    using 1 by simp
  also
  have "\<And>r'. \<exists>\<^sub>Ar. \<Gamma>2 x x' * true * R r r' * \<up> (SPECT [r \<mapsto> enat T2] \<le> f x) \<Longrightarrow>\<^sub>A
    \<exists>\<^sub>Ar. \<Gamma>' * R r r' * true * \<up> (SPECT [r \<mapsto> enat T2] \<le> f x)" 
    apply(intro ent_ex_preI )
    subgoal for r r'
    apply(intro ent_ex_postI[where x=r'])   
      apply(rule ent_frame_fwd[OF IMP[THEN enttD]]) 
      unfolding f
       apply(rule entails_frame[where R="true * R r' r * \<up> (SPECT [r' \<mapsto> enat T2] \<le> f x)"])
       apply(rule entails_triv)
      by auto2
    done
  finally (cons_post_rule) have 
    R: "<\<Gamma>1 * Rh x x' * $T2> f' x' 
        <\<lambda>r'. \<exists>\<^sub>Ar. \<Gamma>' * R r r' * true * \<up>(SPECT [r \<mapsto> enat T2] \<le> f x)>"
    .
  have g: "\<Gamma>1 * true * $ T2 * Rh x x' = (\<Gamma>1   * Rh x x' * $ T2) * true"  
    using assn_times_assoc assn_times_comm by auto 

  show "<\<Gamma>1 * true * $ T2 * Rh x x'> f' x'
          <\<lambda>r. \<exists>\<^sub>Ax. \<Gamma>' * true * R x r * \<up> (SPECT [x \<mapsto> enat (T1 + T2)] \<le> m \<bind> f)>"
    unfolding g
    apply(rule post_rule) 
     apply(rule frame_rule) 
     apply(rule R) 
    apply(simp add: pullin23)
    apply safe 
    apply(intro ent_ex_preI )
    subgoal for r r'
    apply(intro ent_ex_postI[where x=r']) 
      using bind_det_aux[OF 1]  
      by (smt assn_times_comm entails_def mod_pure_star_dist mult.left_commute top_assn_reduce)
    done
qed
*)

lemma hnr_bind:
  assumes D1: "hn_refineT \<Gamma>  m' \<Gamma>1 Rh m"
  assumes D2: 
    "\<And>x x'. RETURNT  x \<le> m \<Longrightarrow> hn_refineT (\<Gamma>1 * hn_ctxt Rh x x')  (f' x') (\<Gamma>2 x x') R (f x)"
  assumes IMP: "\<And>x x'. \<Gamma>2 x x' \<Longrightarrow>\<^sub>t \<Gamma>' * hn_ctxt Rx x x'" 
  shows "hn_refineT \<Gamma> (m'\<bind>f') \<Gamma>' R (m\<bind>f)"  
  using assms
  unfolding hn_refineT_def
  apply (clarsimp simp add: pw_bindT_nofailT)
  subgoal for T1 
    apply rule 
  apply(rule SepAuto.bind_rule)
  apply(subst time_credit_add)
  apply(subst assn_times_assoc[symmetric])
  apply(rule frame_rule)
  apply assumption
  apply (clarsimp    simp: hn_ctxt_def)
  apply(clarsimp simp: pullia3 ) apply(clarsimp simp: pullin2) 
  apply(clarsimp intro!: normalize_rules)
  apply(clarsimp simp: assn_times_assoc[symmetric])
  apply(clarsimp intro!: normalize_rules)
proof -
  fix x' x
    

  assume 1: "SPECT [x \<mapsto> enat T1] \<le> m" 
    and "nofailT m" "\<forall>x. (\<exists>t. inresT m x t)  \<longrightarrow> nofailT (f x)"
  hence "nofailT (f x)" "RETURNT x \<le> m"   by (auto simp: pw_le_iff split: if_splits)
  moreover assume "\<And>x x'. RETURNT x \<le> m \<Longrightarrow>
           nofailT (f x) \<longrightarrow> (\<exists>T2.  <\<Gamma>1 * Rh x x' * $ T2> f' x'
           <\<lambda>r'. \<exists>\<^sub>Ar. \<Gamma>2 x x' * true * R r r' * \<up> (SPECT [r \<mapsto> enat T2] \<le> f x)>)"
  ultimately have "\<And>x'. \<exists>T2. <\<Gamma>1 * Rh x x'* $ T2> f' x'
           <\<lambda>r'. \<exists>\<^sub>Ar. \<Gamma>2 x x' * true * R r r' * \<up> (SPECT [r \<mapsto> enat T2] \<le> f x)>"
    by simp
  then obtain T2 where "<\<Gamma>1 * Rh x x'* $ T2> f' x'
           <\<lambda>r'. \<exists>\<^sub>Ar. \<Gamma>2 x x' * true * R r r' * \<up> (SPECT [r \<mapsto> enat T2] \<le> f x)>" by auto
  also


  have  f: "\<And>r r'. \<Gamma>2 x x' * true * R r' r * \<up> (SPECT [r' \<mapsto> enat T2] \<le> f x)
      = \<Gamma>2 x x' * (true * R r' r * \<up> (SPECT [r' \<mapsto> enat T2] \<le> f x))"
     by (simp add: assn_times_assoc) 

   have k: "RETURNT x \<le> SPECT [x \<mapsto> enat T1]" unfolding RETURNT_def apply auto   
     by (simp add:  le_fun_def)

  have "\<And>r'. \<exists>\<^sub>Ar. \<Gamma>2 x x' * true * R r r' * \<up> (SPECT [r \<mapsto> enat T2] \<le> f x) \<Longrightarrow>\<^sub>A
    \<exists>\<^sub>Ar. \<Gamma>' * R r r' * true * \<up> (SPECT [r \<mapsto> enat T2] \<le> f x)" 
    apply(intro ent_ex_preI )
    subgoal for r r'
    apply(intro ent_ex_postI[where x=r'])   
      apply(rule ent_frame_fwd[OF IMP[THEN enttD]]) 
      unfolding f
       apply(rule entails_frame[where R="true * R r' r * \<up> (SPECT [r' \<mapsto> enat T2] \<le> f x)"])
       apply(rule entails_triv)
      by auto2
    done
  finally (cons_post_rule) have 
    R: "<\<Gamma>1 * Rh x x' * $T2> f' x' 
        <\<lambda>r'. \<exists>\<^sub>Ar. \<Gamma>' * R r r' * true * \<up>(SPECT [r \<mapsto> enat T2] \<le> f x)>"
    .
  have g: "\<Gamma>1 * true * $ T2 * Rh x x' = (\<Gamma>1   * Rh x x' * $ T2) * true"  
    using assn_times_assoc assn_times_comm by auto 

  have "<\<Gamma>1 * true * $ T2 * Rh x x'> f' x'
          <\<lambda>r. \<exists>\<^sub>Ax. \<Gamma>' * true * R x r * \<up> (SPECT [x \<mapsto> enat (T1 + T2)] \<le> m \<bind> f)>"
    unfolding g
    apply(rule post_rule) 
     apply(rule frame_rule) 
     apply(rule R) 
    apply(simp add: pullin23)
    apply safe 
    apply(intro ent_ex_preI )
    subgoal for r r'
    apply(intro ent_ex_postI[where x=r']) 
      using bind_det_aux[OF 1]  
      by (smt assn_times_comm entails_def mod_pure_star_dist mult.left_commute top_assn_reduce)
    done 
       show "<\<Gamma>1 * true * $ T2 * Rh x x'> f' x' <\<lambda>r. \<exists>\<^sub>Ax. \<Gamma>' * true * R x r * \<up> (SPECT [x \<mapsto> enat (T1 + T2)] \<le> m \<bind> f)>"
  qed 

lemma hnr_frame: fixes P T
  assumes "hn_refineT P'  c Q' R m"
  assumes "P \<Longrightarrow>\<^sub>t F * P'"
  shows "hn_refineT P  c (F * Q') R m"
  using assms
  unfolding hn_refineT_def entailst_def
  apply clarsimp  (*
  apply (erule cons_pre_rule)
  apply (rule cons_post_rule)
  apply (erule fi_rule, frame_inference)
  apply (simp only: star_aci)
  apply simp
  done *)
sorry

lemma hnr_cons: 
  assumes I: "P\<Longrightarrow>\<^sub>tP'"
  assumes R: "hn_refineT P'  c Q R m"
  assumes I': "Q\<Longrightarrow>\<^sub>tQ'"
  assumes R': "\<And>x y. R x y \<Longrightarrow>\<^sub>t R' x y"
  shows "hn_refineT P  c Q' R' m"
  sorry


lemma hn_refineI[intro?]: fixes T
  assumes "nofailT m 
    \<Longrightarrow> (\<exists>T. <\<Gamma> * $ T> c <\<lambda>r. \<Gamma>' * (\<exists>\<^sub>Ax. R x r * \<up> (SPECT [x \<mapsto> enat T] \<le> m))>\<^sub>t)"
  shows "hn_refineT \<Gamma>   c \<Gamma>' R m"
  using assms unfolding hn_refineT_def by blast

lemma hn_refineD: fixes T
  assumes "hn_refineT \<Gamma> c \<Gamma>' R m"
  assumes "nofailT  m"
  shows "(\<exists>T. <\<Gamma> * $ T> c <\<lambda>r. \<Gamma>' * (\<exists>\<^sub>Ax. R x r * \<up> (SPECT [x \<mapsto> enat T] \<le> m))>\<^sub>t)"
  using assms unfolding hn_refineT_def by blast

lemma hnr_ref: fixes P T
  assumes LE: "m\<le>m'"
  assumes R: "hn_refineT P  c Q R m"
  shows "hn_refineT P  c Q R m'"
  apply rule  (*
  apply (rule cons_post_rule)
  apply (rule hn_refineD[OF R])
  using LE apply (simp add: pw_le_iff)
  using LE apply auto2 
  done *) sorry


lemma hn_refineT_cons_complete: fixes P T
  assumes I: "P\<Longrightarrow>\<^sub>tP'"
  assumes R: "hn_refineT P' c Q R m"
  assumes I': "Q\<Longrightarrow>\<^sub>tQ'"
  assumes R': "\<And>x y. R x y \<Longrightarrow>\<^sub>t R' x y"
  assumes LE: "m\<le>m'"
  shows "hn_refineT P  c Q' R' m'"
  apply (rule hnr_ref[OF LE])
  apply (rule hnr_cons[OF I R I' R'])
  done





end