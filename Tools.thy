theory Tools
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



subsection "Rotate method"

definition gr where "gr A B = A * B"

lemma right_swap: "(A \<Longrightarrow>\<^sub>A B * (C * D)) \<Longrightarrow> (A \<Longrightarrow>\<^sub>A B * (D * C))"
  by (simp add: assn_times_comm)
lemma right_take: "(A \<Longrightarrow>\<^sub>A gr B C * D) \<Longrightarrow> (A \<Longrightarrow>\<^sub>A B * (C * D))"
  by (simp add: gr_def assn_times_assoc) 
lemma left_swap: "(B * (C * D) \<Longrightarrow>\<^sub>A A) \<Longrightarrow> (B * (D * C) \<Longrightarrow>\<^sub>A A)"
  by (simp add: assn_times_comm)
lemma left_take: "(gr B C * D \<Longrightarrow>\<^sub>A A) \<Longrightarrow> (B * (C * D) \<Longrightarrow>\<^sub>A A)"
  by (simp add: gr_def assn_times_assoc) 

lemma right_move_back: "(A \<Longrightarrow>\<^sub>A B * C) \<Longrightarrow> (A \<Longrightarrow>\<^sub>A C * B)"
  by (simp add: assn_times_comm)
lemma left_move_back: "(B * C \<Longrightarrow>\<^sub>A A) \<Longrightarrow> (C * B \<Longrightarrow>\<^sub>A A)"
  by (simp add: assn_times_comm)

thm mult.assoc
method rotater = ( (simp only: mult.assoc)? , rule right_move_back , (simp only: mult.assoc)?  )
method rotatel = ( (simp only: mult.assoc)? , rule left_move_back , (simp only: mult.assoc)?  )

method swapl = ( (simp only: mult.assoc)? ,rule left_swap, (simp only: mult.assoc)?   )
method takel = ( (simp only: mult.assoc)? , rule left_take, (simp only: mult.assoc)?  )

method swapr = ( (simp only: mult.assoc)? , rule right_swap , (simp only: mult.assoc)?  )
method taker = ( (simp only: mult.assoc)? , rule right_take, (simp only: mult.assoc)?  )


lemma "\<And>x y. A \<Longrightarrow>\<^sub>A B x y * C"
  apply rotater
  oops
 
schematic_goal "\<And>x y. A \<Longrightarrow>\<^sub>A B x y * ?C x " 
  apply rotater
  oops

lemma "A \<Longrightarrow>\<^sub>A B * D * E * F"  
  apply swapr
  oops
lemma "A \<Longrightarrow>\<^sub>A B * D * E * F"  
  apply rotater
  oops

lemma pull_forward: "(A \<Longrightarrow>\<^sub>A B * C * D) \<Longrightarrow> (A \<Longrightarrow>\<^sub>A B * (C * D))"
  by (simp add: mult.assoc)

lemma match_first: "A \<Longrightarrow>\<^sub>A B \<Longrightarrow> \<Gamma> * A \<Longrightarrow>\<^sub>A \<Gamma> * B"  
  by (simp add: assn_times_comm entails_frame)  

lemma match_rest: "emp \<Longrightarrow>\<^sub>A B \<Longrightarrow> \<Gamma> \<Longrightarrow>\<^sub>A \<Gamma> * B"  
  using match_first by fastforce 



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

lemma ent_iffI:
  assumes "A\<Longrightarrow>\<^sub>AB"
  assumes "B\<Longrightarrow>\<^sub>AA"
  shows "A=B" 
  using assms  assn_ext entails_def by blast

lemma hn_invalidI: "h\<Turnstile>hn_ctxt P x y \<Longrightarrow> hn_invalid P x y = true"
  apply (cases h)
  apply (rule ent_iffI)
  apply (auto simp: invalid_assn_def hn_ctxt_def) 
  using assn_times_comm entails_pure_post by fastforce 

lemma mod_starD: "h\<Turnstile>A*B \<Longrightarrow> \<exists>h1 h2. h1\<Turnstile>A \<and> h2\<Turnstile>B"
  by (metis assn_times_comm entailsD' entails_def mod_false')

method extract_hnr_invalids = (
  rule hn_refine_preI,
  ((drule mod_starD hn_invalidI | elim conjE exE)+)?
) \<comment> \<open>Extract \<open>hn_invalid _ _ _ = true\<close> preconditions from \<open>hn_refine\<close> goal.\<close>
  


method_setup weaken_hnr_post = \<open>Scan.succeed (fn ctxt => SIMPLE_METHOD'  (weaken_post_tac ctxt))\<close>
  \<open>Convert "hn_invalid" to "hn_ctxt (\<lambda>_ _. true)" in postcondition of hn_refine goal\<close>



subsection "refine setup"

ML \<open>
  structure refine = Named_Thms
    ( val name = @{binding refine}
      val description = "Refinement Framework: Refinement rules (intro)" )\<close>

ML {*
structure Refine = struct

  structure vcg = Named_Thms
    ( val name = @{binding refine_vcg}
      val description = "Refinement Framework: " ^ 
        "Verification condition generation rules (intro)" )

  structure vcg_cons = Named_Thms
    ( val name = @{binding refine_vcg_cons}
      val description = "Refinement Framework: " ^
        "Consequence rules tried by VCG" )

  structure refine0 = Named_Thms
    ( val name = @{binding refine0}
      val description = "Refinement Framework: " ^
        "Refinement rules applied first (intro)" )

  structure refine = Named_Thms
    ( val name = @{binding refine}
      val description = "Refinement Framework: Refinement rules (intro)" )

  structure refine2 = Named_Thms
    ( val name = @{binding refine2}
      val description = "Refinement Framework: " ^
        "Refinement rules 2nd stage (intro)" )

  (* If set to true, the product splitter of refine_rcg is disabled. *)
  val no_prod_split = 
    Attrib.setup_config_bool @{binding refine_no_prod_split} (K false);

  fun rcg_tac add_thms ctxt = 
    let 
      val cons_thms = vcg_cons.get ctxt
      val ref_thms = (refine0.get ctxt 
        @ add_thms @ refine.get ctxt @ refine2.get ctxt);
      val prod_ss = (Splitter.add_split @{thm prod.split} 
        (put_simpset HOL_basic_ss ctxt));
      val prod_simp_tac = 
        if Config.get ctxt no_prod_split then 
          K no_tac
        else
          (simp_tac prod_ss THEN' 
            REPEAT_ALL_NEW (resolve_tac ctxt @{thms impI allI}));
    in
      REPEAT_ALL_NEW_FWD (DETERM o FIRST' [
        resolve_tac ctxt ref_thms,
        resolve_tac ctxt cons_thms THEN' resolve_tac ctxt ref_thms,
        prod_simp_tac
      ])
    end;

  fun post_tac ctxt = REPEAT_ALL_NEW_FWD (FIRST' [
    eq_assume_tac,
    (*match_tac ctxt thms,*)
    SOLVED' (Tagged_Solver.solve_tac ctxt)]) 
         

end;
*}
setup {* Refine.vcg.setup *}
setup {* Refine.vcg_cons.setup *}
setup {* Refine.refine0.setup *}
setup {* Refine.refine.setup *}
setup {* Refine.refine2.setup *}


end