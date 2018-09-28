section \<open>The Ford-Fulkerson Method\<close>
theory FordFulkerson_Algo
imports 
  Flow_Networks.Ford_Fulkerson EdmondsKarp_Termination_Abstract
 (*  Maxflow_Lib.Refine_Add_Fofu *)
  "../../Refine_Imperative_HOL/Sepref"
  "../../RefineMonadicVCG"
begin

(* TODO: MOVE *)

text \<open>Select some value with given property, or \<open>None\<close> if there is none.\<close>  
definition SELECT :: "('a \<Rightarrow> bool) \<Rightarrow> enat \<Rightarrow> 'a option nrest"
  where "SELECT P tf \<equiv> if \<exists>x. P x then REST (emb (\<lambda>r. case r of Some p \<Rightarrow> P p | None \<Rightarrow> False) tf)
               else REST [None \<mapsto> tf]"

                    
lemma inresT_SELECT_Some: "inresT (SELECT Q tt) (Some x) t' \<longleftrightarrow> (Q x  \<and> (t' \<le> tt))"
  by(auto simp: inresT_def SELECT_def emb'_def) 

lemma inresT_SELECT_None: "inresT (SELECT Q tt) None t' \<longleftrightarrow> (\<not>(\<exists>x. Q x) \<and> (t' \<le> tt))"
  by(auto simp: inresT_def SELECT_def emb'_def) 

lemma inresT_SELECT[refine_pw_simps]:
 "inresT (SELECT Q tt) x t' \<longleftrightarrow> ((case x of None \<Rightarrow> \<not>(\<exists>x. Q x) | Some x \<Rightarrow> Q x)  \<and> (t' \<le> tt))"
  by(auto simp: inresT_def SELECT_def emb'_def) 


lemma nofailT_SELECT[refine_pw_simps]: "nofailT (SELECT Q tt)"
  by(auto simp: nofailT_def SELECT_def)

lemma s1: "SELECT P T \<le> (SELECT P T') \<longleftrightarrow> T \<le> T'"
  apply(cases "\<exists>x. P x") 
   apply(auto simp: pw_le_iff refine_pw_simps split: option.splits)
  subgoal 
    by (metis (full_types) enat_ord_code(3) enat_ord_simps(1) lessI not_infinity_eq not_le order_mono_setup.refl) 
  subgoal 
    by (metis (full_types) enat_ord_code(3) enat_ord_simps(1) lessI not_enat_eq not_le order_mono_setup.refl) 
  done
     
lemma s2: "SELECT P T \<le> (SELECT P' T) \<longleftrightarrow> (
    (Ex P' \<longrightarrow> Ex P)  \<and> (\<forall>x. P x \<longrightarrow> P' x)) "
  apply(auto simp: pw_le_iff refine_pw_simps split: option.splits)
  subgoal 
    by (metis enat_ile linear)                                          
  subgoal 
    by (metis enat_ile linear) 
  done
 
lemma SELECT_refine:
  assumes "\<And>x'. P' x' \<Longrightarrow> \<exists>x. P x"
  assumes "\<And>x. P x \<Longrightarrow>   P' x"
  assumes "T \<le> T'"
  shows "SELECT P T \<le> (SELECT P' T')"
proof -
  have "SELECT P T \<le> SELECT P T'"
    using s1 assms(3) by auto
  also have "\<dots> \<le> SELECT P' T'"
    unfolding s2 apply safe
    using assms(1,2) by auto  
  finally show ?thesis .
qed


lemma TTT_SELECT: 
  assumes  
    "\<forall>x. \<not> P x \<Longrightarrow> Some tt \<le> TTT Q (SPECT [None \<mapsto> tf])"
  and p: "(\<And>x. P x \<Longrightarrow> Some tt \<le> TTT Q (SPECT [Some x \<mapsto> tf]))"
   shows "Some tt \<le> TTT Q (SELECT P tf)"
proof(cases "\<exists>x. P x")
  case True
  from p[unfolded T_pw mii_alt] have
    p': "\<And>y x. P y \<Longrightarrow> Some tt \<le> mm2 (Q x)([Some y \<mapsto> tf] x)"
    by auto

  from True 
  show ?thesis 
    unfolding SELECT_def apply (auto simp: emb'_def split: if_splits)
    apply(auto simp: T_pw) subgoal for x xa apply(cases xa)
      apply (simp add: mii_alt)
      apply (simp add: mii_alt) apply safe subgoal for a
        using p'[of a xa] by auto
      done
    done
next
  case False
  then show ?thesis 
    unfolding SELECT_def apply (auto simp: emb'_def split: if_splits) using assms by auto
qed 

lemma progress_SELECT_iff: "progress (SELECT P T) \<longleftrightarrow> T > 0"
  unfolding progress_def SELECT_def emb'_def by (auto split: option.splits)

lemmas [progress_rules] = progress_SELECT_iff[THEN iffD2]



lemma case_prod_refine:
  fixes P Q :: "'a \<Rightarrow> 'b \<Rightarrow> 'c nrest"
  assumes
    "\<And>a b. P a b \<le> Q a b"
  shows
 "(case x of (a,b) \<Rightarrow> P a b) \<le> (case x of (a,b) \<Rightarrow> Q a b)"
  using assms 
  by (simp add: split_def)

lemma case_option_refine:
  fixes P Q :: "'a \<Rightarrow> 'b \<Rightarrow> 'c nrest"
  assumes
    "PN \<le> QN"
    "\<And>a. PS a \<le> QS a"
  shows
 "(case x of None \<Rightarrow> PN | Some a \<Rightarrow> PS a ) \<le> (case x of None \<Rightarrow> QN | Some a \<Rightarrow> QS a )"
  using assms 
  by (auto split: option.splits)

lemma ASSERT_refine: "(Q \<Longrightarrow> P) \<Longrightarrow> ASSERT P \<le> ASSERT Q"
  by(auto simp: pw_le_iff refine_pw_simps)

lemma ASSERT_leI: "\<Phi> \<Longrightarrow> (\<Phi> \<Longrightarrow> M \<le> M') \<Longrightarrow> ASSERT \<Phi> \<bind> (\<lambda>_. M) \<le> M'"
  by(auto simp: pw_le_iff refine_pw_simps)

lemma le_ASSERTI: "(\<Phi> \<Longrightarrow> M \<le> M') \<Longrightarrow> M \<le> ASSERT \<Phi> \<bind> (\<lambda>_. M')"
  by(auto simp: pw_le_iff refine_pw_simps)

lemma inresT_ASSERT: "inresT (ASSERT Q \<bind> (\<lambda>_. M)) x ta = (Q \<longrightarrow> inresT M x ta)"
  unfolding ASSERT_def iASSERT_def by auto


lemma nofailT_ASSERT_bind: "nofailT (ASSERT P \<bind> (\<lambda>_. M)) \<longleftrightarrow> (P \<and> nofailT M)"
  by(auto simp: pw_bindT_nofailT pw_ASSERT)




text \<open>In this theory, we formalize the abstract Ford-Fulkerson
  method, which is independent of how an augmenting path is chosen\<close>






(*


lemma (in FoFu) R_decreases:
  assumes "NFlow c s t a"
      "NPreflow.isAugmentingPath c s t a x"
      "special_info c s t a x"
  shows "R (NFlow.augment_with_path c a x) < R a"
proof -
  have 2: "Graph.isShortestPath (cf_of a) s x t"
    using assms(3)  by simp

  show "R (NFlow.augment_with_path c a x) < R a"
  unfolding R_def  
  using NFlow.shortest_path_decr_ek_measure[OF assms(1) 2] 
    NFlow.augment_with_path_def[OF assms(1) ] by auto
qed 

*)

text \<open>We specify augmentation of a flow along a path\<close>
definition (in NFlow) "augment_with_path p \<equiv> augment (augmentingFlow p)"
 
locale FoFu = Network c s t for c :: "'capacity::linordered_idom graph" and s t +
  fixes  R :: "(nat \<times> nat \<Rightarrow> 'capacity) \<Rightarrow> nat"
     and   find_augmenting_time :: "nat "
     and special_info :: "(nat \<times> nat \<Rightarrow> 'capacity) \<Rightarrow> (nat \<times> nat) list \<Rightarrow> bool"
   assumes ff: "NFlow c s t a \<Longrightarrow>
 \<forall>x. \<not> special_info a x
   \<Longrightarrow> NPreflow.isAugmentingPath c s t a x \<Longrightarrow> False"  

  and R_decreases: "NFlow c s t a \<Longrightarrow> special_info a x \<Longrightarrow> R (NFlow.augment_with_path c a x) < R a"

  and fat_g_0: "\<And>x. find_augmenting_time  > 0"

  and augments: "\<And>p f.  NFlow c s t f \<Longrightarrow> special_info f p \<Longrightarrow> NPreflow.isAugmentingPath c s t f p"


context Network 
begin

(*
context
  fixes find_augmenting_time :: "(nat \<times> nat \<Rightarrow> 'capacity) \<Rightarrow> nat "
  assumes find_augmenting_time_const: "\<And>a b. find_augmenting_time a = find_augmenting_time b"
begin
*)
(* some measure that decreases after each loop of the edmondsKarp algorithm  
  ek_analysis_defs.ekMeasure is a possible?  
definition R :: "(nat \<times> nat \<Rightarrow> 'capacity) \<Rightarrow> nat" where 
  "R cf = ek_analysis_defs.ekMeasure (residualGraph c cf) s t"

(* upper bound on the runtime of the algorithm for finding an
    augmenting path
definition  where
  "find_augmenting_time f = 10"

definition "special_info f p \<equiv> Graph.isShortestPath (cf_of f) s p t"

lemma ff: "NFlow c s t a \<Longrightarrow>
 \<forall>x. NPreflow.isAugmentingPath c s t a x \<longrightarrow> \<not> special_info a x
   \<Longrightarrow> NPreflow.isAugmentingPath c s t a x \<Longrightarrow> False"  
  using NFlow.augmenting_path_imp_shortest NFlow.shortest_is_augmenting special_info_def by blast
  
 *) *)

subsection \<open>Algorithm\<close>
text \<open>
  We abstractly specify the procedure for finding an augmenting path:
  Assuming a valid flow, the procedure must return an augmenting path 
  iff there exists one.
  \<close>
definition (in FoFu) "find_augmenting_spec f \<equiv> do {
    ASSERT (NFlow c s t f);
    SELECT (%p. (* NPreflow.isAugmentingPath c s t f p \<and> *) special_info f p) (find_augmenting_time)
  }"



    

text \<open>
  We also specify the loop invariant, and annotate it to the loop.
\<close>
abbreviation "fofu_invar \<equiv> \<lambda>(f,brk). 
        NFlow c s t f 
      \<and> (brk \<longrightarrow> (\<forall>p. \<not>NPreflow.isAugmentingPath c s t f p))
    "  

text \<open>Finally, we obtain the Ford-Fulkerson algorithm.
  Note that we annotate some assertions to ease later refinement\<close>
definition (in FoFu) "fofu \<equiv> do {
  f\<^sub>0 \<leftarrow> RETURNT (\<lambda>_. 0);

  (f,_) \<leftarrow> whileT(*\<^bsup>fofu_invar\<^esup>*)
    (\<lambda>(f,brk). \<not>brk) 
    (\<lambda>(f,_). do {
      p \<leftarrow> find_augmenting_spec f;
      case p of 
        None \<Rightarrow> RETURNT (f,True)
      | Some p \<Rightarrow> do {
          ASSERT (p\<noteq>[]);
          ASSERT (NPreflow.isAugmentingPath c s t f p);
          f \<leftarrow> RETURNT ( NFlow.augment_with_path c f p );
          ASSERT (NFlow c s t f);
          RETURNT (f, False)
        }  
    })
    (f\<^sub>0,False);
  ASSERT (NFlow c s t f);
  RETURNT f 
}"

subsection \<open>Partial Correctness\<close>
text \<open>Correctness of the algorithm is a consequence from the 
  Ford-Fulkerson theorem. We need a few straightforward 
  auxiliary lemmas, though:
\<close>

text \<open>The zero flow is a valid flow\<close>
lemma zero_flow: "NFlow c s t (\<lambda>_. 0)" 
  apply unfold_locales
  by (auto simp: s_node t_node cap_non_negative)  

text \<open>Augmentation preserves the flow property\<close>
lemma (in NFlow) augment_pres_nflow:
  assumes AUG: "isAugmentingPath p"
  shows "NFlow c s t (augment (augmentingFlow p))"
proof -
  from augment_flow_presv[OF augFlow_resFlow[OF AUG]]
  interpret f': Flow c s t "augment (augmentingFlow p)" .
  show ?thesis by intro_locales
qed    

text \<open>Augmenting paths cannot be empty\<close>
lemma (in NFlow) augmenting_path_not_empty:
  "\<not>isAugmentingPath []"
  unfolding isAugmentingPath_def using s_not_t by auto



text \<open>Finally, we can use the verification condition generator to
  show correctness\<close>

fun (in FoFu) Te where "Te (f,brk) = (if brk then 0 else find_augmenting_time  * (1+ R f))"


definition (in FoFu) "maxFlow_time = enat (find_augmenting_time * (R (\<lambda>_. 0) + 1)) "


theorem (in FoFu)  fofu_partial_correct: "fofu \<le> SPECT (emb (\<lambda>f. isMaxFlow f) (maxFlow_time))"
  unfolding fofu_def find_augmenting_spec_def 
  apply(rule T_specifies_I)
  apply (vcg'\<open>-\<close>)    

  apply (rule T_conseq4)
   apply (rule whileT_rule'''[OF refl, where I="(\<lambda>e. if fofu_invar e
                then Some (Te e) else None)"])
  subgoal (*progress*) by (progress'\<open>auto simp: fat_g_0 zero_enat_def\<close>)   
    apply (vcg'\<open>-\<close>)  apply(rule TTT_SELECT)   
  subgoal (* no augmenting path *)    
    apply (vcg'\<open>-\<close>) 
    using ff by blast
  subgoal for f brk p (* found augmenting path *)    
    apply (vcg'\<open>-\<close>)
    subgoal unfolding NFlow.augment_with_path_def
      using  NFlow.augment_pres_nflow augments by metis
    subgoal using NFlow.augmenting_path_not_empty augments  by metis
    subgoal  using  augments by simp 
    subgoal 
      by (simp add: R_decreases less_imp_le_nat)
    subgoal by (metis R_decreases diff_mult_distrib2 prod_ineqs2 zero_less_diff)
  done
  apply (auto simp: zero_flow)
  apply (vcg'\<open>-\<close>)
  subgoal using 
    NFlow.noAugPath_iff_maxFlow[symmetric] by blast
  subgoal unfolding maxFlow_time_def by auto
  done 
(*
subsection \<open>Algorithm without Assertions\<close>
text \<open>For presentation purposes, we extract a version of the algorithm
  without assertions, and using a bit more concise notation\<close>

context begin

private abbreviation (input) "augment 
  \<equiv> NFlow.augment_with_path"
private abbreviation (input) "is_augmenting_path f p 
  \<equiv> NPreflow.isAugmentingPath c s t f p"

text \<open> {} \<close>
text_raw \<open>\DefineSnippet{ford_fulkerson_algo}{\<close>       
definition "ford_fulkerson_method \<equiv> do {
  let f\<^sub>0 = (\<lambda>(u,v). 0);

  (f,brk) \<leftarrow> while (\<lambda>(f,brk). \<not>brk) 
    (\<lambda>(f,brk). do {
      p \<leftarrow> select p. is_augmenting_path f p;
      case p of 
        None \<Rightarrow> return (f,True)
      | Some p \<Rightarrow> return (augment c f p, False)
    })
    (f\<^sub>0,False);
  return f 
}"
text_raw \<open>}%EndSnippet\<close>

text \<open> {} \<close>

end \<comment> \<open>Anonymous context\<close> *)
end \<comment> \<open>Network\<close> 
(*
text \<open> {} \<close>
text_raw \<open>\DefineSnippet{ford_fulkerson_correct}{\<close>       
theorem (in Network) "ford_fulkerson_method \<le> (spec f. isMaxFlow f)"
text_raw \<open>}%EndSnippet\<close>
text \<open> {} \<close>
proof -
  have [simp]: "(\<lambda>(u,v). 0) = (\<lambda>_. 0)" by auto
  have "ford_fulkerson_method \<le> fofu"
    unfolding ford_fulkerson_method_def fofu_def Let_def find_augmenting_spec_def
    apply (rule refine_IdD)
    apply (refine_vcg)
    apply (refine_dref_type)
    apply (vc_solve simp: NFlow.augment_with_path_def solve: exI)
    done
  also note fofu_partial_correct  
  finally show ?thesis .
qed  
*)
end \<comment> \<open>Theory\<close>
