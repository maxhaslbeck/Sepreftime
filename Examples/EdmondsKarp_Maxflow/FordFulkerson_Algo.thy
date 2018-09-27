section \<open>The Ford-Fulkerson Method\<close>
theory FordFulkerson_Algo
imports 
  Flow_Networks.Ford_Fulkerson EdmondsKarp_Termination_Abstract
 (*  Maxflow_Lib.Refine_Add_Fofu *)
  "../../Refine_Imperative_HOL/Sepref"
  "../../RefineMonadicVCG"
begin
text \<open>In this theory, we formalize the abstract Ford-Fulkerson
  method, which is independent of how an augmenting path is chosen\<close>

context Network 
begin


(*
context
  fixes find_augmenting_time :: "(nat \<times> nat \<Rightarrow> 'capacity) \<Rightarrow> nat "
  assumes find_augmenting_time_const: "\<And>a b. find_augmenting_time a = find_augmenting_time b"
begin
*)
(* some measure that decreases after each loop of the edmondsKarp algorithm  
  ek_analysis_defs.ekMeasure is a possible? *)
definition R :: "(nat \<times> nat \<Rightarrow> 'capacity) \<Rightarrow> nat" where 
  "R cf = ek_analysis_defs.ekMeasure (residualGraph c cf) s t"

(* upper bound on the runtime of the algorithm for finding an
    augmenting path *)
definition find_augmenting_time :: "(nat \<times> nat \<Rightarrow> 'capacity) \<Rightarrow> nat " where
  "find_augmenting_time f = 10"

definition "special_info f p \<equiv> Graph.isShortestPath (cf_of f) s p t"

lemma ff: "NFlow c s t a \<Longrightarrow>
 \<forall>x. NPreflow.isAugmentingPath c s t a x \<longrightarrow> \<not> special_info a x
   \<Longrightarrow> NPreflow.isAugmentingPath c s t a x \<Longrightarrow> False"  
  using NFlow.augmenting_path_imp_shortest NFlow.shortest_is_augmenting special_info_def by blast
  


text \<open>Select some value with given property, or \<open>None\<close> if there is none.\<close>  
definition SELECT :: "('a \<Rightarrow> bool) \<Rightarrow> enat \<Rightarrow> 'a option nrest"
  where "SELECT P tf \<equiv> if \<exists>x. P x then REST (emb (\<lambda>r. case r of Some p \<Rightarrow> P p | None \<Rightarrow> False) tf)
               else REST [None \<mapsto> tf]"

subsection \<open>Algorithm\<close>
text \<open>
  We abstractly specify the procedure for finding an augmenting path:
  Assuming a valid flow, the procedure must return an augmenting path 
  iff there exists one.
  \<close>
definition "find_augmenting_spec f \<equiv> do {
    ASSERT (NFlow c s t f);
    SELECT (%p. NPreflow.isAugmentingPath c s t f p \<and> special_info f p) (find_augmenting_time f)
  }"

text \<open>Moreover, we specify augmentation of a flow along a path\<close>
definition (in NFlow) "augment_with_path p \<equiv> augment (augmentingFlow p)"
 

lemma R_decreases:
  assumes "NFlow c s t a"
      "NPreflow.isAugmentingPath c s t a x"
      "special_info a x"
  shows "R (NFlow.augment_with_path c a x) < R a"
proof -
  have 2: "Graph.isShortestPath (cf_of a) s x t"
    using assms(3) special_info_def by simp

  show "R (NFlow.augment_with_path c a x) < R a"
  unfolding R_def  
  using NFlow.shortest_path_decr_ek_measure[OF assms(1) 2] 
    NFlow.augment_with_path_def[OF assms(1) ] by auto
qed
    

text \<open>
  We also specify the loop invariant, and annotate it to the loop.
\<close>
abbreviation "fofu_invar \<equiv> \<lambda>(f,brk). 
        NFlow c s t f 
      \<and> (brk \<longrightarrow> (\<forall>p. \<not>NPreflow.isAugmentingPath c s t f p))
    "  

text \<open>Finally, we obtain the Ford-Fulkerson algorithm.
  Note that we annotate some assertions to ease later refinement\<close>
definition "fofu \<equiv> do {
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

fun Te where "Te (f,brk) = (if brk then 0 else find_augmenting_time f * (1+ R f))"


definition "maxFlow_time = enat (find_augmenting_time (\<lambda>_. 0) * (R (\<lambda>_. 0)))"

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


thm NFlow.shortest_path_decr_ek_measure


lemma progress_SELECT_iff: "progress (SELECT P T) \<longleftrightarrow> T > 0"
  unfolding progress_def SELECT_def emb'_def by (auto split: option.splits)

lemmas [progress_rules] = progress_SELECT_iff[THEN iffD2]

theorem fofu_partial_correct: "fofu \<le> SPECT (emb (\<lambda>f. isMaxFlow f) (maxFlow_time))"
  unfolding fofu_def find_augmenting_spec_def 
  apply(rule T_specifies_I)
  apply (vcg'\<open>-\<close>)    

  apply (rule T_conseq4)
   apply (rule whileT_rule'''[OF refl, where I="(\<lambda>e. if fofu_invar e
                then Some (Te e) else None)"])
  subgoal (*progress*) by (progress'\<open>auto simp: find_augmenting_time_def zero_enat_def\<close>)   
    apply (vcg'\<open>-\<close>)  apply(rule TTT_SELECT)   
  subgoal (* no augmenting path *)    
    apply (vcg'\<open>-\<close>) 
    using ff by blast
  subgoal for f brk p (* found augmenting path *)    
    apply (vcg'\<open>-\<close>)
    subgoal unfolding NFlow.augment_with_path_def
      using  NFlow.augment_pres_nflow by metis
    subgoal using NFlow.augmenting_path_not_empty by metis
    subgoal  unfolding find_augmenting_time_def  
      by (simp add: R_decreases less_imp_le_nat)
    subgoal unfolding find_augmenting_time_def   using R_decreases[of "f" "p"] by simp 
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
