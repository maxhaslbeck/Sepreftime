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


text \<open>We specify augmentation of a flow along a path\<close>
definition (in NFlow) "augment_with_path p \<equiv> augment (augmentingFlow p)"
 
locale FoFu = Network c s t for c :: "'capacity::linordered_idom graph" and s t +
  fixes  R :: "(nat \<times> nat \<Rightarrow> 'capacity) \<Rightarrow> nat"
     and find_augmenting_time :: "nat "
     and augment_with_path_time :: "nat"
     and special_info :: "(nat \<times> nat \<Rightarrow> 'capacity) \<Rightarrow> (nat \<times> nat) list \<Rightarrow> bool"
   assumes ff: "NFlow c s t a \<Longrightarrow>
 \<forall>x. \<not> special_info a x
   \<Longrightarrow> NPreflow.isAugmentingPath c s t a x \<Longrightarrow> False"  

  and R_decreases: "NFlow c s t a \<Longrightarrow> special_info a x \<Longrightarrow> R (NFlow.augment_with_path c a x) < R a"

  and fat_g_0: "\<And>x. find_augmenting_time  > 0"

  and augments: "\<And>p f.  NFlow c s t f \<Longrightarrow> special_info f p \<Longrightarrow> NPreflow.isAugmentingPath c s t f p"


context Network 
begin


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
          f \<leftarrow> SPECT [NFlow.augment_with_path c f p \<mapsto> augment_with_path_time];
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

fun (in FoFu) Te where "Te (f,brk) = (if brk then 0 else (find_augmenting_time + augment_with_path_time)  * (1+ R f))"


definition (in FoFu) "maxFlow_time = enat ( (find_augmenting_time + augment_with_path_time) * (R (\<lambda>_. 0) + 1)) "


theorem (in FoFu)  fofu_partial_correct: "fofu \<le> SPECT (emb (\<lambda>f. isMaxFlow f) (maxFlow_time))"
  unfolding fofu_def find_augmenting_spec_def 
  apply(rule T_specifies_I)
  apply (vcg'\<open>-\<close>)    

  apply (rule T_conseq4)
   apply (rule whileT_rule'''[OF refl, where I="(\<lambda>e. if fofu_invar e
                then Some (Te e) else None)"])
  subgoal (*progress*) by (progress'\<open>auto simp: fat_g_0 zero_enat_def\<close>)   
    apply (vcg'\<open>-\<close>)  apply(rule T_SELECT)   
  subgoal (* no augmenting path *)    
    apply (vcg'\<open>-\<close>) 
    using ff by blast
  subgoal for f brk p (* found augmenting path *)    
    apply (vcg'\<open>-\<close>)
    subgoal unfolding NFlow.augment_with_path_def
      using  NFlow.augment_pres_nflow augments by metis
    subgoal 
      by (simp add: R_decreases less_imp_le_nat) 
    subgoal  
      by (simp add: R_decreases less_imp_le_nat) 
    subgoal by (metis R_decreases diff_mult_distrib2 prod_ineqs2 zero_less_diff)
    subgoal  using  augments by simp 
    subgoal using NFlow.augmenting_path_not_empty augments  by metis
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
