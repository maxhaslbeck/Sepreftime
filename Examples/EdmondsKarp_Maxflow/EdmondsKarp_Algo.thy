theory EdmondsKarp_Algo
imports EdmondsKarp_Termination_Abstract FordFulkerson_Algo
begin
text \<open>
  In this theory, we formalize an abstract version of
  Edmonds-Karp algorithm, which we obtain by refining the 
  Ford-Fulkerson algorithm to always use shortest augmenting paths.

  Then, we show that the algorithm always terminates within $O(VE)$ iterations.
\<close>

subsection \<open>Algorithm\<close>

locale EdKa = Network c s t for c :: "'capacity::linordered_idom graph" and s t +
  fixes shortestpath_time :: nat
    and augment_with_path_time :: nat 
  assumes augment_progress: "0 \<noteq> enat shortestpath_time"
begin


text \<open>First, we specify the refined procedure for finding augmenting paths\<close>
definition "find_shortest_augmenting_spec f \<equiv> ASSERT (NFlow c s t f) \<then> 
  SELECT (\<lambda>p. Graph.isShortestPath (residualGraph c f) s p t) (shortestpath_time)"


definition edka_measure :: "(nat \<times> nat \<Rightarrow> 'capacity) \<Rightarrow> nat" where
  "edka_measure cf = ek_analysis_defs.ekMeasure (residualGraph c cf) s t" 

definition info :: "(nat \<times> nat \<Rightarrow> 'capacity) \<Rightarrow> (nat \<times> nat) list \<Rightarrow> bool" where
  "info f p =  Graph.isShortestPath (residualGraph c f) s p t"

lemma  edka_measure_decreases:
  assumes "NFlow c s t a"
      "NPreflow.isAugmentingPath c s t a x"
      "info  a x"
  shows "edka_measure (NFlow.augment_with_path c a x) < edka_measure a"
proof -
  have 2: "Graph.isShortestPath (cf_of a) s x t"
    using assms(3) unfolding info_def  by simp

  show "edka_measure (NFlow.augment_with_path c a x) < edka_measure a"
  unfolding edka_measure_def  
  using NFlow.shortest_path_decr_ek_measure[OF assms(1) 2] 
    NFlow.augment_with_path_def[OF assms(1) ] by auto
qed 


lemma augments: "\<And>f p. NFlow c s t f \<Longrightarrow> info f p \<Longrightarrow> NPreflow.isAugmentingPath c s t f p"
  unfolding info_def using  NFlow.shortest_is_augmenting by blast

print_locale FoFu

definition (in -) edka_time_aux   where
  "edka_time_aux shortestpath_time augment_with_path_time cE cV  =   (shortestpath_time+augment_with_path_time) * (2 * cV * cE + cV + 1)"

interpretation edka: FoFu c s t "edka_measure:: (nat \<times> nat \<Rightarrow> 'capacity) \<Rightarrow> nat" shortestpath_time augment_with_path_time "info :: (nat \<times> nat \<Rightarrow> 'capacity) \<Rightarrow> (nat \<times> nat) list \<Rightarrow> bool"
  apply standard
  subgoal using NFlow.augmenting_path_imp_shortest info_def by blast 
  subgoal using edka_measure_decreases info_def augments by simp
  subgoal using augment_progress by simp
  subgoal using augments by blast
  done


text \<open>We show that our refined procedure is actually a refinement\<close>  
lemma find_shortest_augmenting_refine: 
  "(f',f)\<in>Id \<Longrightarrow> find_shortest_augmenting_spec f' \<le> \<Down>(\<langle>Id\<rangle>option_rel) (edka.find_augmenting_spec f)"  
  unfolding find_shortest_augmenting_spec_def edka.find_augmenting_spec_def
  apply(rule bindT_refine'[where R'=Id])
   apply auto 
  apply(rule SELECT_refine)
  subgoal unfolding info_def by auto
  subgoal unfolding info_def by safe  
  by simp

text \<open>Next, we specify the Edmonds-Karp algorithm. 
  Our first specification still uses partial correctness, 
  termination will be proved afterwards. \<close>  
definition "edka_partial \<equiv> do {
  f \<leftarrow> RETURNT (\<lambda>_. 0);

  (f,_) \<leftarrow> whileT(*\<^bsup>fofu_invar\<^esup>*)
    (\<lambda>(f,brk). \<not>brk) 
    (\<lambda>(f,_). do {
      p \<leftarrow> find_shortest_augmenting_spec f;
      case p of 
        None \<Rightarrow> RETURNT (f,True)
      | Some p \<Rightarrow> do {
          ASSERT (p\<noteq>[]);
          ASSERT (NPreflow.isAugmentingPath c s t f p);
          ASSERT (Graph.isShortestPath (residualGraph c f) s p t);
          f \<leftarrow> SPECT [NFlow.augment_with_path c f p \<mapsto> augment_with_path_time];
          ASSERT (NFlow c s t f);
          RETURNT (f, False)
        }  
    })
    (f,False);
  ASSERT (NFlow c s t f);
  RETURNT f 
}" 
 

lemma edka_partial_refine : "edka_partial \<le> \<Down>Id edka.fofu"
  unfolding edka_partial_def edka.fofu_def 
  apply(rule bindT_refine'[where R'=Id])
  apply simp
  apply(rule bindT_refine'[where R'="Id"])
   apply simp unfolding whileIET_def
   apply(rule whileT_mono)
   apply(rule case_prod_refine)
   apply auto   
  apply(rule bindT_mono) apply auto
  subgoal 
    using find_shortest_augmenting_refine[simplified option_rel_id_simp, simplified] by simp
  subgoal 
    apply(rule case_option_mono) apply simp  
    apply(rule le_ASSERTI)+   
    apply(rule ASSERT_leI | simp)+
    unfolding find_shortest_augmenting_spec_def
    subgoal apply(simp only: inresT_ASSERT inresT_SELECT_Some)  apply safe
      unfolding edka.find_augmenting_spec_def (* WHY DO I NEED TO RECOVER ALL THIS INFORMATION FROM THE
          inresT and nofailT predicate?! *)      
      by(simp add: nofailT_ASSERT_bind)
    by (rule ASSERT_leI | simp)+     
  done


 

subsubsection \<open>Total Correctness\<close>
 
text \<open>We specify the total correct version of Edmonds-Karp algorithm.\<close>
definition "edka \<equiv> do {
  f \<leftarrow> RETURNT (\<lambda>_. 0);

  (f,_) \<leftarrow> whileT(*\<^bsup>fofu_invar\<^esup>*)
    (\<lambda>(f,brk). \<not>brk) 
    (\<lambda>(f,_). do {
      p \<leftarrow> find_shortest_augmenting_spec f;
      case p of 
        None \<Rightarrow> RETURNT (f,True)
      | Some p \<Rightarrow> do {
          ASSERT (p\<noteq>[]);
          ASSERT (NPreflow.isAugmentingPath c s t f p);
          ASSERT (Graph.isShortestPath (residualGraph c f) s p t);
          f \<leftarrow> SPECT [NFlow.augment_with_path c f p \<mapsto> augment_with_path_time];
          ASSERT (NFlow c s t f);
          RETURNT (f, False)
        }  
    })
    (f,False);
  ASSERT (NFlow c s t f);
  RETURNT f 
}"

text \<open>Based on the measure function, it is easy to obtain a well-founded 
  relation that proves termination of the loop in the Edmonds-Karp algorithm:\<close>
definition "edka_wf_rel \<equiv> inv_image 
  (less_than_bool <*lex*> measure (\<lambda>cf. ek_analysis_defs.ekMeasure cf s t))
  (\<lambda>(f,brk). (\<not>brk,residualGraph c f))"

lemma edka_wf_rel_wf[simp, intro!]: "wf edka_wf_rel"
  unfolding edka_wf_rel_def by auto

text \<open>The following theorem states that the total correct 
  version of Edmonds-Karp algorithm refines the partial correct one.\<close>  
theorem edka_refine: "edka \<le> \<Down>Id edka_partial"
  unfolding edka_def edka_partial_def
  by simp 
 

thm edka_refine edka_partial_refine edka.fofu_partial_correct

lemma edka_correct_time: "edka \<le> SPECT (emb isMaxFlow edka.maxFlow_time)" 
  using edka_refine edka_partial_refine edka.fofu_partial_correct 
  by simp


subsubsection \<open>Complexity Analysis\<close>

text \<open>For the complexity analysis, we additionally show that the measure
  function is bounded by $O(VE)$. Note that our absolute bound is not as 
  precise as possible, but clearly $O(VE)$.\<close>
  (* TODO: #edgesSp even bound by |E|, as either e or swap e lays on shortest path! *)
lemma ekMeasure_upper_bound: 
  "ek_analysis_defs.ekMeasure (residualGraph c (\<lambda>_. 0)) s t 
   < 2 * card V * card E + card V"
proof -  
  interpret NFlow c s t "(\<lambda>_. 0)"
    by unfold_locales (auto simp: s_node t_node cap_non_negative)

  interpret ek: ek_analysis cf  
    by unfold_locales auto

  have cardV_positive: "card V > 0" and cardE_positive: "card E > 0"
    using card_0_eq[OF finite_V] V_not_empty apply blast
    using card_0_eq[OF finite_E] E_not_empty apply blast
    done

  show ?thesis proof (cases "cf.connected s t")  
    case False hence "ek.ekMeasure = 0" by (auto simp: ek.ekMeasure_def)
    with cardV_positive cardE_positive show ?thesis
      by auto
  next
    case True 

    have "cf.min_dist s t > 0"
      apply (rule ccontr)
      apply (auto simp: Graph.min_dist_z_iff True s_not_t[symmetric])
      done

    have "cf = c"  
      unfolding residualGraph_def E_def
      by auto
    hence "ek.uE = E\<union>E\<inverse>" unfolding ek.uE_def by simp

    from True have "ek.ekMeasure 
      = (card cf.V - cf.min_dist s t) * (card ek.uE + 1) + (card (ek.spEdges))"
      unfolding ek.ekMeasure_def by simp
    also from 
      mlex_bound[of "card cf.V - cf.min_dist s t" "card V", 
                 OF _ ek.card_spEdges_less]
    have "\<dots> < card V * (card ek.uE+1)" 
      using \<open>cf.min_dist s t > 0\<close> \<open>card V > 0\<close>
      by (auto simp: resV_netV)
    also have "card ek.uE \<le> 2*card E" unfolding \<open>ek.uE = E\<union>E\<inverse>\<close> 
      apply (rule order_trans)
      apply (rule card_Un_le)
      by auto
    finally show ?thesis by (auto simp: algebra_simps)
  qed  
qed  

text \<open>Finally, we present a version of the Edmonds-Karp algorithm 
  which is instrumented with a loop counter, and asserts that
  there are less than $2|V||E|+|V| = O(|V||E|)$ iterations.

  Note that we only count the non-breaking loop iterations.
  \<close>

abbreviation "edka_time \<equiv> edka_time_aux shortestpath_time augment_with_path_time (card E) (card V)"

lemma maxFlow_time_ub: "edka.maxFlow_time \<le>  edka_time"
  unfolding edka.maxFlow_time_def edka_measure_def unfolding edka_time_aux_def
  using ekMeasure_upper_bound by auto





lemma edka_correct: "edka \<le> (SPECT (emb isMaxFlow (edka_time)))"
  apply(rule order_trans[OF edka_correct_time]) 
  apply(rule SPECT_ub)
  apply (simp only: le_fun_def)
    using  maxFlow_time_ub by simp  
 

end \<comment> \<open>EdKa\<close>
end \<comment> \<open>Theory\<close>
