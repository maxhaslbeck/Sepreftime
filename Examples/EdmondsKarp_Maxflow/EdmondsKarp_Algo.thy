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

context Network 
begin


definition "shortestpath_time = enat 10"
                    
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
 


text \<open>First, we specify the refined procedure for finding augmenting paths\<close>
definition "find_shortest_augmenting_spec f \<equiv> ASSERT (NFlow c s t f) \<then> 
  SELECT (\<lambda>p. Graph.isShortestPath (residualGraph c f) s p t) (shortestpath_time)"

text \<open>We show that our refined procedure is actually a refinement\<close>  
lemma find_shortest_augmenting_refine: 
  "(f',f)\<in>Id \<Longrightarrow> find_shortest_augmenting_spec f' \<le> \<Down>(\<langle>Id\<rangle>option_rel) (find_augmenting_spec f)"  
  unfolding find_shortest_augmenting_spec_def find_augmenting_spec_def
  apply(rule bindT_refine'[where R'=Id])
   apply auto 
  apply(rule SELECT_refine)
  subgoal unfolding special_info_def by auto
  subgoal unfolding special_info_def apply safe
    using NFlow.shortest_is_augmenting  
      NFlow.augmenting_path_imp_shortest pw_ASSERT 
    by blast 
  unfolding shortestpath_time_def find_augmenting_time_def by simp

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
          f \<leftarrow> RETURNT (NFlow.augment_with_path c f p);
          ASSERT (NFlow c s t f);
          RETURNT (f, False)
        }  
    })
    (f,False);
  ASSERT (NFlow c s t f);
  RETURNT f 
}" 
 

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

thm refine_mono

lemma inresT_ASSERT: "inresT (ASSERT Q \<bind> (\<lambda>_. M)) x ta = (Q \<longrightarrow> inresT M x ta)"
  unfolding ASSERT_def iASSERT_def by auto


lemma nofailT_ASSERT_bind: "nofailT (ASSERT P \<bind> (\<lambda>_. M)) \<longleftrightarrow> (P \<and> nofailT M)"
  by(auto simp: pw_bindT_nofailT pw_ASSERT)


lemma edka_partial_refine : "edka_partial \<le> \<Down>Id fofu"
  unfolding edka_partial_def fofu_def 
  apply(rule bindT_refine'[where R'=Id])
  apply simp
  apply(rule bindT_refine'[where R'="Id"])
   apply simp
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
      unfolding find_augmenting_spec_def (* WHY DO I NEED TO RECOVER ALL THIS INFORMATION FROM THE
          inresT and nofailT predicate?! *)      
      by(simp add: nofailT_ASSERT_bind)
    by(rule ASSERT_leI | simp)+     
  done


end \<comment> \<open>Network\<close>

subsubsection \<open>Total Correctness\<close>
context Network begin
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
          f \<leftarrow> RETURNT (NFlow.augment_with_path c f p);
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
 

thm edka_refine edka_partial_refine fofu_partial_correct

lemma edka_correct_time: "edka \<le> SPECT (emb isMaxFlow maxFlow_time)" 
  using edka_refine edka_partial_refine fofu_partial_correct 
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


lemma maxFlow_time_ub: "maxFlow_time \<le> find_augmenting_time (\<lambda>_. 0) * ((2 * card V * card E + card V) + 1)"
  unfolding maxFlow_time_def R_def 
  using ekMeasure_upper_bound 
  by (meson enat_ord_simps(2) le_iff_add less_le less_le_trans linorder_not_le nat_mult_less_cancel_disj)


lemma SPECT_ub: "T\<le>T' \<Longrightarrow> SPECT (emb' M' T) \<le> SPECT (emb' M' T')"
  unfolding emb'_def by (auto simp: pw_le_iff le_funD order_trans refine_pw_simps)

lemma "edka \<le> (SPECT (emb isMaxFlow (find_augmenting_time (\<lambda>_. 0) * ((2 * card V * card E + card V) + 1))))"
  apply(rule order_trans[OF edka_correct_time]) 
  apply(rule SPECT_ub)
  apply (simp only: le_fun_def)
    using  maxFlow_time_ub by simp  
 

end \<comment> \<open>Network\<close>
end \<comment> \<open>Theory\<close>
