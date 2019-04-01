theory
  Examples
  imports 
  "Kruskal/Kruskal_Time"
  "BinarySearch"
  "FloydWarshall/FW_Code"
  "Remdups"
  "EdmondsKarp_Maxflow/EdmondsKarp_Time"
begin 

section \<open>Remdups\<close>


term remdups_spec    \<comment> \<open>The specification for remdups\<close>
term rd_impl1         \<comment> \<open>The abstract algorithm in the NREST monad\<close>
thm rd_impl1_correct  \<comment> \<open>The correctness theorem\<close>

term remdups_impl    \<comment> \<open>The synthesised Imperative/HOL program\<close>


lemma "<$ (remdups_time (length as))> 
          remdups_impl as
        <\<lambda>r. \<exists>\<^sub>Ara. da_assn id_assn ra r * \<up> (set as = set ra \<and> distinct ra)>\<^sub>t"
  by(rule remdups_rule)

lemma "remdups_time \<in> \<Theta>(\<lambda>n. n * ln n)"
  by(fact remdups_time_nln)



section \<open>Binary Search\<close>

term binarysearch_SPEC    \<comment> \<open>The specification for binary search\<close>
term binarysearch         \<comment> \<open>The abstract algorithm in the NREST monad\<close>
thm binarysearch_correct  \<comment> \<open>The correctness theorem\<close>

term binarysearch_impl    \<comment> \<open>The synthesised Imperative/HOL program\<close>

lemma binary_search_correct: 
  assumes "sorted xs"  "l \<le> r" "r \<le> length xs"
  shows  
    "<array_assn xs p * $(binarysearch_time (r - l))> 
        binarysearch_impl l r x p
     <\<lambda>ra.   array_assn xs p * \<up> (ra \<longleftrightarrow> (\<exists>i\<ge>l. i < r \<and> xs ! i = x))>\<^sub>t"
  using assms binary_search_correct by blast

lemma binary_search_time_ln: "binarysearch_time \<in> \<Theta>(\<lambda>n. ln (real n))"
  by(fact binary_search_time_ln)


section \<open>Floyd Warshall\<close>

term fw_spec              \<comment> \<open>The specification for FloydWarshall\<close>
term fw'                  \<comment> \<open>The abstract algorithm in the NREST monad\<close>
thm fw'_spec              \<comment> \<open>The correctness theorem\<close>

term fw_impl    \<comment> \<open>The synthesised Imperative/HOL program\<close>

corollary 
  shows
    "<mtx_curry_assn n M Mi * $(fw_time n)>
        fw_impl n Mi
     <\<lambda> Mi'. \<exists>\<^sub>A M'. mtx_curry_assn n M' Mi'
           * \<up>(if (\<exists> i \<le> n. M' i i < 0) then \<not> cyc_free M n
                else \<forall>i \<le> n. \<forall>j \<le> n. M' i j = D M i j n \<and> cyc_free M n)>\<^sub>t"
  by(fact fw_correct)     

lemma "fw_time \<in> \<Theta>(\<lambda>n. n*n*n)"
  by (fact fw_time_n_cube)



section \<open>Kruskal\<close>

definition "kruskal getEdges_impl = Kruskal_intermediate_Impl.kruskal getEdges_impl uf_init uf_cmp uf_union sortEdges'"

lemma "kruskal getedges = Gr"
  unfolding kruskal_def apply(subst Kruskal_intermediate_Impl.kruskal_def) oops


lemma
  fixes connected path and E :: "nat uprod set"
  assumes "Kruskal_intermediate E forest connected path"
    \<comment> \<open>If we have a set of edges E for a Graph representation that provides
        predicates for forest, connected and path,...\<close>
    and  "E \<noteq>{}" 
    and getEdges_impl_refines: 
    "(uncurry0 getEdges_impl, uncurry0 (getEdges' weight E (enat (getEdges_time (card E))))) \<in> unit_assn\<^sup>k
                   \<rightarrow>\<^sub>a list_assn (nat_assn \<times>\<^sub>a int_assn \<times>\<^sub>a nat_assn)"
    \<comment> \<open>... and an implementation @{term getEdges_impl}, that gives a list of the edges of the Graph
          in time @{term getEdges_time}, ...  \<close>
    and getEdges_linear: "getEdges_time \<in> \<Theta>(\<lambda>n. n)"
    \<comment> \<open>... and the time bound @{term getEdges_time} is linear, then we can show ...  \<close>
  shows 
    \<comment> \<open>... that kruskal (using the @{term getEdges_impl} subprogram) calculates
          a minimum spanning forest for the graph and ...  \<close>
    kruskal_correct:
      "<timeCredit_assn (kruskal_time getEdges_time (card E, Max (Kruskal_intermediate_defs.V E)))>
        kruskal getEdges_impl 
       <\<lambda>r. \<exists>\<^sub>Ara. hr_comp (da_assn id_assn) (lst_graph_rel' weight) ra r * \<up> (minWeightBasis.minBasis E forest weight ra)>\<^sub>t"
  and
    \<comment> \<open> ... takes time in O( E * ln E + M + E * ln M ), where cE is the cardinality
          of the set of edges E, and M is the maximal node in the graph. \<close>
    kruska_time_bound:
      "kruskal_time getEdges_time \<in> \<Theta>\<^sub>2(\<lambda>(cE::nat,M::nat). cE * ln cE + M + cE * ln M )"
  subgoal 
    unfolding kruskal_def
    apply(rule Kruskal_final.k_c)
    using assms unfolding Pff_def Kruskal_final_axioms_def by auto
  subgoal  
    apply(rule kruskal_time_plus_linear) by fact
  done


section \<open>Edmonds Karp\<close>

context Network_Impl \<comment> \<open>given a Network c s t\<close>
begin

term Edka_Impl.edka5          \<comment> \<open>The abstract algorithm in the NREST monad\<close>
thm Edka_Impl.edka5_correct'  \<comment> \<open>The correctness theorem\<close>

term edka_imp    \<comment> \<open>The synthesised Imperative/HOL program\<close>

theorem edka_imp_correct: 
      assumes VN: "Graph.V c = {0..<N}" and "s < N" and "t < N"
      assumes ABS_PS: "is_adj_map am"
      shows "<$(edka_cost (card V, card E))> 
          edka_imp c s t N am 
        <\<lambda>fi. \<exists>\<^sub>Af. is_rflow N f fi * \<up>(isMaxFlow f)>\<^sub>t"
  apply (rule edka_imp_correct) by fact+

lemma "edka_cost \<in> \<Theta>\<^sub>2(\<lambda>(V::nat,E::nat). (V * E) * (V + E) )"
  by(fact final_running_time)

end


end