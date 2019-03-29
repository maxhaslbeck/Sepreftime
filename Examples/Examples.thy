theory
  Examples
  imports 
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


section \<open>Edmonds Karp\<close>

context Network_Impl \<comment> \<open>given a Network c s t\<close>
begin

term fw_spec                  \<comment> \<open>The specification for FloydWarshall\<close>
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