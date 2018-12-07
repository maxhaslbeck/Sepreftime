theory InLocale
imports "SepLogicTime_RBTreeBasic.Asymptotics_2D" 
begin


(* works fine outside an locale *)

definition getEdges_time :: "nat \<Rightarrow>  nat" where "getEdges_time = undefined"
definition sort_time' :: "nat \<Rightarrow>  nat" where "sort_time' = undefined"
definition uf_init_time :: "nat \<Rightarrow>  nat" where "uf_init_time = undefined"
definition uf_cmp_time :: "nat \<Rightarrow>  nat" where "uf_cmp_time = undefined"
definition uf_union_time :: "nat \<Rightarrow>  nat" where "uf_union_time = undefined"
lemma [asym_bound]: "getEdges_time \<in> \<Theta>(\<lambda>n::nat. n)" sorry
  lemma [asym_bound]: "sort_time' \<in> \<Theta>(\<lambda>n::nat. n * ln n)" sorry
  lemma [asym_bound]: "uf_init_time \<in> \<Theta>(\<lambda>n::nat. 1)" sorry
  lemma [asym_bound]: "uf_cmp_time \<in> \<Theta>(\<lambda>n::nat. 1)" sorry
  lemma [asym_bound]: "uf_union_time \<in> \<Theta>(\<lambda>n::nat. ln n)" sorry
 


fun kruskal_time :: "nat * nat \<Rightarrow> nat" where "kruskal_time (sE, mV) = 
      (getEdges_time sE + sort_time' sE + (12 + uf_init_time mV) +
      sE * (uf_cmp_time mV + (23 + uf_union_time mV)))"

term "\<Theta>\<^sub>2(\<lambda>(e::nat,m::nat). e * ln e + e * ln m + e )"
                                                                  
lemma "kruskal_time \<in> \<Theta>\<^sub>2(\<lambda>(e::nat,m::nat). e * ln e + e * ln m  )"
  apply (subst surjective_pairing)
  unfolding kruskal_time.simps
  by auto2



(* breaks in locale *)


locale krtime = fixes
  getEdges_time :: "nat \<Rightarrow>  nat"  
 and sort_time' :: "nat \<Rightarrow>  nat"  
and uf_init_time :: "nat \<Rightarrow>  nat"  
and uf_cmp_time :: "nat \<Rightarrow>  nat"  
and uf_union_time :: "nat \<Rightarrow>  nat"  
assumes [asym_bound]: "getEdges_time \<in> \<Theta>(\<lambda>n::nat. n)"  
  and [asym_bound]: "sort_time' \<in> \<Theta>(\<lambda>n::nat. n * ln n)" 
  and [asym_bound]: "uf_init_time \<in> \<Theta>(\<lambda>n::nat. 1)" 
  and [asym_bound]: "uf_cmp_time \<in> \<Theta>(\<lambda>n::nat. 1)" 
  and [asym_bound]: "uf_union_time \<in> \<Theta>(\<lambda>n::nat. ln n)" 
begin


fun kruskal_time :: "nat * nat \<Rightarrow> nat" where "kruskal_time (sE, mV) = 
      (getEdges_time sE + sort_time' sE + (12 + uf_init_time mV) +
      sE * (uf_cmp_time mV + (23 + uf_union_time mV)))"

                                                                  
lemma "kruskal_time \<in> \<Theta>\<^sub>2(\<lambda>(e::nat,m::nat). e * ln e + e * ln m  )"
  apply (subst surjective_pairing)
  unfolding kruskal_time.simps
  by auto2

end



end