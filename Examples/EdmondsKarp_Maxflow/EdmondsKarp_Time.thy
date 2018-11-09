theory EdmondsKarp_Time
imports EdmondsKarp_Impl "SepLogicTime_RBTreeBasic.Asymptotics_2D"
begin
 

definition cost' :: "nat \<times> nat \<Rightarrow> nat" 
  where "cost' = (\<lambda>(cV,cE). 
    (
      3 + rbt_insert_logN 1 + rbt_insert_logN 1 + 10
       +
         (1 + cV + cV * cV)   
         *
          (
            10 + 10 + rbt_delete_time_logN (cV + 1) + 10 + 10 + (2 + cV * (1 + 1))
             + 
                  cV
                   *
                  (rbt_search_time_logN (1 + cV) + 1 + max (rbt_insert_logN (cV + 1) + rbt_insert_logN (1 + cV)) 1)
          )
       +
          cV * (rbt_search_time_logN (1 + cV) + 1 + 1)
       +
          (1 + (1 + 10) * cV + (1 + cV * (2 * 1 + 2 * 1 + 3)))
    )  
   *
    (2 * cV * cE + cV + 1)        (* O(V*E) - fofu iterations *)
  )"

fun f_sum :: "nat \<times> nat \<Rightarrow> nat" where
  "f_sum (n,m) = n + m"

lemma f_sum_asym [asym_bound]: "f_sum \<in> \<Theta>\<^sub>2(\<lambda>x. real (fst x) + real (snd x))"
  apply (subst surjective_pairing) unfolding f_sum.simps by auto2

fun cost2 :: "nat \<times> nat \<Rightarrow> nat" where "cost2 (cV,cE) = (3 + 1 + 1 + 10 +
     (1 + cV + cV * cV) )"

lemma "cost2 \<in> \<Theta>\<^sub>2(\<lambda>(V,E). real V * real V)"
  apply (subst surjective_pairing) unfolding cost2.simps by auto2
 
fun cost3 :: "nat \<times> nat \<Rightarrow> nat" where "cost3 (cV,cE) = rbt_search_time_logN ( cV)"

thm rbt_search_time_logN_bound
lemma "cost3 \<in> \<Theta>\<^sub>2(\<lambda>(V::nat,E::nat). ln V)"
  apply (subst surjective_pairing) unfolding cost3.simps by auto2 (* ? ? ? *)

lemma rbt_search_time_logN_bound[asym_bound]:
  "(\<lambda>n. rbt_search_time_logN n) \<in> \<Theta>(\<lambda>n. ln n)" unfolding rbt_search_time_logN_def rbt_search_time_def by auto2

lemma "cost3 \<in> \<Theta>\<^sub>2(\<lambda>(V::nat,E::nat). ln V)"
  apply (subst surjective_pairing) unfolding cost3.simps by auto2


definition edka_cost' :: "nat \<times> nat \<Rightarrow> nat" 
    where "edka_cost' = (\<lambda>(cV,cE). 3 + rbt_insert_logN cV + rbt_insert_logN cV + 10)"

lemma "edka_cost' \<in> \<Theta>\<^sub>2(\<lambda>(V,E). ln V)"
  apply (subst surjective_pairing) unfolding edka_cost_def by auto2
 

end