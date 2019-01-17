theory EdmondsKarp_Time
  imports EdmondsKarp_Impl 
 (*    "SepLogicTime_RBTreeBasic.Asymptotics_2D" 
      \<longrightarrow> Cannot join unrelated theory certificates SepLogicTime_RBTreeBasic.Asymptotics_2D:321 and SepLogicTime_RBTreeBasic.RBTree_Impl:4570
  *)
begin
 
lemma "(\<lambda>x::nat. real ((3 ))) \<in> \<Theta>(\<lambda>(x). real 1)" 
  by auto2 

lemma "(\<lambda>x. real ((32 ))) \<in> \<Theta>\<^sub>2(\<lambda>(V::nat,E::nat). 1)"
  apply (subst surjective_pairing) by auto2

lemma "(\<lambda>x. real ((rbt_insert_logN 1 ))) \<in> \<Theta>\<^sub>2(\<lambda>(V::nat,E::nat). 1)" 
  apply (subst surjective_pairing) by auto2

lemma edka_runt: "edka_cost \<in> \<Theta>\<^sub>2(\<lambda>(V::nat,E::nat). V * E * V + V * E * E  )"
  apply (subst surjective_pairing)
  unfolding edka_cost_simp by auto2


lemma final_running_time: "edka_cost \<in> \<Theta>\<^sub>2(\<lambda>(V::nat,E::nat). (V * E) * (V + E) )"
proof -
  have *:  "\<And>E V::nat. (V * E) * (V + E) = V * E * V + V * E * E"  
    by (simp add: distrib_left)  
  show ?thesis unfolding * using edka_runt  
    by simp
qed 

end