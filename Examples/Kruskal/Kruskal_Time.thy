theory Kruskal_Time
  imports MaxNode_Impl
    Union_Find_Time
begin





locale Kruskal_final = Kruskal_intermediate  E forest connected path weight 
  for E :: "nat uprod set" and forest connected path
      and weight :: "nat uprod \<Rightarrow> int"
    + fixes getEdges getEdges_time getEdges_impl
  assumes E: "E \<noteq>{}"
    and getEdges_Spec: "getEdges \<le> \<Down> Id (getEdges' weight E (enat (getEdges_time (card E))))"
    and getEdges_impl_refines: 
          "(uncurry0 getEdges_impl, uncurry0 getEdges) \<in> unit_assn\<^sup>k
                   \<rightarrow>\<^sub>a list_assn (nat_assn \<times>\<^sub>a int_assn \<times>\<^sub>a nat_assn)" 
begin
 
sublocale  Kruskal_intermediate_Impl E forest connected path weight getEdges getEdges_impl
      "getEdges_time (card E)" "sortEdges'_time (card E)" "uf_init_time (Suc (Max V))"
      "uf_cmp_time (Suc (Max V))" "uf_union_time (Suc (Max V))"
      is_uf uf_init uf_init_time uf_cmp uf_cmp_time uf_union uf_union_time
      sortEdges' sortEdges'_time
  apply(unfold_locales)
        apply (fact E)
       apply(fact getEdges_Spec)
      apply(fact getEdges_impl_refines)
  by auto 


thm kruskal_correct_forest
 

term minBasis_time
thm minBasis_time_def

definition (in -) "kruskal_time gt  \<equiv> \<lambda>(cE, M). gt cE + sortEdges'_time cE + (12 + uf_init_time (Suc M)) + cE * (uf_cmp_time (Suc M) + (23 + uf_union_time (Suc M)))"
definition (in -) "kruskal_time'  \<equiv> \<lambda>(cE, M). sortEdges'_time cE + (12 + uf_init_time (M + 1)) + cE * (uf_cmp_time (M + 1) + (23 + uf_union_time (M + 1)))"

term minBasis_time

lemma mBT: "minBasis_time = kruskal_time getEdges_time (card E, Max V)"
  unfolding minBasis_time_def kruskal_time_def by simp


lemma k_c: "<timeCredit_assn (kruskal_time getEdges_time (card E, Max V))> kruskal <\<lambda>r. \<exists>\<^sub>Ara. hr_comp (da_assn id_assn) lst_graph_rel ra r * \<up> (MST ra)>\<^sub>t"
  unfolding mBT[symmetric] using kruskal_correct_forest by simp

thm sortEdges'_time_bound uf_init_bound uf_cmp_time_bound uf_union_time_bound

lemma uf_init_bound[asym_bound]: "uf_init_time \<in> \<Theta>(\<lambda>n. n)" 
  unfolding uf_init_time_def by auto2

lemma (in -) kruskal_time'_bound:
  shows "kruskal_time'  \<in> \<Theta>\<^sub>2(\<lambda>(E::nat,M::nat). E * ln E + M + E * ln M )"
  unfolding kruskal_time'_def
  by (auto2)

lemma (in -) kruskal_time_split: "kruskal_time gt  = (\<lambda>(cE,M). gt cE) +  kruskal_time'"
  apply(rule ext) apply (simp add: kruskal_time'_def kruskal_time_def) by auto

lemma (in -) polylog00: "polylog 0 0 m = 1" unfolding polylog_def by simp

lemma (in -) kruskal_time_plus_linear:
  assumes "gt \<in> \<Theta>(\<lambda>n. n)"
  shows "kruskal_time gt \<in> \<Theta>\<^sub>2(\<lambda>(E::nat,M::nat). E * ln E + M + E * ln M )" (is "_ \<in> ?T")
proof -
  have A: "(\<lambda>x. real (gt (fst x))) \<in> \<Theta>\<^sub>2 (\<lambda>(n::nat, m::nat). real n)"
    using mult_Theta_bivariate1[unfolded polylog2_def polylog_def, of gt 1 0 ]
    apply auto using assms by simp

  have split: "\<And>x. gt (fst x) + kruskal_time' x = kruskal_time gt x"
    unfolding kruskal_time'_def kruskal_time_def by auto

  have r: "(\<lambda>x. real (gt (fst x) + kruskal_time' x)) \<in> \<Theta>\<^sub>2 ((\<lambda>x. case x of (n, m) \<Rightarrow> real n) + (\<lambda>x. case x of (E, M) \<Rightarrow> real E * ln (real E) + real M + real E * ln (real M)))"
    apply(rule bigtheta_add[OF _ _ A kruskal_time'_bound ])
    subgoal apply(auto simp: eventually_nonneg_def eventually_sequentially)
       
      using eventually_prod_same by force  
    subgoal apply(auto simp: eventually_nonneg_def eventually_sequentially)
      apply(subst eventually_prod_same) apply auto apply(rule exI[where x="\<lambda>x. x\<ge>1"])
      by simp
    done

  { fix x y :: nat and c
    assume t: "y\<ge>1 " " x\<ge>1 " " 1 \<le> c * ln (real x)" "c>0"
    then have t': "real y + real x * ln (real y) \<ge> 0"  
      by simp  
    from t have "real x \<le> c * real x * ln (real x)" by auto
    also have "\<dots> \<le> c * (real x * ln (real x) + real y + real x * ln (real y)) " 
      using t' t by auto 
    finally
    have "real x \<le> c * (real x * ln (real x) + real y + real x * ln (real y)) " .
  } note blub = this



  have 2: "?T = \<Theta>\<^sub>2 ((\<lambda>x. case x of (n, m) \<Rightarrow> real n) + (\<lambda>x. case x of (E, M) \<Rightarrow> real E * ln (real E) + real M + real E * ln (real M)))"
    apply(subst plus_absorb1')
    subgoal apply(rule landau_o.smallI) apply(subst eventually_prod_same) 
      subgoal for c apply(rule exI[where x="\<lambda>x::nat. real x \<le> c * \<bar>real x * ln (real x)\<bar> \<and> x\<ge>1"])
        apply safe subgoal apply(simp add: eventually_sequentially) apply (rule exI[where x="max (max 1 (nat (ceiling (exp (1/c))))) (nat (ceiling (1/c)))"])
          apply auto  
          by (metis exp_gt_zero exp_le_cancel_iff exp_ln less_le_trans mult.commute pos_divide_le_eq)    
          apply auto  apply(rule blub) by auto       
        done
    by simp

  show ?thesis 
    unfolding split[symmetric] 2
    using r .
qed 

end


end