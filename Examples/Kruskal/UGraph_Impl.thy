theory UGraph_Impl
imports
 Kruskal_Impl "../../../Kruskal/UGraph" "SepLogicTime_RBTreeBasic.Asymptotics_2D" 
begin

abbreviation "subforest' EE F \<equiv> forest F \<and> F \<subseteq> EE"

definition "spanningforest' EE F \<longleftrightarrow> subforest' EE F \<and> (\<forall>x \<in> EE - F. \<not> subforest' EE (insert x F))"

definition "MST' EE w F \<longleftrightarrow> spanningforest' EE F \<and> (\<forall>F'. spanningforest' EE F' \<longrightarrow> sum w F \<le> sum w F')"

 

locale uGraph_impl = uGraph E w for E :: "nat uprod set" and w :: "nat uprod \<Rightarrow> int" +
  fixes getEdges_impl :: "(nat \<times> int \<times> nat) list Heap"
    and getEdges_time sort_time :: nat
    and empty_uf_time indep_test_time insert_uf_time :: nat
  assumes getEdges_impl[sepref_fr_rules]:
    "(uncurry0 getEdges_impl,  uncurry0 (PR_CONST (SPECT (emb (\<lambda>L. lst_graph_P' w L E) getEdges_time)))) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a list_assn (nat_assn \<times>\<^sub>a int_assn \<times>\<^sub>a nat_assn)"
   
begin


abbreviation "subforest EE F \<equiv> forest F \<and> F \<subseteq> EE"

sublocale  Kruskal_intermediate_Impl0 E "subforest E" "uconnectedV" "epath" w 
    "PR_CONST (SPECT (emb (\<lambda>L. lst_graph_P' w L E) getEdges_time))" getEdges_impl
    getEdges_time sort_time
    empty_uf_time indep_test_time insert_uf_time
proof (unfold_locales, goal_cases)
  fix e
  assume "e\<in>E"
  then show "proper_uprod e" using ecard2 by auto
next
  show "finite E" by simp
next
  fix E'
  assume "forest E' \<and> E' \<subseteq> E"
  then show "E' \<subseteq> E" by auto
next
  show "forest {} \<and> {} \<subseteq> E" apply (auto simp: decycle_def forest_def)
    using epath.elims(2) by fastforce 
next
  fix X Y
  assume "forest X \<and> X \<subseteq> E" "Y \<subseteq> X" 
  then show "forest Y \<and> Y \<subseteq> E" using forest_mono by auto
next
  fix u v E'
  show " ((u, v) \<in> uconnectedV E') = (\<exists>p. epath E' u p v \<and> u \<in> Kruskal_intermediate_defs.V E \<and> v \<in> Kruskal_intermediate_defs.V E)"
    unfolding uconnected_def Kruskal_intermediate_defs.V_def by auto
next
  case (7 u v)
  then show ?case unfolding uconnected_def Kruskal_intermediate_defs.V_def apply auto 
    using epath.elims(2) by force 
next
  case (8 E1 u p v E2)
  then have "\<exists>a b. (a, b) \<notin> uconnected E2
           \<and> Upair a b \<notin> E2 \<and> Upair a b \<in> E1" by(rule findaugmenting_edge)
  then show ?case by auto
next
  fix F u v
  assume f: "forest F \<and> F \<subseteq> E" and notin: "Upair u v \<in> E - F"
  from notin ecard2 have unv: "u\<noteq>v" by fastforce
  show "(forest (insert (Upair u v) F) \<and> insert (Upair u v) F \<subseteq> E) = ((u, v) \<notin> uconnectedV F)"
  proof
    assume a: "forest (insert (Upair u v) F) \<and> insert (Upair u v) F \<subseteq> E "
    have "(u, v) \<notin> uconnected F" apply(rule insert_stays_forest_means_not_connected)
      using notin a unv by auto
    then show "((u, v) \<notin> Restr (uconnected F) (UNION E set_uprod))" by auto
  next 
    assume a: "(u, v) \<notin> Restr (uconnected F) (UNION E set_uprod)"
    have "forest (insert (Upair u v) F)" apply(rule augment_forest_overedges[where E=E])
      using notin f a unv  by auto 
    moreover have "insert (Upair u v) F \<subseteq> E"
      using notin f by auto
    ultimately show "forest (insert (Upair u v) F) \<and> insert (Upair u v) F \<subseteq> E" by auto
  qed
next      
  fix F
  assume "F\<subseteq>E"
  show "equiv (Kruskal_intermediate_defs.V E) (uconnectedV F)"
    unfolding  Kruskal_intermediate_defs.V_def by(rule equiv_vert_uconnected)
next                                 
  case (11 F)
  then show ?case unfolding  Kruskal_intermediate_defs.V_def by auto
next
  case (12 x y F)
  then show ?case unfolding  Kruskal_intermediate_defs.V_def by (rule insert_uconnectedV_per)
next
  show "E \<noteq> {}" by simp
  show "PR_CONST (getEdges' w E (enat getEdges_time)) \<le> \<Down> Id (getEdges' w E (enat getEdges_time))" using  PR_CONST_def by simp
  show "(uncurry0 getEdges_impl, uncurry0 (PR_CONST (getEdges' w E (enat getEdges_time)))) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a list_assn (nat_assn \<times>\<^sub>a int_assn \<times>\<^sub>a nat_assn)"
    using getEdges_impl by simp
qed
 
lemma minBasis_is_MST': "minBasis = MST' E w"
  unfolding minBasis_def MST'_def
   basis_def  spanningforest'_def by simp

end


locale uGraph_impl2 = uGraph_impl + UnionFind_Impl + sortMaxnode +
  assumes 
  [simp]:  "uf_init_time (Suc (Max V)) \<le> empty_uf_time" 
    "uf_cmp_time (Suc (Max V)) \<le> indep_test_time" 
    "uf_union_time (Suc (Max V)) \<le> insert_uf_time" 
    "sort_time' (card E) \<le> sort_time"
begin
 

sublocale s: Kruskal_intermediate_Impl E "subforest E" "uconnectedV" "epath" w "PR_CONST getEdges" getEdges_impl
  getEdges_time sort_time empty_uf_time indep_test_time insert_uf_time is_uf
     uf_init uf_init_time uf_cmp uf_cmp_time uf_union uf_union_time sortEdges_impl sort_time'
  apply (unfold_locales)
        apply simp apply simp
  subgoal  using getEdges_impl PR_CONST_def by auto
     apply simp_all
  done

term MST

lemmas kurskal_horetriple =  s.kruskal_correct_forest
thm s.kruskal_ref_spec
abbreviation "kruskal \<equiv> s.kruskal"

end

thm uGraph_impl2.kurskal_horetriple
thm uGraph_impl2_def
(*
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
*)

locale stuffdone = UnionFind_Impl + sortMaxnode
  + fixes "getEdges_time" :: "nat \<Rightarrow> nat"
  assumes
      [asym_bound]: "getEdges_time \<in> \<Theta>(\<lambda>n::nat. n)" 
  and [asym_bound]: "sort_time' \<in> \<Theta>(\<lambda>n::nat. n * ln n)" 
  and [asym_bound]: "uf_init_time \<in> \<Theta>(\<lambda>n::nat. 1)" 
  and [asym_bound]: "uf_cmp_time \<in> \<Theta>(\<lambda>n::nat. 1)" 
  and [asym_bound]: "uf_union_time \<in> \<Theta>(\<lambda>n::nat. ln n)" 
begin


fun kruskal_time :: "nat * nat \<Rightarrow> nat" where "kruskal_time (sE, mV) = 
      (getEdges_time sE + sort_time' sE + (12 + uf_init_time mV) +
      sE * (uf_cmp_time mV + (23 + uf_union_time mV)))"

term "\<Theta>\<^sub>2(\<lambda>(e::nat,m::nat). e * ln e + e * ln m + e )"
                                                                  
lemma "kruskal_time \<in> \<Theta>\<^sub>2(\<lambda>(e::nat,m::nat). e * ln e + e * ln m   )"
  apply (subst surjective_pairing)
  unfolding kruskal_time.simps
  apply (auto2) sorry

lemma 
  assumes [simp]: "\<And>e. e \<in> E \<Longrightarrow> proper_uprod e" "finite E" "E \<noteq> {}"
      and getEdges_impl:
    "(uncurry0 getEdges_impl,  uncurry0 (PR_CONST (SPECT (emb (\<lambda>L. lst_graph_P' w L E) (enat (getEdges_time (card E))))))) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a list_assn (nat_assn \<times>\<^sub>a int_assn \<times>\<^sub>a nat_assn)"
   
  shows "<$ (kruskal_time (card E,Suc (Max (uGraph.verts E))) )>
             uGraph_impl2.kruskal getEdges_impl uf_init uf_cmp uf_union sortEdges_impl
         <\<lambda>r. \<exists>\<^sub>Ara. hr_comp (da_assn id_assn) (lst_graph_rel' w) ra r * \<up> ( MST' E w ra)>\<^sub>t"
proof -

  interpret uGraph_impl2 E w  getEdges_impl 
      "getEdges_time (card E)" "sort_time' (card E)"   "uf_init_time (Suc (Max (uGraph.verts E)))"
        "uf_cmp_time (Suc (Max (uGraph.verts E)))" "uf_union_time (Suc (Max (uGraph.verts E)))"
  is_uf   uf_init  uf_init_time uf_cmp  uf_cmp_time  uf_union  uf_union_time  sortEdges_impl  sort_time'  
    apply unfold_locales
       apply (simp_all add: Kruskal_intermediate_defs.V_def)
    using getEdges_impl    
    by auto

  from kurskal_horetriple show ?thesis
    unfolding minBasis_time_def minBasis_is_MST' kruskal_time.simps .
qed
  


end



end
