theory Kruskal
imports Kruskal_Misc  MinWeightBasis "HOL-Library.Uprod"   
begin


abbreviation "\<alpha>'' == (\<lambda>(a,_,b). (a,b))"
abbreviation "\<alpha>' == (\<lambda>(a,_,b). Upair a b)"

definition "lst_graph_P' w l S \<equiv> distinct (map \<alpha>' l) \<and> (\<lambda>(a,_,b). Upair a b) ` set l = S 
                            \<and> (\<forall>(a,wv,b)\<in>set l.  w (Upair a b) = wv)"


definition "lst_graph_rel' w \<equiv> {(l,S). lst_graph_P' w l S }"

locale Kruskal_intermediate_defs =
  fixes  E :: "('a uprod) set"
   and forest :: "('a uprod) set \<Rightarrow> bool"
   and connected :: "('a uprod) set \<Rightarrow> ('a*'a) set"
   and path :: "('a uprod) set \<Rightarrow> 'a \<Rightarrow> ('a uprod) list \<Rightarrow> 'a \<Rightarrow> bool"
   and weight :: "'a uprod \<Rightarrow> 'b::{linorder, ordered_comm_monoid_add}" 
begin

  definition "V = \<Union>( set_uprod ` E)"

  lemma finiteE_finiteV: "finite E \<Longrightarrow> finite V"
    by(auto simp: V_def)


end
  
locale Kruskal_intermediate = Kruskal_intermediate_defs   E forest connected path weight for
     E :: "('a uprod) set"
   and forest :: "('a uprod) set \<Rightarrow> bool"
   and connected :: "('a uprod) set \<Rightarrow> ('a*'a) set"
   and path :: "('a uprod) set \<Rightarrow> 'a \<Rightarrow> ('a uprod) list \<Rightarrow> 'a \<Rightarrow> bool"
   and weight :: "'a uprod \<Rightarrow> 'b::{linorder, ordered_comm_monoid_add}" +
 assumes Eproper: "\<And>e. e\<in>E \<Longrightarrow> proper_uprod e" 
   and finiteE[simp]: "finite E" 
   and forest_subE: "forest E' \<Longrightarrow> E' \<subseteq> E"
   and forest_empty: "forest {}"
   and forest_mono: "forest X \<Longrightarrow> Y \<subseteq> X \<Longrightarrow> forest Y" 
   and connected_Epath: "(u,v) \<in> connected E'  \<longleftrightarrow> (\<exists>p. path E' u p v \<and> u \<in> V \<and> v \<in> V)" 
   and connected_same: "(u,v) \<in> connected {} \<longleftrightarrow> u=v \<and> v\<in>V"
   and findaugmenting_aux: "path E1 u p v \<Longrightarrow> \<not>(\<exists>p. path E2 u p v)
           \<Longrightarrow> \<exists>a b. (a,b) \<notin> connected E2 \<and> Upair a b \<notin> E2 \<and> Upair a b \<in> E1"
   and augment_forest: "forest F \<Longrightarrow> Upair u v \<in> E-F
           \<Longrightarrow> forest (insert (Upair u v) F) \<longleftrightarrow> (u,v) \<notin> connected F"
   and equiv: "F \<subseteq> E \<Longrightarrow> equiv V (connected F)"
   and connected_in: "connected F \<subseteq> V \<times> V"      
   and insert_reachable: "x\<noteq>y \<Longrightarrow> x \<in> V \<Longrightarrow> y \<in> V \<Longrightarrow> F \<subseteq> E
           \<Longrightarrow> connected (insert (Upair x y) F) = per_union (connected F) x y"  
begin

lemma E_inV: "\<And>e. e\<in>E \<Longrightarrow> set_uprod e \<subseteq> V"
  using V_def by auto

lemma finiteV[simp]: "finite V"
  by(auto intro: finiteE_finiteV)

definition "CC E' x = (connected E')``{x}"      

lemma sameCC_reachable: "E' \<subseteq> E \<Longrightarrow> u\<in>V \<Longrightarrow> v\<in>V \<Longrightarrow> CC E' u = CC E' v \<longleftrightarrow> (u,v) \<in> connected E'"
  unfolding CC_def using  equiv_class_eq_iff[OF equiv ] by auto

definition "CCs E' = quotient V (connected E')"  

lemma "quotient V Id = {{v}|v. v\<in>V}" unfolding quotient_def by auto  

lemma CCs_empty: "CCs {} = {{v}|v. v\<in>V}"   
  unfolding CCs_def unfolding quotient_def using connected_same by auto

lemma CCs_empty_card: "card (CCs {}) = card V"   
proof -
  have i: "{{v}|v. v\<in>V} = (\<lambda>v. {v})`V"  
    by blast 
  have "card (CCs {}) = card {{v}|v. v\<in>V}" 
    using CCs_empty  by auto
  also have "\<dots> = card ((\<lambda>v. {v})`V)" by(simp only: i) 
  also have "\<dots> = card V"
    apply(rule card_image)
    unfolding inj_on_def by auto
  finally show ?thesis .
qed

lemma CCs_imageCC: "CCs F = (CC F) ` V"
  unfolding CCs_def CC_def quotient_def  
  by blast


lemma union_eqclass_decreases_components: 
  assumes "CC F x \<noteq> CC F y" "(Upair x y) \<notin> F" "x\<in>V" "y\<in>V" "F \<subseteq> E"
  shows "Suc (card (CCs (insert (Upair x y) F))) = card (CCs F)"
proof -  
  from assms(1) have xny: "x\<noteq>y" by blast   
  show ?thesis unfolding CCs_def
    apply(simp only: insert_reachable[OF xny assms(3-5)])
    apply(rule unify2EquivClasses_alt)          
         apply(fact assms(1)[unfolded CC_def])                           
        apply fact+      
      apply (fact connected_in)      
     apply(rule equiv) apply fact      
    by (fact finiteV)      
qed

lemma forest_CCs: assumes "forest E'" shows "card (CCs E') + card E' = card V"
proof -
  from assms have "finite E'" using forest_subE
    using finiteE finite_subset by blast
  from this assms show ?thesis
  proof(induct E') 
    case (insert x F)
    then have xE: "x\<in>E" using forest_subE by auto
    from this obtain a b where xab: "x = Upair a b"  using uprod_exhaust by blast
    then have xab': "a\<noteq>b" using  Eproper[OF xE]  by auto
    from insert(4) forest_mono have fF: "forest F" by auto
    with insert(3) have eq: "card (CCs F) + card F = card V" by auto 

    from insert(4) forest_subE have k: "F \<subseteq> E" by auto     
    from xab xab' have abV: "a\<in>V" "b\<in>V" using E_inV xE by fastforce+
    from insert(2) xab have "Upair a b \<notin> F" by auto

    have "(a,b) \<notin> connected F" apply(subst augment_forest[symmetric])
        apply fact
      using xE xab apply simp
      using xab insert by auto
    with k abV sameCC_reachable have "CC F a \<noteq> CC F b" by auto 
    have "Suc (card (CCs (insert (Upair a b) F))) = card (CCs F)" 
      apply(rule union_eqclass_decreases_components)  
      by fact+ 
    then show ?case using xab insert(1,2) eq   by auto 
  qed (simp add: CCs_empty_card)
qed

lemma pigeonhole_CCs: 
  assumes finiteV: "finite V" and cardlt: "card (CCs E1) < card (CCs E2)"
  shows "(\<exists>u v. u\<in>V \<and> v\<in>V \<and> CC E1 u = CC E1 v \<and> CC E2 u \<noteq> CC E2 v)"  
proof (rule ccontr, clarsimp)
  assume "\<forall>u. u \<in> V \<longrightarrow> (\<forall>v. CC E1 u = CC E1 v \<longrightarrow> v \<in> V \<longrightarrow> CC E2 u = CC E2 v)"
  then have "\<And>u v. u\<in>V \<Longrightarrow> v\<in>V \<Longrightarrow> CC E1 u = CC E1 v \<Longrightarrow> CC E2 u = CC E2 v" by blast

  with coarser[OF finiteV] have "card ((CC E1) ` V) \<ge> card ((CC E2) ` V)" by auto

  with CCs_imageCC cardlt show "False" by auto
qed


theorem assumes f1: "forest E1"
  and f2: "forest E2"  
  and c: "card E1 > card E2"
shows augment: "\<exists>e\<in>E1-E2. forest (insert e E2)"
proof -
  \<comment> \<open>as E1 and E2 are both forests, and E1 has more edges than E2, E2 has more connected
        components than E1\<close> 
  from forest_CCs[OF f1] forest_CCs[OF f2] c have "card (CCs E1) < card (CCs E2)" by linarith

\<comment> \<open>by an pigeonhole argument, we can obtain two vertices u and v that are in the same components of E1,
        but in different components of E2\<close>
  then obtain u v where sameCCinE1: "CC E1 u = CC E1 v" and
    diffCCinE2: "CC E2 u \<noteq> CC E2 v" and k: "u \<in> V" "v \<in> V"
    using pigeonhole_CCs[OF finiteV] by blast   

  from diffCCinE2 have unv: "u \<noteq> v" by auto

\<comment> \<open>this means that there is a path from u to v in E1 ...\<close>   
  from f1 forest_subE have e1: "E1 \<subseteq> E" by auto    
  with connected_Epath sameCC_reachable k sameCCinE1 obtain p
    where pathinE1: "path E1 u p v"
    by auto 
      \<comment> \<open>... but none in E2\<close>  
  from f2 forest_subE have "E2 \<subseteq> E" by auto    
  with connected_Epath sameCC_reachable k diffCCinE2
  have nopathinE2: "\<not>(\<exists>p. path E2 u p v)"
    by auto

\<comment> \<open>hence, we can find vertices a and b that are not connected in E2,
          but are connected by an edge in E1\<close>    
  obtain a b where pe: "(a,b) \<notin> connected E2" and abE2: "Upair a b \<notin> E2"
    and abE1: "Upair a b \<in> E1"
    using findaugmenting_aux[OF pathinE1 nopathinE2] by auto

  with forest_subE[OF f1] have "Upair a b \<in> E" by auto
  from abE1 abE2 have abdif: "Upair a b \<in> E1 - E2" by auto
  with e1 have "Upair a b \<in> E - E2" by auto

\<comment> \<open>we can savely add this edge {a,b} to E2 and obtain a bigger forest\<close>    
  have "forest (insert (Upair a b) E2)" apply(subst augment_forest)
    by fact+
  then show "\<exists>e\<in>E1-E2. forest (insert e E2)" using abdif
    by blast
qed

sublocale minWeightBasis E forest weight  
proof  
  have "forest {}" using forest_empty by auto
  then show "\<exists>X. forest X" by blast 
qed (auto simp: forest_subE forest_mono augment)

end

locale Kruskal_intermediate_time = Kruskal_intermediate +
 fixes     
       empty_forest_time  empty_uf_time indep_test_time insert_time insert_uf_time :: nat 
    and getEdges_time sort_time :: nat 
begin


sublocale minWeightBasis_time E forest weight      "getEdges_time + sort_time"
     "empty_forest_time + empty_uf_time" indep_test_time "insert_time+insert_uf_time" 
  apply unfold_locales .


end

end