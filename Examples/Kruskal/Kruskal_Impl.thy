theory Kruskal_Impl
imports Kruskal_Refine "../../Refine_Imperative_HOL/Sepref"
begin



definition "sort_edges \<equiv> quicksort_by_rel edges_less_eq []"


definition "max_node l \<equiv> Max (insert 0 (fst`set l \<union> (snd o snd)`set l))"

lemma max_node_impl[code]: "max_node l = fold (\<lambda>(u,_,w) x. max u (max w x)) l 0"
proof -
  have "fold (\<lambda>(u,_,w) x. max u (max w x)) l a = Max (insert a (fst`set l \<union> (snd o snd)`set l))" for a
    apply (induction l arbitrary: a)
    apply (auto simp:  )
    subgoal for a b l aa
      apply (cases l)
      by (auto simp: ac_simps)
    done
  thus ?thesis unfolding max_node_def by auto
qed

lemma set_uprod_nonempty[simp]: "set_uprod x \<noteq> {}"
  apply(cases x) by auto

locale Kruskal_intermediate_Impl = Kruskal_intermediate E forest connected path weight for E forest connected path 
      and weight :: "nat uprod \<Rightarrow> int"  +
    fixes getEdges  :: "(nat \<times> int \<times> nat) list nres"
      and getEdges_impl :: "(nat \<times> int \<times> nat) list Heap"
    assumes  
        getEdges_refine: "getEdges \<le> SPEC (\<lambda>L. lst_graph_P' weight L E)"
      and
        getEdges_impl: "(uncurry0 getEdges_impl, uncurry0 getEdges) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a list_assn (nat_assn \<times>\<^sub>a int_assn \<times>\<^sub>a nat_assn)"
      and
         E_nonempty: "E\<noteq>{}"
begin




       
definition "obtain_sorted_carrier''' =
      do {
    l \<leftarrow> getEdges;
    RETURN (quicksort_by_rel edges_less_eq [] l, max_node l)
}" 

definition "is_linorder_rel R \<equiv> (\<forall>x y. R x y \<or> R y x) \<and> (\<forall>x y z. R x y \<longrightarrow> R y z \<longrightarrow> R x z)"
lemma edges_less_eq_linorder: "is_linorder_rel edges_less_eq"
  unfolding edges_less_eq_def is_linorder_rel_def
  by (metis linear order_trans)
lemma sort_edges_correct: "sorted_wrt edges_less_eq (quicksort_by_rel edges_less_eq [] l)"
  by (metis (no_types, hide_lams) edges_less_eq_linorder is_linorder_rel_def sorted_wrt_quicksort_by_rel)

lemma distinct_mset_eq:"distinct a \<Longrightarrow> mset a = mset b \<Longrightarrow> distinct b"
  by (metis card_distinct distinct_card set_mset_mset size_mset)

lemma quicksort_by_rel_distinct: "distinct l \<Longrightarrow> distinct (quicksort_by_rel edges_less_eq [] l)"
  by (auto intro: distinct_mset_eq)

definition "add_size_rel   = br fst (\<lambda>(l,n). n= Max V)"



lemma max_node_is_Max_V: " E = (\<lambda>(a, _, y). Upair a y) ` set la \<Longrightarrow> max_node la = Max V"
proof -
  assume E: "E = (\<lambda>(a, _, y). Upair a y) ` set la"
  have pff: "fst ` set la \<union> (snd \<circ> snd) ` set la = (\<Union>x\<in>set la. case x of (x1, x1a, x2a) \<Rightarrow> {x1, x2a})"
    apply auto by (metis image_comp img_snd)
  have "V \<noteq> {}" using E_nonempty V_def by auto
  then have Mo: "Max V = Max (insert 0 V)" by auto
  show ?thesis unfolding Mo unfolding V_def
  unfolding E apply simp 
  by (auto simp add:  max_node_def prod.case_distrib pff ) 
qed


lemma obtain_sorted_carrier'''_refine: "(obtain_sorted_carrier''', obtain_sorted_carrier'') \<in> \<langle>add_size_rel\<rangle>nres_rel"
  unfolding obtain_sorted_carrier'''_def obtain_sorted_carrier''_def
  apply(refine_rcg getEdges_refine)  
  by (auto intro!: RETURN_SPEC_refine simp:   quicksort_by_rel_distinct sort_edges_correct
          add_size_rel_def in_br_conv lst_graph_P_def max_node_is_Max_V
         dest!: distinct_mapI)

 definition kruskal3 :: "(nat \<times> int \<times> nat) list nres"
   where "kruskal3  \<equiv> do {
    (sl,mn) \<leftarrow> obtain_sorted_carrier''';
    let initial_union_find = per_init' (mn + 1);
    (per, spanning_forest) \<leftarrow> nfoldli sl (\<lambda>_. True)
        (\<lambda>(a,w,b) (uf, T). do { 
            ASSERT (a \<in> Domain uf \<and> b \<in> Domain uf);
            if \<not> per_compare uf a b then
              do { 
                let uf = per_union uf a b;
                ASSERT ((a,w,b)\<notin>set T);
                RETURN (uf, T@[(a,w,b)])
              }
            else 
              RETURN (uf,T)
        }) (initial_union_find, []);
        RETURN spanning_forest
      }"


  definition per_supset_rel :: "('a per \<times> 'a per) set" where
    "per_supset_rel
      \<equiv> {(p1,p2). p1 \<inter> Domain p2 \<times> Domain p2 = p2 \<and> p1 - (Domain p2 \<times> Domain p2) \<subseteq> Id}"

  lemma per_supset_rel_dom: "(p1, p2) \<in> per_supset_rel \<Longrightarrow> Domain p1 \<supseteq> Domain p2"
    by (auto simp: per_supset_rel_def)
  
  lemma per_supset_compare:
    "(p1, p2) \<in> per_supset_rel \<Longrightarrow> x1\<in>Domain p2 \<Longrightarrow> x2\<in>Domain p2 \<Longrightarrow> per_compare p1 x1 x2 \<longleftrightarrow> per_compare p2 x1 x2"
    by (auto simp: per_supset_rel_def)
  
  lemma per_supset_union: "(p1, p2) \<in> per_supset_rel \<Longrightarrow> x1\<in>Domain p2 \<Longrightarrow> x2\<in>Domain p2 \<Longrightarrow>
    (per_union p1 x1 x2, per_union p2 x1 x2) \<in> per_supset_rel"
    apply (clarsimp simp: per_supset_rel_def per_union_def Domain_unfold )
    apply (intro subsetI conjI)
    apply blast
    apply force
    done

lemma per_initN_refine: "(per_init' (Max V + 1), per_init V) \<in> per_supset_rel"
  unfolding per_supset_rel_def per_init'_def per_init_def max_node_def
  by (auto simp: less_Suc_eq_le  ) 

theorem kruskal3_refine: "(kruskal3, kruskal2)\<in>\<langle>Id\<rangle>nres_rel"
  unfolding kruskal2_def kruskal3_def Let_def
  apply (refine_rcg obtain_sorted_carrier'''_refine[THEN nres_relD]   )
  supply RELATESI[where R="per_supset_rel::(nat per \<times> _) set", refine_dref_RELATES]
         apply refine_dref_type 
         apply (simp add: add_size_rel_def in_br_conv)
  using per_initN_refine apply (simp add: add_size_rel_def in_br_conv)
  by (auto simp add: add_size_rel_def in_br_conv per_supset_compare
                per_supset_union
             dest: per_supset_rel_dom
             simp del: per_compare_def )
 



section \<open>Kruskal\<close>


lemma [sepref_import_param]: "(sort_edges,sort_edges)\<in>\<langle>Id\<times>\<^sub>rId\<times>\<^sub>rId\<rangle>list_rel \<rightarrow>\<langle>Id\<times>\<^sub>rId\<times>\<^sub>rId\<rangle>list_rel" by simp
lemma [sepref_import_param]: "(max_node, max_node) \<in> \<langle>Id\<times>\<^sub>rId\<times>\<^sub>rId\<rangle>list_rel \<rightarrow> nat_rel" by simp

  sepref_register "getEdges" :: "(nat \<times> int \<times> nat) list nres"
 
 
declare getEdges_impl [sepref_fr_rules]

sepref_definition kruskal is
  "uncurry0 kruskal3" :: "(unit_assn)\<^sup>k \<rightarrow>\<^sub>a list_assn (nat_assn \<times>\<^sub>a int_assn \<times>\<^sub>a nat_assn)"
  unfolding kruskal3_def obtain_sorted_carrier'''_def 
  unfolding sort_edges_def[symmetric]
  apply (rewrite at "nfoldli _ _ _ (_,\<hole>)" HOL_list.fold_custom_empty)
  by sepref 

thm kruskal3_refine kruskal2_refine   kruskal1_refine kruskal0_refine minWeightBasis3_refine

abbreviation "MST == minBasis"

(* TODO: *) 

lemmas kruskal3_ref_spec = kruskal3_refine[FCOMP kruskal2_refine,
            FCOMP kruskal1_refine,
            FCOMP kruskal0_refine,
            FCOMP minWeightBasis3_refine] 

  lemma [fcomp_norm_simps]: "list_assn (nat_assn \<times>\<^sub>a int_assn \<times>\<^sub>a nat_assn) = id_assn"
    by (auto simp: list_assn_pure_conv)
lemmas kruskal_ref_spec = kruskal.refine[FCOMP kruskal3_ref_spec]


lemma kruskal_correct_forest:
  shows "<emp> kruskal <\<lambda>r. \<up>( MST (set (map \<alpha>' r)))>\<^sub>t"
proof -
  show ?thesis
    using kruskal_ref_spec[to_hnr]
    unfolding hn_refine_def lst_graph_rel_alt
    apply clarsimp
    apply (erule cons_post_rule)
    by (sep_auto simp: hn_ctxt_def pure_def list_set_rel_def in_br_conv
              dest: list_relD)     
qed

 




end



end