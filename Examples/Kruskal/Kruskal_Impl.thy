theory Kruskal_Impl
imports Kruskal_Refine "../../Refine_Imperative_HOL/IICF/Impl/IICF_DArray_List"
begin

type_synonym uf = "nat array \<times> nat array"


context
  fixes t ::  "nat \<Rightarrow> nat"
begin

  definition "mop_per_init n = SPECT [ per_init' n \<mapsto> enat (t n) ]"

  lemma progress_mop_per_init[progress_rules]: "t n > 0 \<Longrightarrow> progress (mop_per_init n)"
    unfolding mop_per_init_def by (auto intro!: progress_rules simp add:   zero_enat_def) 

  lemma mop_per_init: "tt \<le> TTT Q (SPECT [ per_init' n \<mapsto> t n]) \<Longrightarrow> tt
           \<le> TTT Q (mop_per_init n)" unfolding mop_per_init_def by simp

  sepref_register "mop_per_init" 
end

context
  fixes t ::  "('a \<times> 'a) set \<Rightarrow> nat"
begin

  definition "mop_per_compare R a b = SPECT [ per_compare R a b \<mapsto> enat (t R) ]"
(*
  lemma progress_mop_per_init[progress_rules]: "t n > 0 \<Longrightarrow> progress (mop_per_init n)"
    unfolding mop_per_init_def by (auto intro!: progress_rules simp add:   zero_enat_def) 

  lemma mop_per_init: "tt \<le> TTT Q (SPECT [ per_init' n \<mapsto> t n]) \<Longrightarrow> tt
           \<le> TTT Q (mop_per_init n)" unfolding mop_per_init_def by simp
*)
  sepref_register "mop_per_compare" 
end

context
  fixes t ::  "('a \<times> 'a) set \<Rightarrow> nat"
begin

  definition "mop_per_union R a b = SPECT [ per_union R a b \<mapsto> enat (t R) ]"
(*
  lemma progress_mop_per_init[progress_rules]: "t n > 0 \<Longrightarrow> progress (mop_per_init n)"
    unfolding mop_per_init_def by (auto intro!: progress_rules simp add:   zero_enat_def) 

  lemma mop_per_init: "tt \<le> TTT Q (SPECT [ per_init' n \<mapsto> t n]) \<Longrightarrow> tt
           \<le> TTT Q (mop_per_init n)" unfolding mop_per_init_def by simp
*)
  sepref_register "mop_per_union" 
end





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
    fixes getEdges  :: "(nat \<times> int \<times> nat) list nrest"
      and getEdges_impl :: "(nat \<times> int \<times> nat) list Heap" 
      and getEdges_time sort_time :: nat
      and sortEdges  :: "(nat \<times> int \<times> nat) list \<Rightarrow> ((nat \<times> int \<times> nat) list * nat) nrest"
      and sortEdges_impl :: "(nat \<times> int \<times> nat) list \<Rightarrow> ((nat \<times> int \<times> nat) list * nat) Heap" 
      and is_uf :: "(nat\<times>nat) set \<Rightarrow> uf \<Rightarrow> assn"
      and uf_init :: "nat \<Rightarrow> uf Heap"
      and uf_cmp :: "uf \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool Heap"
      and uf_union :: "uf \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> uf Heap"
    assumes  
        getEdges_refine: "getEdges \<le> \<Down> Id (SPECT (emb (\<lambda>L. lst_graph_P' weight L E) (enat getEdges_time)))"
      and
        getEdges_impl[sepref_fr_rules]: "(uncurry0 getEdges_impl, uncurry0 getEdges) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a list_assn (nat_assn \<times>\<^sub>a int_assn \<times>\<^sub>a nat_assn)"
      and
        sortEdges_refine: "sortEdges l \<le> \<Down> (br fst (\<lambda>(l,n). n= Max V)) (SPECT (emb (\<lambda>L. sorted_wrt edges_less_eq L \<and> distinct L \<and> set L = set l) (enat sort_time)))"
      and
        sortEdges_impl[sepref_fr_rules]: "(sortEdges_impl, sortEdges) \<in>
                (list_assn (nat_assn \<times>\<^sub>a int_assn \<times>\<^sub>a nat_assn))\<^sup>k \<rightarrow>\<^sub>a (list_assn (nat_assn \<times>\<^sub>a int_assn \<times>\<^sub>a nat_assn)\<times>\<^sub>a nat_assn)"
      and
         E_nonempty: "E\<noteq>{}"
      and

per_init'_sepref_rule[sepref_fr_rules]:  "\<And>t x' x. 10 * x' \<le> t x' \<Longrightarrow>
     hn_refine (hn_ctxt nat_assn x' x) (uf_init x)
         (hn_ctxt nat_assn x' x)  
             is_uf (PR_CONST (mop_per_init t) $  x' )" 

  and

per_compare_sepref_rule[sepref_fr_rules]:  "\<And>t R' R a' a b' b . 10 \<le> t R' \<Longrightarrow>
     hn_refine (hn_ctxt is_uf R' R * hn_ctxt nat_assn a' a * hn_ctxt nat_assn b' b) (uf_cmp R a b)
         (hn_ctxt is_uf R' R * hn_ctxt nat_assn a' a * hn_ctxt nat_assn b' b) 
             bool_assn (PR_CONST (mop_per_compare t) $  R' $ a' $ b' )" 

  and

per_union_sepref_rule[sepref_fr_rules]:  "\<And>t R' R a' a b' b . a' \<in> Domain R' \<and> b' \<in> Domain R'
  \<Longrightarrow> 100 * card (Domain R') \<le> t R' \<Longrightarrow> 
     hn_refine (hn_ctxt is_uf R' R * hn_ctxt nat_assn a' a * hn_ctxt nat_assn b' b) (uf_union R a b)
         (hn_invalid is_uf R' R * hn_ctxt nat_assn a' a * hn_ctxt nat_assn b' b) 
             uf_assn (PR_CONST (mop_per_union t) $  R' $ a' $ b' )" 
                                                      
begin

abbreviation "insert_time \<equiv> 23"
abbreviation "empty_forest_time \<equiv> 12"

(* ! ! TODO  *)
abbreviation "empty_uf_time \<equiv> 10*(Max (Kruskal_intermediate_defs.V E)+1) "
abbreviation "indep_test_time \<equiv> 10"
abbreviation "insert_uf_time \<equiv> 100 * (Max (Kruskal_intermediate_defs.V E)+1) "

sublocale Kruskal_intermediate_time  E forest connected  path weight
        empty_forest_time empty_uf_time indep_test_time insert_time insert_uf_time getEdges_time sort_time
  apply unfold_locales .



term obtain_sorted_carrier''
       
definition (in -) obtain_sorted_carrier'''_aux :: "(nat \<times> int \<times> nat) list nrest \<Rightarrow> _ \<Rightarrow> ((nat \<times> int \<times> nat) list \<times> nat) nrest" where
  "obtain_sorted_carrier'''_aux gE sE =
      do {
    l \<leftarrow> gE;
    sE l
}" 

abbreviation "obtain_sorted_carrier''' \<equiv> obtain_sorted_carrier'''_aux getEdges sortEdges"


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


lemma obtain_sorted_carrier'''_refine: "obtain_sorted_carrier''' \<le> \<Down>add_size_rel obtain_sorted_carrier''"
  unfolding obtain_sorted_carrier'''_aux_def  add_size_rel_def
  apply(refine_rcg getEdges_refine )  
  using sortEdges_refine by auto

definition (in -) initState''_aux where
  "initState''_aux mn eft eut\<equiv> do {
    initial_union_find \<leftarrow> mop_per_init (\<lambda>_. eut) (mn + 1);
    ASSERT ( card (Domain initial_union_find) = mn + 1);
    e \<leftarrow> mop_empty_list eft;
    RETURNT (initial_union_find, e)      
    }" 


abbreviation "initState'' mn == initState''_aux mn empty_forest_time empty_uf_time"

 definition (in -) "addEdge''_aux uf a w b T iut it = do {
  uf \<leftarrow> mop_per_union (\<lambda>_. iut) uf a b;
  T' \<leftarrow> mop_push_list (\<lambda>_.  it) (a,w,b) T;
  RETURNT (uf, T')
  }"

abbreviation "addEdge'' uf a w b T == addEdge''_aux uf a w b T insert_uf_time insert_time"

definition (in -) "notcompare uf a b itt = do {
      i \<leftarrow> mop_per_compare (\<lambda>_. itt) uf a b;
      RETURNT (\<not>i)
     }"


 definition (in -) kruskal3_aux 
   where "kruskal3_aux E gE sE eft eut iut it   itt \<equiv> do {
    (sl,mn) \<leftarrow> obtain_sorted_carrier'''_aux gE sE;
    ASSERT (mn = Max (Kruskal_intermediate_defs.V E));
    s \<leftarrow> initState''_aux mn eft eut ;
    (per, spanning_forest) \<leftarrow> nfoldli sl (\<lambda>_. True)
        (\<lambda>(a,w,b) (uf, T). do { 
            ASSERT (a \<in> Domain uf \<and> b \<in> Domain uf);
            i \<leftarrow> notcompare uf a b itt;
            if i then
              do { 
                ASSERT ((a,w,b)\<notin>set T);
                ASSERT ( card (Domain uf) = Max (Kruskal_intermediate_defs.V E) + 1);
                addEdge''_aux uf a w b T iut it
              }
            else 
              RETURNT (uf,T)
        }) s;
        RETURNT spanning_forest
      }"

abbreviation "kruskal3 \<equiv> kruskal3_aux E getEdges sortEdges empty_forest_time empty_uf_time
                      insert_uf_time  insert_time  indep_test_time"

  definition per_supset_rel :: "('a per \<times> 'a per) set" where
    "per_supset_rel
      \<equiv> {(p1,p2). p1 \<inter> Domain p2 \<times> Domain p2 = p2 \<and> p1 - (Domain p2 \<times> Domain p2) \<subseteq> Id}"

 definition "kk_rel n \<equiv> per_supset_rel \<inter> ({p. Domain p = {0..<n}} \<times> UNIV)"

lemma kk_relD: "x\<in> kk_rel n \<Longrightarrow> x\<in>per_supset_rel" unfolding kk_rel_def by auto

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

  lemma per_kk_rel_union: 
    assumes "(p1, p2) \<in> kk_rel n" and inDom: "x1\<in>Domain p2" "x2\<in>Domain p2"
    shows "(per_union p1 x1 x2, per_union p2 x1 x2) \<in> kk_rel n"
  proof -
    from assms(1) have "(p1, p2) \<in> per_supset_rel" by(auto dest: kk_relD)
    with inDom have ss: "(per_union p1 x1 x2, per_union p2 x1 x2) \<in> per_supset_rel" 
      by(auto intro: per_supset_union)

    from assms(1) have "Domain p1 = {0..<n}" by (auto simp: kk_rel_def)
    then have "Domain (per_union p1 x1 x2) = {0..<n}" by simp
    with ss show ?thesis unfolding kk_rel_def by auto
  qed

lemma per_initN_refine: "(per_init' (Max V + 1), per_init V) \<in> per_supset_rel"
  unfolding per_supset_rel_def per_init'_def per_init_def max_node_def
  by (auto simp: less_Suc_eq_le  ) 

lemma per_init'_refine: "SPECT [per_init' (Max V  + 1) \<mapsto> enat empty_uf_time] \<le> \<Down> per_supset_rel (SPECT [per_init V \<mapsto> enat empty_uf_time])"
  apply(rule SPECT_refine)   using per_initN_refine by (auto split: if_splits)
  
lemma gg: "{(i, i) |i. i < X} = (\<lambda>i. (i,i)) ` {i. i < X}" by auto
   

lemma ff: "\<And>X. card (Domain {(i, i) |i. i < X}) = X"
  unfolding Domain_fst apply(subst card_image)
  subgoal by (smt fst_conv inj_onI mem_Collect_eq) 
  subgoal unfolding gg apply(subst card_image) by auto  
  done


lemma initState''_refine: "initState'' (Max V) \<le> \<Down>(kk_rel (Max V + 1) \<times>\<^sub>r Id) initState'"
  unfolding initState'_aux_def initState''_aux_def mop_empty_list_def  kk_rel_def
  unfolding mop_per_init_def
  apply(rule bindT_refine') apply(rule per_init'_refine)

  apply(refine_rcg  ) 
  subgoal by (auto split: if_splits simp: ff   per_init'_def )   
  unfolding conc_fun_RES 
    apply(rule T_specifies_I)               
  apply(vcg' \<open>-\<close>  )  
  apply(rule Sup_upper)  by (auto simp: per_init'_def numeral_eq_enat split: if_splits)  

   

lemma SPECT_bind_RETURNT: "SPECT [x \<mapsto> t] \<bind> (\<lambda>i. RETURNT (f i)) = SPECT [f x \<mapsto> t]"
  unfolding bindT_def by(auto split: nrest.split)

theorem kruskal3_refine: "kruskal3 \<le> \<Down> Id kruskal2"
  unfolding kruskal2_aux_def kruskal3_aux_def Let_def
  apply (refine_rcg obtain_sorted_carrier'''_refine   )
            (*supply RELATESI[where R="per_supset_rel::(nat per \<times> _) set", refine_dref_RELATES]*)
            supply RELATESI[where R="kk_rel (Max V + 1)::(nat per \<times> _) set", refine_dref_RELATES]
             apply refine_dref_type 
  subgoal unfolding add_size_rel_def by (auto simp: in_br_conv)
  subgoal apply (simp add: add_size_rel_def in_br_conv  )
    using initState''_refine  by simp  
          apply (auto simp add: add_size_rel_def in_br_conv per_supset_compare
                        per_supset_union 
                      dest: per_supset_rel_dom
                      simp del: per_compare_def )
  subgoal by(auto dest!: kk_relD per_supset_rel_dom)    
  subgoal by(auto dest!: kk_relD per_supset_rel_dom)  
  subgoal apply(auto dest!: kk_relD simp: SPECT_bind_RETURNT le_fun_def notcompare_def mop_per_compare_def)
    by (meson Domain.simps local.per_supset_compare per_compare_def)+ 
  subgoal by(auto simp: kk_rel_def) 
  subgoal unfolding addEdge'_aux_def addEdge''_aux_def mop_per_union_def mop_push_list_def
    apply(refine_rcg)
     apply refine_dref_type            
    subgoal apply (rule SPECT_refine) by (auto  split: if_splits intro: per_kk_rel_union)
    subgoal apply (rule RETURNT_refine) by(auto split: if_splits)   
    done
  done



section \<open>Kruskal\<close>


  lemma [fcomp_norm_simps]: "list_assn (nat_assn \<times>\<^sub>a int_assn \<times>\<^sub>a nat_assn) = id_assn"
    by (auto simp: list_assn_pure_conv)
  lemma [fcomp_norm_simps]: " (nat_assn \<times>\<^sub>a int_assn \<times>\<^sub>a nat_assn) = id_assn"
    by (auto simp: )

lemma [sepref_import_param]: "(sort_edges,sort_edges)\<in>\<langle>Id\<times>\<^sub>rId\<times>\<^sub>rId\<rangle>list_rel \<rightarrow>\<langle>Id\<times>\<^sub>rId\<times>\<^sub>rId\<rangle>list_rel" by simp
lemma [sepref_import_param]: "(max_node, max_node) \<in> \<langle>Id\<times>\<^sub>rId\<times>\<^sub>rId\<rangle>list_rel \<rightarrow> nat_rel" by simp

  sepref_register "getEdges" :: "(nat \<times> int \<times> nat) list nrest"
  sepref_register "sortEdges" :: "(nat \<times> int \<times> nat) list \<Rightarrow> ((nat \<times> int \<times> nat) list * nat) nrest"
  sepref_register uf_init :: "nat \<Rightarrow> uf Heap"
  sepref_register uf_cmp :: "uf \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool Heap"
  sepref_register uf_union :: "uf \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> uf Heap"
 
declare getEdges_impl [sepref_fr_rules]

 

sepref_definition kruskal is
  "uncurry0 kruskal3" :: "(unit_assn)\<^sup>k \<rightarrow>\<^sub>a da_assn (nat_assn \<times>\<^sub>a int_assn \<times>\<^sub>a nat_assn)"
  unfolding kruskal3_aux_def obtain_sorted_carrier'''_aux_def initState''_aux_def
      addEdge''_aux_def notcompare_def nfoldli_def
  using [[goals_limit = 2]]
  by sepref (*
  apply sepref_dbg_preproc
  apply sepref_dbg_cons_init
  apply sepref_dbg_id 
     apply sepref_dbg_monadify

         apply sepref_dbg_opt_init

  apply sepref_dbg_trans      
 
  apply sepref_dbg_opt
  apply sepref_dbg_cons_solve \<comment> \<open>Frame rule, recovering the invalidated list 
    or pure elements, propagating recovery over the list structure\<close>
  apply sepref_dbg_cons_solve \<comment> \<open>Trivial frame rule\<close>
  apply sepref_dbg_constraints
      done 
 *)


thm kruskal3_refine kruskal2_refine   kruskal1_refine kruskal0_refine minWeightBasis3_refine
 
thm kruskal.refine kruskal3_refine kruskal2_refine   kruskal1_refine kruskal0_refine minWeightBasis3_refine


abbreviation "MST == minBasis"

(* TODO: *) 

lemmas kruskal3_ref_spec = kruskal3_refine[FCOMP kruskal2_refine,
            FCOMP kruskal1_refine,
            FCOMP kruskal0_refine] 

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