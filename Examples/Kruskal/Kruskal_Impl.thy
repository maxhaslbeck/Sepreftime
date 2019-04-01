theory Kruskal_Impl
  imports Kruskal_Refine "../../Refine_Imperative_HOL/IICF/Impl/IICF_DArray_List"
        UnionFind_Impl
begin

context
  fixes t ::  "nat \<Rightarrow> nat"
begin
  definition mop_sortEdges   where
    "mop_sortEdges l = (SPECT (emb (\<lambda>(L,n). n= Max (insert 0 (set (map fst L) \<union> set (map (snd o snd) L))) \<and> sorted_wrt edges_less_eq L \<and> distinct L \<and> set L = set l) (enat (t (length l)))))"
  
    sepref_register "mop_sortEdges"  
end

locale sortMaxnode = 
  fixes sortEdges_impl :: "(nat \<times> int \<times> nat) list \<Rightarrow> ((nat \<times> int \<times> nat) list * nat) Heap" 
    and sort_time' :: "nat \<Rightarrow> nat"
  assumes   
      sortEdges_impl[sepref_fr_rules]: "\<And>t. (sortEdges_impl, PR_CONST (mop_sortEdges t)) \<in>
        [\<lambda>l. sort_time' (length l) \<le> t (length l)]\<^sub>a
      (list_assn (nat_assn \<times>\<^sub>a int_assn \<times>\<^sub>a nat_assn))\<^sup>k \<rightarrow> (list_assn (nat_assn \<times>\<^sub>a int_assn \<times>\<^sub>a nat_assn)\<times>\<^sub>a nat_assn)"



 

  
lemma set_uprod_nonempty[simp]: "set_uprod x \<noteq> {}"
  apply(cases x) by auto


locale Kruskal_intermediate_Impl0 = Kruskal_intermediate E forest connected path weight for E forest connected path 
      and weight :: "nat uprod \<Rightarrow> int"  +
    fixes getEdges  :: "(nat \<times> int \<times> nat) list nrest"
      and getEdges_impl :: "(nat \<times> int \<times> nat) list Heap" 
      and getEdges_time sort_time :: nat
(*      and sortEdges  :: "(nat \<times> int \<times> nat) list \<Rightarrow> ((nat \<times> int \<times> nat) list * nat) nrest"
      and sortEdges_impl :: "(nat \<times> int \<times> nat) list \<Rightarrow> ((nat \<times> int \<times> nat) list * nat) Heap" *)
      and empty_uf_time indep_test_time insert_uf_time :: nat
    assumes           
        E_nonempty: "E\<noteq>{}"
      and  
        getEdges_refine: "getEdges \<le> \<Down> Id (SPECT (emb (\<lambda>L. lst_graph_P' weight L E) (enat getEdges_time)))"
      and
        getEdges_impl[sepref_fr_rules]: "(uncurry0 getEdges_impl, uncurry0 getEdges) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a list_assn (nat_assn \<times>\<^sub>a int_assn \<times>\<^sub>a nat_assn)"
(*       and
        sortEdges_refine': "sortEdges l \<le> (SPECT (emb (\<lambda>(L,n). n= Max (set (map fst l) \<union> set (map (snd o snd) l)) \<and> sorted_wrt edges_less_eq L \<and> distinct L \<and> set L = set l) (enat sort_time)))"
     and
        sortEdges_impl[sepref_fr_rules]: "(sortEdges_impl, sortEdges) \<in>
                (list_assn (nat_assn \<times>\<^sub>a int_assn \<times>\<^sub>a nat_assn))\<^sup>k \<rightarrow>\<^sub>a (list_assn (nat_assn \<times>\<^sub>a int_assn \<times>\<^sub>a nat_assn)\<times>\<^sub>a nat_assn)"
     
*)
                                                   
begin

thm conc_fun_br

abbreviation "sortEdges \<equiv> mop_sortEdges (\<lambda>_. sort_time)"


(*
lemma sortEdges_refine: 
  assumes a: "V = set (map fst l) \<union> set (map (snd o snd) l)"
    shows "sortEdges l = \<Down> (br fst (\<lambda>(l,n). n= Max V)) (SPECT (emb (\<lambda>L. sorted_wrt edges_less_eq L \<and> distinct L \<and> set L = set l) (enat sort_time)))"
proof -
  have gg: "(\<lambda>x. (case x of (l, n) \<Rightarrow> n = Max V) \<and> sorted_wrt edges_less_eq (fst x) \<and> distinct (fst x) \<and> set (fst x) = set l)
        =(\<lambda>(L, n). n = Max (set (map fst l) \<union> set (map (snd o snd) l)) \<and> sorted_wrt edges_less_eq L \<and> distinct L \<and> set L = set l)"
    unfolding a by auto
  show ?thesis 
    apply(simp only: conc_fun_br gg) by(rule sortEdges_refine')
qed *)

abbreviation "insert_time \<equiv> 23"
abbreviation "empty_forest_time \<equiv> 12"


sublocale Kruskal_intermediate_time  E forest connected  path weight
        empty_forest_time empty_uf_time indep_test_time insert_time insert_uf_time getEdges_time sort_time
  apply unfold_locales .



term obtain_sorted_carrier''
       
definition (in -) obtain_sorted_carrier'''_aux  where
  "obtain_sorted_carrier'''_aux gE sE c =
      do {
    l \<leftarrow> gE;
    ASSERT (length l = card c);
    sE l
}" 

abbreviation "obtain_sorted_carrier''' \<equiv> obtain_sorted_carrier'''_aux getEdges sortEdges E"
 
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

lemma lst_graph_P_V: "lst_graph_P la E \<Longrightarrow> V = (fst ` set la \<union> (snd \<circ> snd) ` set la)" 
  apply (auto simp: emb_eq_Some_conv lst_graph_P_def V_def)
  subgoal 
    by blast 
  subgoal  
    by (metis image_comp img_snd) 
  done

 

lemma  k: "\<And>V::nat set. finite V \<Longrightarrow> V \<noteq> {} \<Longrightarrow> Max V = Max (insert 0 V)" by auto

lemma *: "(la::((nat*int*nat) list)) \<noteq> [] \<Longrightarrow> Max (insert 0 (fst ` set la \<union> (snd \<circ> snd) ` set la)) = Max (fst ` set la \<union> (snd \<circ> snd) ` set la)"
proof -
  assume "la \<noteq> []"
  then have "fst ` set la \<union> (snd \<circ> snd) ` set la \<noteq> {}" by auto
  then show ?thesis apply(intro k[symmetric])  apply simp by simp
qed


lemma obtain_sorted_carrier'''_refine: "obtain_sorted_carrier''' \<le> \<Down>add_size_rel obtain_sorted_carrier''"
  unfolding obtain_sorted_carrier'''_aux_def  add_size_rel_def
  apply(rule bindT_refine')      
   apply(rule getEdges_refine) apply safe
  apply(auto simp: emb_eq_Some_conv  dest!:  split: if_splits)
  unfolding conc_fun_br  mop_sortEdges_def 
  apply(auto  simp: le_fun_def emb'_def dest: lst_graph_P_V split: if_splits)
  apply(rule le_R_ASSERTI)
  apply(rule ASSERT_leI) apply simp
  apply(rule SPECT_refine) apply (auto split: if_splits)    
  apply(subst * ) subgoal apply auto using E_nonempty by auto
  by (metis (mono_tags) fst_conv in_br_conv lst_graph_P_V prod_case_simp) 
   
    

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
    (sl,mn) \<leftarrow> obtain_sorted_carrier'''_aux gE sE E;
    ASSERT (mn = Max (Kruskal_intermediate_defs.V E));
    s \<leftarrow> initState''_aux mn eft eut ;
    (per, spanning_forest) \<leftarrow> nfoldli sl (\<lambda>_. True)
        (\<lambda>(a,w,b) (uf, T). do { 
            ASSERT (a \<in> Domain uf \<and> b \<in> Domain uf);
            ASSERT ( card (Domain uf) = Max (Kruskal_intermediate_defs.V E) + 1);
            i \<leftarrow> notcompare uf a b itt;
            if i then
              do { 
                ASSERT ((a,w,b)\<notin>set T);
                addEdge''_aux uf a w b T iut it
              }
            else 
              RETURNT (uf,T)
        }) s;
        RETURNT spanning_forest
      }"

abbreviation "kruskal3 \<equiv> kruskal3_aux E getEdges sortEdges  empty_forest_time empty_uf_time
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
  subgoal by(auto simp: kk_rel_def) 
  subgoal apply(auto dest!: kk_relD simp: SPECT_bind_RETURNT le_fun_def notcompare_def mop_per_compare_def)
    by (meson Domain.simps local.per_supset_compare per_compare_def)+  
  subgoal unfolding addEdge'_aux_def addEdge''_aux_def mop_per_union_def mop_push_list_def
    apply(refine_rcg)
     apply refine_dref_type            
    subgoal apply (rule SPECT_refine) by (auto  split: if_splits intro: per_kk_rel_union)
    subgoal apply (rule RETURNT_refine) by(auto split: if_splits)   
    done
  done

end


       

locale Kruskal_intermediate_Impl = Kruskal_intermediate_Impl0
  + UnionFind_Impl + sortMaxnode   +
  assumes 
  [simp]:  "uf_init_time (Suc (Max V)) \<le> empty_uf_time" 
    "uf_cmp_time (Suc (Max V)) \<le> indep_test_time" 
    "uf_union_time (Suc (Max V)) \<le> insert_uf_time" 
    "sort_time' (card E) \<le> sort_time"
begin

section \<open>Kruskal\<close>


  lemma [fcomp_norm_simps]: "list_assn (nat_assn \<times>\<^sub>a int_assn \<times>\<^sub>a nat_assn) = id_assn"
    by (auto simp: list_assn_pure_conv)
  lemma [fcomp_norm_simps]: " (nat_assn \<times>\<^sub>a int_assn \<times>\<^sub>a nat_assn) = id_assn"
    by (auto simp: )

  lemma [sepref_import_param]: "(sort_edges,sort_edges)\<in>\<langle>Id\<times>\<^sub>rId\<times>\<^sub>rId\<rangle>list_rel \<rightarrow>\<langle>Id\<times>\<^sub>rId\<times>\<^sub>rId\<rangle>list_rel" by simp
  lemma [sepref_import_param]: "(max_node, max_node) \<in> \<langle>Id\<times>\<^sub>rId\<times>\<^sub>rId\<rangle>list_rel \<rightarrow> nat_rel" by simp

  sepref_register "getEdges" :: "(nat \<times> int \<times> nat) list nrest"
  sepref_register uf_init :: "nat \<Rightarrow> uf Heap"
  sepref_register uf_cmp :: "uf \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool Heap"
  sepref_register uf_union :: "uf \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> uf Heap"
 
declare getEdges_impl [sepref_fr_rules]

 

sepref_definition kruskal is
  "uncurry0 kruskal3" :: "(unit_assn)\<^sup>k \<rightarrow>\<^sub>a da_assn (nat_assn \<times>\<^sub>a int_assn \<times>\<^sub>a nat_assn)"
  unfolding kruskal3_aux_def obtain_sorted_carrier'''_aux_def initState''_aux_def
      addEdge''_aux_def notcompare_def nfoldli_def
  using [[goals_limit = 2]]
   
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

thm kruskal3_refine kruskal2_refine   kruskal1_refine kruskal0_refine minWeightBasis3_refine
 
thm kruskal.refine kruskal3_refine kruskal2_refine   kruskal1_refine kruskal0_refine minWeightBasis3_refine


abbreviation "MST == minBasis"

term minWeightBasis3

(* TODO: *) 

lemma k3: "(kruskal3,kruskal2) \<in> \<langle>Id\<rangle>nrest_rel"
  apply(rule nrest_relI) by (rule kruskal3_refine) 
lemma k2: "(kruskal2,kruskal1) \<in> \<langle>lst_graph_rel\<rangle>nrest_rel"
  apply(rule nrest_relI) by (rule kruskal2_refine) 
lemma k1: "(kruskal1,kruskal0) \<in> \<langle>Id\<rangle>nrest_rel"
  apply(rule nrest_relI) by (rule kruskal1_refine) 
lemma k0: "(kruskal0,minWeightBasis3) \<in> \<langle>Id\<rangle>nrest_rel"
  apply(rule nrest_relI) by (rule kruskal0_refine) 
lemma kmw: "(minWeightBasis3,SPECT (emb minBasis (enat minBasis_time))) \<in> \<langle>Id\<rangle>nrest_rel"
  apply(rule nrest_relI)  
  by (rule minWeightBasis3_refine)

lemmas k_ref_spec = k3[FCOMP k2, FCOMP k1, FCOMP k0, FCOMP kmw]


  lemma [fcomp_norm_simps]: "list_assn (nat_assn \<times>\<^sub>a int_assn \<times>\<^sub>a nat_assn) = id_assn"
    by (auto simp: list_assn_pure_conv)
lemmas kruskal_ref_spec = kruskal.refine[FCOMP k_ref_spec]

thm minBasis_time_def
lemma kruskal_correct_forest:
  shows "<$ minBasis_time> kruskal <\<lambda>r. (\<exists>\<^sub>Ara. hr_comp (da_assn id_assn) lst_graph_rel ra r * \<up> (MST ra))>\<^sub>t"
proof -
  thm extract_cost_ub 
  note l= hn_refine_ref[OF _  kruskal_ref_spec[to_hnr] ]
  thm extract_cost_ub[OF l, where Cost_ub="minBasis_time", simplified in_ran_emb_special_case]
  have ht: "<emp * $ minBasis_time> kruskal <\<lambda>r. emp * (\<exists>\<^sub>Ara. hr_comp (da_assn id_assn) lst_graph_rel ra r * \<up> (ra \<in> dom ((emb MST (enat minBasis_time)))))>\<^sub>t"
    apply(rule extract_cost_ub[OF l, where Cost_ub="minBasis_time" ])
    by (auto simp: in_ran_emb_special_case)  

  from ht show ?thesis by auto        
qed
thm minBasis_time_def 
end
(*
thm extract_cost_ub[where M= "(emb Pr t)", no_vars]

lemma "hn_refine \<Gamma> c \<Gamma>' R (SPECT (emb Pr t))  \<Longrightarrow>
<\<Gamma> * $ t> c <\<lambda>r. \<Gamma>' * (\<exists>\<^sub>Ara. R ra r * \<up> (Pr ra))>\<^sub>t"
proof -
  assume "hn_refine \<Gamma> c \<Gamma>' R (SPECT (emb Pr t))"
  from extract_cost_ub[OF this, of t]
  show ?thesis by (simp add: ran_emb')
qed
 

lemma array_length_rule_raw [hoare_triple]:
  "<dyn_array_raw (xs, n) p * $1>
   array_length p
   <\<lambda>r. dyn_array_raw (xs, n) p * \<up>(r = n)>"
  unfolding dyn_array'_def array_length_def 
  apply(cases p)
  by (sep_auto simp: zero_time)  
 

lemma array_max_rule_raw [hoare_triple]:
  "<dyn_array_raw (xs, n) p * $1>
   array_max p
   <\<lambda>r. dyn_array_raw (xs, n) p * \<up>(r = length xs)>"
  unfolding array_max_def 
  apply (cases p)
  by (sep_auto heap: length_rule simp: zero_time)  


lemma double_length_raw_rule2 [hoare_triple]:
  "length xs = n \<Longrightarrow>
   <dyn_array_raw (xs, length xs) p * $(length xs * 5 + 5)>
   double_length p
   <dyn_array_raw (double_length_fun (xs, n))>\<^sub>t" 
  using double_length_raw_rule[of xs n p] by(simp add: mult.commute) 

lemma push_array_raw_rule [hoare_triple]:
  "n \<le> length xs \<Longrightarrow>
   <dyn_array_raw (xs, n) p * $( length xs *5+9)>
   push_array x p
   <dyn_array_raw (push_array_fun x (xs, n))>\<^sub>t" 
  unfolding  
    push_array_def  
  apply(sep_auto heap: array_max_rule_raw push_array_basic_raw_rule
          array_length_rule_raw  double_length_raw_rule2)
  subgoal apply(subst array_copy_length) by simp_all
  by sep_auto

lemma push_array_rule''' [hoare_triple]:
  "n \<le> length xs \<Longrightarrow>
   <dyn_array' (xs, n) p * $19>
   push_array x p
   <dyn_array' (push_array_fun x (xs, n))>\<^sub>t" 
  unfolding  
    push_array_def
  apply(sep_auto heap: array_max_rule' array_length_rule' push_array_basic_rule')
   apply(sep_auto heap: double_length_rule' )
  using push_array_basic_rule'
  unfolding double_length_fun.simps
  apply(sep_auto simp only: heap: push_array_basic_rule')
  subgoal apply(subst array_copy_length) by simp_all
  by sep_auto
   
thm array_max_rule'

*)
end