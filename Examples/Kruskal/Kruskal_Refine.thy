theory Kruskal_Refine
imports Kruskal   "../../Refine_Heuristics" UnionFind
begin
 
definition edges_less_eq :: "('a \<times> 'w::{linorder, ordered_comm_monoid_add} \<times> 'a) \<Rightarrow> ('a \<times> 'w \<times> 'a) \<Rightarrow> bool"
  where "edges_less_eq a b \<equiv> fst(snd a) \<le> fst(snd b)"

context Kruskal_intermediate_time
begin


thm  minWeightBasis3_refine
thm minWeightBasis3_aux_def

thm obtain_sorted_carrier_aux_def
term wsorted

definition (in -) "\<alpha> = (\<lambda>(x,y). Upair x y)"

definition (in -) wsorted_wrt_w' where "wsorted_wrt_w' w == sorted_wrt (\<lambda>x y. w (\<alpha> x) \<le> w (\<alpha> y))"

abbreviation "wsorted' \<equiv> wsorted_wrt_w' weight"

lemma wsorted_map\<alpha>[simp]: "wsorted' s \<Longrightarrow> wsorted (map \<alpha> s)"
  by(auto simp: wsorted_wrt_w'_def sorted_wrt_map) 

definition (in -) "obtain_sorted_carrier'_aux c w obst == SPECT (emb (\<lambda>L. wsorted_wrt_w' w L \<and> distinct (map \<alpha> L) \<and> \<alpha> ` set L = c) obst)"


abbreviation "obtain_sorted_carrier' == obtain_sorted_carrier'_aux E weight (getEdges_time + sort_time)"


definition RR :: "(('a \<times> 'a)  \<times> 'a uprod) set" where "RR \<equiv> {( (cx,cy) , a). Upair cx cy = a }"


lemma RR_alt: "RR = br \<alpha> (\<lambda>_. True)"
  unfolding RR_def br_def \<alpha>_def by auto

lemma "obtain_sorted_carrier' \<le> \<Down>(list_rel RR) obtain_sorted_carrier"
  unfolding obtain_sorted_carrier'_aux_def obtain_sorted_carrier_aux_def 
  oops

lemma obtain_sorted_carrier'_refine:
  "obtain_sorted_carrier' \<le> \<Down> (\<langle>RR\<rangle>list_rel) obtain_sorted_carrier"
  unfolding obtain_sorted_carrier'_aux_def obtain_sorted_carrier_aux_def 
  apply(rule SPECT_refine)
  unfolding RR_alt 
  subgoal for s apply(rule exI[where x="map \<alpha> s"])
    by(auto simp: map_in_list_rel_conv in_br_conv vcg_simp_rules)  
  done


abbreviation "empty_forest \<equiv> {}"

definition kruskal0 
  where "kruskal0 \<equiv> do {
    l \<leftarrow> obtain_sorted_carrier';
    s \<leftarrow> SPECT [empty_forest \<mapsto> enat (empty_forest_time+empty_uf_time)];
    spanning_forest \<leftarrow> nfoldli l (\<lambda>_. True)
        (\<lambda>(a,b) T. do { 
            ASSERT (Upair a b\<notin>T \<and> forest T \<and> Upair a b\<in>E \<and> T \<subseteq> E);
            i \<leftarrow> SPECT [\<not> (a,b) \<in> connected T \<mapsto> enat indep_test_time];
            if i then
              do { 
                ASSERT (Upair a b\<notin>T);
                SPECT [(insert (Upair a b) T) \<mapsto> enat (insert_time+insert_uf_time)]
              }
            else 
              RETURNT T
        }) s;
        RETURNT spanning_forest
      }"

lemma "(xi, x) \<in> RR \<Longrightarrow>  xi = (x1, x2) \<Longrightarrow> x = Upair x1 x2"
  unfolding RR_def  by auto


 
               
declare RETURNT_refine [simp]




lemma ff: "(sa, sa) \<in> Id" by auto

lemma ffs: "A \<le> B \<Longrightarrow> A \<le> \<Down> Id B" by auto

lemma kruskal0_refine: "kruskal0 \<le> \<Down>Id minWeightBasis3"
  unfolding kruskal0_def minWeightBasis3_aux_def 
  apply(refine_rcg obtain_sorted_carrier'_refine) 
           apply simp
          apply simp
          apply (rule ff)
  apply simp
  subgoal by(auto simp: RR_def augment_forest) 
  apply(rule ffs) 
  subgoal by(auto simp: RR_def augment_forest)
  subgoal by(auto simp: RR_def augment_forest)
  subgoal by(auto simp: RR_def augment_forest)
  subgoal by(auto simp: RR_def augment_forest)
  subgoal by(auto simp: RR_def augment_forest)
  subgoal by(auto simp: RR_def augment_forest)
  done

 
section "kruskal1 - using union find"



definition corresponding_union_find :: "'a per \<Rightarrow> 'a uprod set \<Rightarrow> bool"
  where "corresponding_union_find uf T \<equiv> (\<forall>a\<in>V. \<forall>b\<in>V.
      per_compare uf a b \<longleftrightarrow> ((a,b)\<in> connected T ))"

definition "uf_graph_invar uf_T \<equiv> case uf_T of (uf, T) \<Rightarrow> 
    corresponding_union_find uf T \<and>
    Domain uf = V"

lemma uf_graph_invarE: "uf_graph_invar (uf, T) \<Longrightarrow> corresponding_union_find uf T"
  unfolding uf_graph_invar_def by simp

definition "uf_graph_rel \<equiv> br snd uf_graph_invar"

lemma uf_graph_relsndD: "((a,b),c) \<in> uf_graph_rel \<Longrightarrow> b=c"
  by(auto simp: uf_graph_rel_def in_br_conv)   

lemma uf_graph_relD: "((a,b),c) \<in> uf_graph_rel \<Longrightarrow> b=c \<and> uf_graph_invar (a,b)"
  by(auto simp: uf_graph_rel_def in_br_conv)            


definition "initState = do {
  initial_union_find \<leftarrow> SPECT [per_init V \<mapsto> enat empty_uf_time];
       SPECT [(initial_union_find, empty_forest) \<mapsto> enat empty_forest_time]
  }"

definition "addEdge uf a b T = do {
    uf \<leftarrow> SPECT [per_union uf a b \<mapsto> enat insert_uf_time];
    SPECT [(uf, insert (Upair a b) T)\<mapsto>enat insert_time]
  }"





definition kruskal1
  where "kruskal1 \<equiv> do {
    l \<leftarrow> obtain_sorted_carrier';
    s \<leftarrow> initState;
    (per, spanning_forest) \<leftarrow> nfoldli l (\<lambda>_. True)
        (\<lambda>(a,b) (uf, T). do { 
            ASSERT (Domain uf = Domain (fst s));
            ASSERT (a\<in>V \<and> b\<in>V \<and> a \<in> Domain uf \<and> b \<in> Domain uf \<and> a\<noteq>b \<and> T\<subseteq>E);
            i \<leftarrow> SPECT [\<not> per_compare uf a b  \<mapsto>  enat indep_test_time];
            if i then
              do { 
                ASSERT (Upair a b\<notin>T);
                addEdge uf a b T
              }
            else 
              RETURNT (uf,T)
        }) s;
        RETURNT spanning_forest
      }"

lemma corresponding_union_find_empty:
  shows "corresponding_union_find (per_init V) empty_forest"
  by(auto simp: corresponding_union_find_def connected_same per_init_def) 
   

lemma empty_forest_refine1: "((per_init V, empty_forest), empty_forest)\<in>uf_graph_rel"
  using corresponding_union_find_empty
  unfolding  uf_graph_rel_def uf_graph_invar_def 
  by (auto simp: in_br_conv per_init_def)

lemma uf_graph_invar_preserve: "uf_graph_invar (uf, T) \<Longrightarrow> a\<in>V \<Longrightarrow> b\<in>V \<Longrightarrow> a\<noteq>b \<Longrightarrow> T\<subseteq>E
         \<Longrightarrow> uf_graph_invar (per_union uf a b, insert (Upair a b) T)"
  by(auto simp add: uf_graph_invar_def corresponding_union_find_def insert_reachable per_union_def)    

lemma initloop: "initState \<le> \<Down> uf_graph_rel (SPECT [{} \<mapsto> enat (empty_forest_time+empty_uf_time)])"
  unfolding initState_def conc_fun_RES
    apply(rule T_specifies_I)         
  apply (vcg' \<open>-\<close>  )   
  apply(rule Sup_upper)  apply (auto split: if_splits)
  using empty_forest_refine1 by auto


lemma ref: "\<And> xi x si sb x1 x2 x1a x2a x1b x2b.      
       (xi, x) \<in> Id \<times>\<^sub>r Id \<Longrightarrow>
       (si, sb) \<in> uf_graph_rel \<Longrightarrow>
       x = (x1, x2) \<Longrightarrow>
       si = (x1b, x2b) \<Longrightarrow>
       xi = (x1a, x2a) \<Longrightarrow>
       x1a \<in> V \<and> x2a \<in> V \<and> x1a \<in> Domain x1b \<and> x2a \<in> Domain x1b \<and> x1a \<noteq> x2a \<and> x2b \<subseteq> E \<Longrightarrow>  
        addEdge x1b x1a x2a x2b 
       \<le> \<Down> uf_graph_rel (SPECT [insert (Upair x1 x2) sb \<mapsto> enat (insert_time+insert_uf_time)]) " 
  unfolding addEdge_def  conc_fun_RES 
    apply(rule T_specifies_I)               
  apply (vcg' \<open>-\<close>  )   
  by (auto dest: uf_graph_relD E_inV Eproper uf_graph_invarE
          simp:  corresponding_union_find_def uf_graph_rel_def in_br_conv uf_graph_invar_preserve
           split: if_splits)  



theorem kruskal1_refine: "kruskal1 \<le> \<Down>Id kruskal0"
  unfolding kruskal1_def kruskal0_def Let_def 
  apply (refine_rcg initloop ref)
           apply refine_dref_type  
  apply simp apply simp apply auto []
  apply (auto dest: uf_graph_relD E_inV Eproper uf_graph_invarE
          simp:  corresponding_union_find_def uf_graph_rel_def in_br_conv uf_graph_invar_preserve)
  by (auto simp: uf_graph_invar_def dest: E_inV) 
    

section "kruskal2 - using lists"


abbreviation "lst_graph_P l S \<equiv> lst_graph_P' weight l S"
lemmas lst_graph_P_def = lst_graph_P'_def


lemma lst_graph_P_distinctD: "lst_graph_P l S \<Longrightarrow> distinct l"
  by(auto simp: lst_graph_P_def dest: distinct_mapI)

abbreviation "lst_graph_rel \<equiv> lst_graph_rel' weight"
lemmas lst_graph_rel_def = lst_graph_rel'_def


lemma lst_graph_rel_empty[simp]: "([], {}) \<in> lst_graph_rel"
  by(simp add: lst_graph_rel_def lst_graph_P_def)

term set_rel
term list_set_rel
abbreviation "edge_rel \<equiv> br \<alpha>' (\<lambda>(a,w,b). weight (Upair a b) = w)"
abbreviation "edge_rel' \<equiv> br \<alpha>'' (\<lambda>(a,w,b). weight (Upair a b) = w)"

lemma lst_graph_rel_alt: 
  "lst_graph_rel = \<langle>edge_rel\<rangle>list_set_rel" (is "?L = ?R")
proof  
  show "?L \<subseteq> ?R"
    unfolding lst_graph_rel_def list_set_rel_def lst_graph_P_def   
    apply rule apply safe subgoal for a b apply(intro relcompI[where b="map \<alpha>' a"])
      by(auto simp add: list_rel_def  in_br_conv list_all2_map2  list_all2_same)
    done
next  
  have D: "\<And>x y. (x, y) \<in> \<langle>br \<alpha>' (\<lambda>(a, w, b). weight (Upair a b) = w)\<rangle>list_rel
      \<Longrightarrow> y = map \<alpha>' x \<and> (\<forall>(a, w, b)\<in>set x. weight (Upair a b) = w)"
    unfolding list_rel_def apply safe
    subgoal for x y 
      by(auto intro: nth_equalityI[where xs=y and ys="map (\<lambda>(a, uu, y). Upair a y) x"]
              simp: list_rel_def list_all2_conv_all_nth in_br_conv)  
    subgoal for x y by(auto simp: list_all2_conv_all_nth in_br_conv in_set_conv_nth)
    done

  show "?R \<subseteq> ?L"
    unfolding lst_graph_rel_def list_set_rel_def lst_graph_P_def   
    by (force dest!: D simp: in_br_conv) 
qed
    
                                      

abbreviation  (in -) getEdges'
  :: "('a uprod \<Rightarrow> 'w::{linorder, ordered_comm_monoid_add}) \<Rightarrow> 'a uprod set \<Rightarrow> enat \<Rightarrow> ('a \<times> 'w \<times> 'a) list nrest"
    where
    "getEdges' w c get == SPECT (emb (\<lambda>L. lst_graph_P' w L c) get)" 
abbreviation     "getEdges == getEdges' weight E getEdges_time"  
 

abbreviation (in -) obtain_sorted_carrier''_aux
  :: "('a uprod \<Rightarrow> 'w::{linorder, ordered_comm_monoid_add}) \<Rightarrow> 'a uprod set \<Rightarrow> enat \<Rightarrow> enat \<Rightarrow> ('a \<times> 'w \<times> 'a) list nrest"  where
  "obtain_sorted_carrier''_aux w c get st \<equiv> do {
    (l::('a \<times> 'w \<times> 'a) list) \<leftarrow> getEdges' w c get;
  ( ((ASSERT (length l = card c))) \<then>
    SPECT (emb (\<lambda>L. sorted_wrt edges_less_eq L \<and> distinct L \<and> set L = set l) st))
}"               

abbreviation "obtain_sorted_carrier'' \<equiv> obtain_sorted_carrier''_aux weight E getEdges_time sort_time "

term "\<langle>edge_rel\<rangle>list_rel"

lemma "distinct x \<Longrightarrow> length x = length y \<Longrightarrow> set x = set y \<Longrightarrow> distinct y"   
  using card_distinct distinct_card by fastforce  


lemma wsorted'_sorted_wrt_edges_less_eq: "\<forall>x\<in>set s. case x of (a, wv, b) \<Rightarrow> weight (Upair a b) = wv \<Longrightarrow> sorted_wrt edges_less_eq s
  \<Longrightarrow> wsorted' (map \<alpha>'' s) "
  unfolding wsorted_wrt_w'_def sorted_wrt_map edges_less_eq_def
  apply(rule sorted_wrt_mono_rel ) 
  by (auto simp add: \<alpha>_def case_prod_beta) 

lemma " distinct s \<Longrightarrow>
    set s = set l \<Longrightarrow>
    distinct (map f l) \<Longrightarrow>  distinct (map f s)"
  by (simp add: distinct_map)

lemma \<alpha>'_conv: "(((\<lambda>(x, y). Upair x y) \<circ>\<circ> case_prod) (\<lambda>a (_, y). (a, y)))
      = \<alpha>'"   by auto 

lemma "SPECT (emb P1 t1) \<bind> (\<lambda>l. SPECT (emb (P2 l) t2))
  = SPECT (emb P (t1+t2)) " unfolding bindT_def
  apply auto unfolding emb'_def apply auto
  oops


lemma emb_eq_Some_conv': "\<And>T.  Some t' = emb' Q T x \<longleftrightarrow> (t'=T x \<and> Q x)"
  by (auto simp: emb'_def)

lemma obtain_sorted_carrier''_refine: "obtain_sorted_carrier'' \<le> \<Down> (\<langle>edge_rel'\<rangle>list_rel) obtain_sorted_carrier'"
  unfolding   obtain_sorted_carrier'_aux_def
  unfolding conc_fun_RES 
    apply(rule T_specifies_I)               
  apply(vcg' \<open>-\<close>  )  
  apply(rule Sup_upper)  apply (auto split: if_splits)  
  subgoal for l s
    apply(rule exI[where x="map \<alpha>'' s"])
    apply (simp add: emb_eq_Some_conv')
    apply(auto simp: in_br_conv lst_graph_P_def wsorted'_sorted_wrt_edges_less_eq
            \<alpha>_def \<alpha>'_conv distinct_map map_in_list_rel_conv) 
     using image_iff  
     by fastforce+  
   subgoal unfolding lst_graph_P_def  
     using distinct_card by fastforce  
  done 


definition (in -) "initState'_aux c eft eut = do {
  initial_union_find \<leftarrow> SPECT [per_init (Kruskal_intermediate_defs.V c) \<mapsto> enat eut];
       SPECT [(initial_union_find, []) \<mapsto> enat eft]
  }"

abbreviation "initState' == initState'_aux E empty_forest_time empty_uf_time"

definition (in -) "addEdge'_aux uf a w b T iut it = do {
  uf \<leftarrow> SPECT [per_union uf a b \<mapsto> enat iut];
  T' \<leftarrow> SPECT [  T@[ ( a,w, b) ] \<mapsto>enat it];
  RETURNT (uf, T')
  }"

abbreviation "addEdge' uf a w b T == addEdge'_aux uf a w b T insert_uf_time insert_time"


 definition (in -) kruskal2_aux
   where "kruskal2_aux w c  get st eft eut itt iut it \<equiv> do {
    sl \<leftarrow> obtain_sorted_carrier''_aux w c  get st; 
    s \<leftarrow> initState'_aux c eft eut;
    (per, spanning_forest) \<leftarrow> nfoldli sl (\<lambda>_. True)
        (\<lambda>(a,w,b) (uf, T). do { 
            ASSERT (a \<in> Domain uf \<and> b \<in> Domain uf);
            i \<leftarrow> SPECT [\<not> per_compare uf a b  \<mapsto> itt];
            if i then
              do {  
                ASSERT ((a,w,b)\<notin>set T);
                addEdge'_aux uf a w b T iut it
              }
            else 
              RETURNT (uf,T)
        }) s;
        RETURNT spanning_forest
      }"

abbreviation "kruskal2 == kruskal2_aux weight E getEdges_time sort_time
                             empty_forest_time empty_uf_time indep_test_time insert_uf_time insert_time "

lemma loop_initial_rel: "((per_init V, []), per_init V, {}) \<in> Id \<times>\<^sub>r lst_graph_rel"
  by simp

lemma loop_initial_refine: "initState'
   \<le> \<Down> (Id \<times>\<^sub>r lst_graph_rel) initState"
  unfolding initState'_aux_def initState_def
  apply(refine_rcg SPECT_refine) 
  by (auto split: if_splits)


lemma wI: "(\<lambda>(a, _, y). Upair a y) ` D = A \<Longrightarrow> Upair b c \<notin> A \<Longrightarrow> (b, w, c) \<notin> D"
  by (metis case_prod_conv pair_imageI)


lemma listall2D: " list_all2 P xs y \<Longrightarrow> (\<And>x x'. P x x' \<longrightarrow> x' = a x)   \<Longrightarrow> y = map a xs" 
  by (smt list.rel_eq list.rel_map(1) list_all2_mono)  

lemma list_relD: "(x, y) \<in> \<langle>br a I\<rangle>list_rel \<Longrightarrow> y = map a x" 
  by(auto dest!: listall2D simp: list_rel_def in_br_conv)

lemma list_set_rel_append: "(x,s)\<in>br a I \<Longrightarrow> (xs,S)\<in>\<langle>br a I\<rangle>list_set_rel \<Longrightarrow> s\<notin>S
     \<Longrightarrow> (xs@[x],insert s S)\<in>\<langle>br a I\<rangle>list_set_rel"
  unfolding list_set_rel_def
  apply(intro relcompI[where b="map a (xs @ [x])"])
   apply (auto simp: in_br_conv)  
  apply parametricity by (auto dest: list_relD simp add: in_br_conv)


theorem kruskal2_refine: "kruskal2 \<le> \<Down>lst_graph_rel kruskal1 "
  unfolding kruskal1_def kruskal2_aux_def Let_def 
  apply (refine_rcg obtain_sorted_carrier''_refine  loop_initial_refine)     
           apply simp apply simp
  subgoal by (auto simp: in_br_conv)  
  subgoal by (auto simp: in_br_conv)
       apply(rule ffs) subgoal by (auto simp: in_br_conv)
  subgoal by (auto simp: in_br_conv ) 
  subgoal   unfolding in_br_conv lst_graph_rel_def lst_graph_P_def list_set_rel_def
    by (simp add: wI)     
  subgoal unfolding addEdge'_aux_def addEdge_def
    apply refine_rcg
     apply refine_dref_type
     apply(rule SPECT_refine)
     apply (auto split: if_splits simp: in_br_conv lst_graph_rel_alt  intro: list_set_rel_append)
    unfolding conc_fun_RES
    apply(rule T_specifies_I)         
    apply (vcg' \<open>-\<close>  )   
    apply(rule Sup_upper)  apply (auto split: if_splits) 
    by (auto split: if_splits simp: in_br_conv lst_graph_rel_alt intro: list_set_rel_append) 
  subgoal by (auto simp: in_br_conv )
  subgoal by (auto simp: in_br_conv )
  done

lemma  "single_valued lst_graph_rel"
  unfolding lst_graph_rel_alt list_set_rel_def
  by(auto intro!: single_valued_relcomp list_rel_sv)  
 
end \<comment> \<open>whatIneed\<close>



end