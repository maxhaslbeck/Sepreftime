section \<open>Implementation of the Edmonds-Karp Algorithm\<close>
theory EdmondsKarp_Refine
imports 
  EdmondsKarp_Algo
  Augmenting_Path_BFS
begin



    lemma ccId: "\<And>c. (c, c) \<in> Id" by simp
 
context
  fixes t ::  "nat"
begin
  definition "mop_min a b =SPECT [min a b \<mapsto> t]"

  lemma mop_min: "\<And>tt. tt \<le> TTT Q (SPECT [ min a b \<mapsto> t]) \<Longrightarrow> tt
           \<le> TTT Q (mop_min a b)" unfolding mop_min_def by simp 
 
  sepref_register "mop_min" 
  print_theorems 
end 

context
  fixes t ::  "nat"
begin
  definition "matrix_get m e = SPECT [m e \<mapsto> t]"

  lemma matrix_get: "\<And>tt. tt \<le> TTT Q (SPECT [ m e \<mapsto> t]) \<Longrightarrow> tt
           \<le> TTT Q (matrix_get m e)" unfolding matrix_get_def by simp 
 
  sepref_register "matrix_get" 
  print_theorems 
end 

context
  fixes t ::  "nat"
begin
  definition "matrix_set (m::'a*'a\<Rightarrow>'b) e v = SPECT [m(e:=v) \<mapsto> t]"

  lemma matrix_set: "\<And>tt. tt \<le> TTT Q (SPECT [ m(e:=v) \<mapsto> t]) \<Longrightarrow> tt
           \<le> TTT Q (matrix_set m e v)" unfolding matrix_set_def by simp 
 
  sepref_register "matrix_set" 
  print_theorems 
end 
    
    



  text \<open>We now implement the Edmonds-Karp algorithm.
    Note that, during the implementation, we explicitly write down the 
    whole refined algorithm several times. As refinement is modular, most 
    of these copies could be avoided--- we inserted them deliberately for
    documentation purposes.
    \<close>

  subsection \<open>Refinement to Residual Graph\<close>
    text \<open>As a first step towards implementation, we refine the algorithm
      to work directly on residual graphs. For this, we first have to 
      establish a relation between flows in a network and residual graphs.
      \<close>
    
  subsubsection \<open>Refinement of Operations\<close>
  context Network 
  begin
    text \<open>We define the relation between residual graphs and flows\<close>
    definition "cfi_rel \<equiv> br flow_of_cf (RGraph c s t)"

    text \<open>It can also be characterized the other way round, i.e., 
      mapping flows to residual graphs:\<close>
    lemma cfi_rel_alt: "cfi_rel = {(cf,f). cf = residualGraph c f \<and> NFlow c s t f}"
      unfolding cfi_rel_def br_def
      by (auto 
          simp: NFlow.is_RGraph RGraph.is_NFlow 
          simp: RPreGraph.rg_fo_inv[OF RGraph.this_loc_rpg]
          simp: NPreflow.fo_rg_inv[OF NFlow.axioms(1)])

    
    text \<open>Initially, the residual graph for the zero flow equals the original network\<close>
    lemma residualGraph_zero_flow: "residualGraph c (\<lambda>_. 0) = c" 
      unfolding residualGraph_def by (auto intro!: ext)
    lemma flow_of_c: "flow_of_cf c = (\<lambda>_. 0)"
      by (auto simp add: flow_of_cf_def[abs_def])

    text \<open>The residual capacity is naturally defined on residual graphs\<close>
    definition "resCap_cf cf p \<equiv> Min {cf e | e. e\<in>set p}"
    lemma (in NFlow) resCap_cf_refine: "resCap_cf cf p = resCap p"
      unfolding resCap_cf_def resCap_def ..

    text \<open>Augmentation can be done by @{const Graph.augment_cf}.\<close> 

    
    lemma (in NFlow) augment_cf_refine_aux: (* For snippet *)
      assumes AUG: "isAugmentingPath p"
      shows "residualGraph c (augment (augmentingFlow p)) (u,v) = (
        if (u,v)\<in>set p then (residualGraph c f (u,v) - resCap p)
        else if (v,u)\<in>set p then (residualGraph c f (u,v) + resCap p)
        else residualGraph c f (u,v))"
      using augment_alt[OF AUG] by (auto simp: Graph.augment_cf_def)

    lemma augment_cf_refine:
      assumes R: "(cf,f)\<in>cfi_rel"
      assumes AUG: "NPreflow.isAugmentingPath c s t f p"
      shows "(Graph.augment_cf cf (set p) (resCap_cf cf p), 
          NFlow.augment_with_path c f p) \<in> cfi_rel"
    proof -    
      from R have [simp]: "cf = residualGraph c f" and "NFlow c s t f"
        by (auto simp: cfi_rel_alt br_def)
      then interpret f: NFlow c s t f by simp
      
      show ?thesis 
        unfolding f.augment_with_path_def
      proof (simp add: cfi_rel_alt; safe intro!: ext)
        fix u v
        show "Graph.augment_cf f.cf (set p) (resCap_cf f.cf p) (u,v) 
              = residualGraph c (f.augment (f.augmentingFlow p)) (u,v)"
          unfolding f.augment_cf_refine_aux[OF AUG]
          unfolding f.cf.augment_cf_def
          by (auto simp: f.resCap_cf_refine)
      qed (rule f.augment_pres_nflow[OF AUG])
    qed  

    text \<open>We rephrase the specification of shortest augmenting path to
      take a residual graph as parameter\<close>
    (* TODO: This actually rephrases the spec to make it look more similar to 
      what BFS does later. This rephrasing does not belong here, but where we 
      implement it with BFS. *)
end 
locale EdKa_Res = Network c s t for c :: "'capacity::linordered_idom graph" and s t +
  fixes shortestpath_time :: nat
    and augment_with_path_time :: nat 
  assumes augment_progress[simp]: "0 \<noteq> enat shortestpath_time"
begin

    interpretation Ed: EdKa c s t shortestpath_time augment_with_path_time
      apply standard by simp


    definition "find_shortest_augmenting_spec_cf cf \<equiv> 
      ASSERT (RGraph c s t cf) \<then>
      SPECT (emb (\<lambda>
        None \<Rightarrow> \<not>Graph.connected cf s t 
      | Some p \<Rightarrow> Graph.isShortestPath cf s p t) shortestpath_time)"
 

    thm RPreGraph.f_def term "RGraph"
    lemma   find_shortest_augmenting_spec_cf_refine: 
       "RGraph c s t cf \<Longrightarrow> find_shortest_augmenting_spec_cf cf \<le> Ed.find_shortest_augmenting_spec (flow_of_cf cf)" 
    proof -
      assume R: "RGraph c s t cf"
      interpret RG: RGraph c s t cf by fact

      show ?thesis
      unfolding RPreGraph.f_def[symmetric]
      unfolding find_shortest_augmenting_spec_cf_def  apply(subst Ed.find_shortest_augmenting_spec_def)
      apply(rule le_ASSERTI) apply(rule ASSERT_leI) using R apply simp     
      using Network_axioms apply(simp add: EdKa_def EdKa_axioms_def) 
      by (auto 
        simp: pw_le_iff refine_pw_simps Some_eq_emb'_conv numeral_eq_enat
        simp: RGraph.this_loc RPreGraph.rg_is_cf
        simp: RG.f.isAugmentingPath_def Graph.connected_def Graph.isSimplePath_def 
        dest: RG.cf.shortestPath_is_path
        split: option.split)   
  qed

    text \<open>This leads to the following refined algorithm\<close>  
    definition  "edka2 \<equiv> do {
      cf \<leftarrow> RETURNT c;

      (cf,_) \<leftarrow> whileT 
        (\<lambda>(cf,brk). \<not>brk) 
        (\<lambda>(cf,_). do {
          ASSERT (RGraph c s t cf);
          p \<leftarrow> find_shortest_augmenting_spec_cf cf;
          case p of 
            None \<Rightarrow> RETURNT (cf,True)
          | Some p \<Rightarrow> do {
              ASSERT (p\<noteq>[]);
              ASSERT (Graph.isShortestPath cf s p t);
              cf \<leftarrow> SPECT [Graph.augment_cf cf (set p) (resCap_cf cf p) \<mapsto> augment_with_path_time];
              ASSERT (RGraph c s t cf);
              RETURNT (cf, False)
            }  
        })
        (cf,False);
      ASSERT (RGraph c s t cf);
      f \<leftarrow> RETURNT (flow_of_cf cf);  
      RETURNT f
    }"


  (*  interpretation edk: EdKa c s t find_shortest_augmenting_spec_cf_time augment_with_path_time
      apply standard by simp
    thm RGraph.find_shortest_augmenting_spec_cf_refine
*)


 


    lemma  edka2_refine: "edka2 \<le> \<Down>Id Ed.edka"
    proof -
      (* have [refine_dref_RELATES]: "RELATES cfi_rel" by (simp add: RELATES_def) *)

      show ?thesis
        unfolding edka2_def Ed.edka_def 
        apply (rule bindT_refine[where R'=cfi_rel] ) 
        subgoal unfolding cfi_rel_alt 
          apply(rule RETURNT_refine) by (auto simp add: residualGraph_zero_flow zero_flow)  
          apply(rule bindT_refine[where R'="cfi_rel \<times>\<^sub>r bool_rel"])
         apply(rule WHILET_refine)     apply simp
        subgoal by auto
         apply auto  apply(rule ASSERT_leI)
        subgoal unfolding cfi_rel_alt by (auto simp add: NFlow.is_RGraph)  
         apply (rule bindT_refine[where R'=Id]) apply simp  
        subgoal    
          apply (frule find_shortest_augmenting_spec_cf_refine)  
          apply (simp add: cfi_rel_def in_br_conv) done
        subgoal apply (auto intro: RETURNT_refine split: option.splits) 
          apply(rule le_R_ASSERTI)+
          apply(rule ASSERT_leI) apply simp
          apply(rule ASSERT_leI) apply (simp add: cfi_rel_alt)
          apply(rule bindT_refine[where R'=cfi_rel]) apply simp
          apply(rule SPECT_refine) apply (auto split: if_splits)[] 
          subgoal apply (auto simp add: cfi_rel_def in_br_conv)
            subgoal by (metis augment_cf_refine cfi_rel_def in_br_conv)
            subgoal by (metis augment_cf_refine cfi_rel_def in_br_conv) 
            done
          apply(rule ASSERT_leI) subgoal  
            by (metis (full_types)  cfi_rel_def in_br_conv) 
          apply(rule le_R_ASSERTI)
          apply(rule RETURNT_refine)
          by (auto simp: augment_cf_refine) 
        subgoal 
          apply(rule le_ASSERTI)
          apply(rule ASSERT_leI)    
          by(simp_all add: cfi_rel_def in_br_conv)
        done  
    qed    

lemma  edka2_correct: "edka2 \<le> \<Down>Id  (SPECT (emb isMaxFlow (enat Ed.edka_time)))"
    apply(rule order.trans) apply(rule edka2_refine) using Ed.edka_correct by simp
 
end

locale RGraph_impl = RGraph c s t cf for c :: "'capacity::linordered_idom graph" and s t cf +
  fixes matrix_lookup_time matrix_set_time :: nat
begin
 

    subsection \<open>Implementation of Bottleneck Computation and Augmentation\<close>  
    text \<open>We will access the capacities in the residual graph
      only by a get-operation, which asserts that the edges are valid\<close>
    
    abbreviation (in Graph) (input) valid_edge :: "edge \<Rightarrow> bool" where
      "valid_edge \<equiv> \<lambda>(u,v). u\<in>V \<and> v\<in>V"
 

    definition cf_get 
      :: "'capacity graph \<Rightarrow> edge \<Rightarrow> 'capacity nrest" 
      where "cf_get cff e \<equiv> ASSERT (valid_edge e) \<then> matrix_get matrix_lookup_time cff e"  
    definition cf_set 
      :: "'capacity graph \<Rightarrow> edge \<Rightarrow> 'capacity \<Rightarrow> 'capacity graph nrest"
      where "cf_set cff e cap \<equiv> ASSERT (valid_edge e) \<then> matrix_set matrix_set_time cff e cap"  


    definition resCap_cf_impl :: "path \<Rightarrow> 'capacity nrest" 
    where "resCap_cf_impl p \<equiv> 
      case p of
        [] \<Rightarrow> SPECT [(0::'capacity) \<mapsto> 1]
      | (e#p) \<Rightarrow> do {
          cap \<leftarrow> cf_get cf e;
          ASSERT (distinct p);
          nfoldli 
            p (\<lambda>_. True)
            (\<lambda>e cap. do {
              cape \<leftarrow> cf_get cf e;
              mop_min 10 cape cap
            }) 
            cap
        }"

    definition "resCap_cf_impl_time n = 1 + (matrix_lookup_time+10) * n"
    lemma resCap_cf_impl_time_mono: "n \<le> m \<Longrightarrow> resCap_cf_impl_time n \<le> resCap_cf_impl_time m"
      unfolding resCap_cf_impl_time_def by simp

    lemma  resCap_cf_impl_refine:   
      assumes AUG: "cf.isSimplePath s p t"
      shows "resCap_cf_impl p \<le> SPECT (emb (\<lambda>r. r = resCap_cf cf p) (resCap_cf_impl_time (length p)))"
    proof -
      (* TODO: Can we exploit Min.set_eq_fold *)

      note [simp del] = Min_insert
      note [simp] = Min_insert[symmetric]
      from AUG[THEN cf.isSPath_distinct]
      have "distinct p" .
      moreover from AUG cf.isPath_edgeset have "set p \<subseteq> cf.E"
        by (auto simp: cf.isSimplePath_def)
      hence "set p \<subseteq> Collect valid_edge"  
        using cf.E_ss_VxV by simp
      moreover from AUG have "p\<noteq>[]" by (auto simp: s_not_t) 
        then obtain e p' where "p=e#p'" by (auto simp: neq_Nil_conv)
      ultimately show ?thesis  
        unfolding resCap_cf_impl_def resCap_cf_def cf_get_def
        apply (simp only: list.case)
        apply(rule T_specifies_I)
        apply(vcg'\<open>-\<close> rules: matrix_get )  
          apply(rule nfoldli_rule[where I="\<lambda>l l' cap. 
              cap = Min (cf`insert e (set l)) 
            \<and> set (l@l') \<subseteq> Collect valid_edge" and body_time="matrix_lookup_time+10"
              and P="(\<lambda>r. r = Min {cf ea |ea. ea \<in> set (e # p')})", THEN T_specifies_rev , THEN T_conseq4]) 
          
            apply (auto intro!: arg_cong[where f=Min])  []
        subgoal apply(rule T_specifies_I) apply(vcg'\<open>-\<close> rules: mop_min matrix_get)  
          by (auto simp add: emb_le_Some_conv numeral_eq_enat intro!: arg_cong[where f=Min])  
        by (auto simp: emb_eq_Some_conv Some_le_emb'_conv resCap_cf_impl_time_def intro!: arg_cong[where f=Min])
 
        
 (*
        apply (refine_vcg nfoldli_rule[where 
            I = "\<lambda>l l' cap. 
              cap = Min (cf`insert e (set l)) 
            \<and> set (l@l') \<subseteq> Collect valid_edge"])
        apply (auto intro!: arg_cong[where f=Min])
        done *)  
    qed    

    definition (in Graph) 
      "augment_edge e cap \<equiv> (c(
                  e := c e - cap, 
        prod.swap e := c (prod.swap e) + cap))"

    (* TODO: This would be much simpler to prove if we had a characterization 
      of simple-path only depending on p. *)    
    lemma (in Graph) augment_cf_inductive:
      fixes e cap s t
      defines "c' \<equiv> augment_edge e cap"
      assumes P: "isSimplePath s (e#p) t"
      shows "augment_cf (insert e (set p)) cap = Graph.augment_cf c' (set p) cap"
      and "\<exists>s'. Graph.isSimplePath c' s' p t"  
    proof -
      obtain u v where [simp]: "e=(u,v)" by (cases e)

      from isSPath_no_selfloop[OF P] have [simp]: "\<And>u. (u,u)\<notin>set p" "u\<noteq>v" by auto

      from isSPath_nt_parallel[OF P] have [simp]: "(v,u)\<notin>set p" by auto
      from isSPath_distinct[OF P] have [simp]: "(u,v)\<notin>set p" by auto

      show "augment_cf (insert e (set p)) cap = Graph.augment_cf c' (set p) cap"
        apply (rule ext)  
        unfolding Graph.augment_cf_def c'_def Graph.augment_edge_def
        by auto

      have "Graph.isSimplePath c' v p t"  
        unfolding Graph.isSimplePath_def
        apply rule
        apply (rule transfer_path)
        unfolding Graph.E_def
        apply (auto simp: c'_def Graph.augment_edge_def) []
        using P apply (auto simp: isSimplePath_def) []
        using P apply (auto simp: isSimplePath_def) []
        done
      thus "\<exists>s'. Graph.isSimplePath c' s' p t" .. 

    qed    
        
    definition "augment_edge_impl cff e cap \<equiv> do {
      v \<leftarrow> cf_get cff e; cf \<leftarrow> cf_set cff e (v-cap);
      e \<leftarrow> SPECT [prod.swap e\<mapsto>3];
      v \<leftarrow> cf_get cf e; cf \<leftarrow> cf_set cf e (v+cap);
      RETURNT cf
    }"

    definition "augment_edge_impl_time = 2* matrix_lookup_time + 2*matrix_set_time+3"

    lemma augment_edge_impl_refine: 
      assumes "valid_edge e" "\<forall>u. e\<noteq>(u,u)"
      shows "augment_edge_impl cff e cap 
              \<le> SPECT (emb  (\<lambda>r. r = Graph.augment_edge cff e cap) augment_edge_impl_time)"
      using assms
      unfolding augment_edge_impl_def Graph.augment_edge_def 
      unfolding cf_get_def cf_set_def apply simp
      apply(rule T_specifies_I)
      apply (vcg'\<open>auto\<close> rules: matrix_get matrix_set) apply (auto simp: emb_le_Some_conv augment_edge_impl_time_def one_enat_def  numeral_eq_enat)
      done

      
    definition augment_cf_impl 
      :: "'capacity graph \<Rightarrow> path \<Rightarrow> 'capacity \<Rightarrow> 'capacity graph nrest" 
      where
      "augment_cf_impl cff p x \<equiv> do {
        RECT (\<lambda>D. \<lambda>
          ([],cf) \<Rightarrow> SPECT [ cf \<mapsto> 1]
        | (e#p,cf) \<Rightarrow> do {
            cf \<leftarrow> augment_edge_impl cf e x;
            D (p,cf)
          }  
        ) (p,cff)
      }"

    text \<open>Deriving the corresponding recursion equations\<close>  
    lemma augment_cf_impl_simps[simp]: 
      "augment_cf_impl cff [] x = SPECT [ cff \<mapsto> 1]"
      "augment_cf_impl cff (e#p) x = do { 
        cf \<leftarrow> augment_edge_impl cff e x; 
        augment_cf_impl cf p x}"
      apply (simp add: augment_cf_impl_def)
      apply (subst RECT_unfold, refine_mono)
      apply simp
      
      apply (simp add: augment_cf_impl_def)
      apply (subst RECT_unfold, refine_mono)
      apply simp
      done      

    definition "augment_cf_impl_time n =    1 + n * augment_edge_impl_time "
    lemma augment_cf_impl_time_mono: "n \<le> m \<Longrightarrow> augment_cf_impl_time n \<le> augment_cf_impl_time m"
      unfolding augment_cf_impl_time_def by simp


    term "cf.isSimplePath"

    lemma augment_cf_impl_aux:  
      assumes "\<forall>e\<in>set p. valid_edge e"
      assumes "\<exists>s. Graph.isSimplePath cf s p t"
      shows "augment_cf_impl cf p x \<le> SPECT [Graph.augment_cf cf (set p) x\<mapsto> augment_cf_impl_time (length p)]"
      using assms unfolding augment_cf_impl_time_def
    proof (induction p arbitrary: cf)
      case Nil
      then show ?case 
        by (simp add: le_fun_def one_enat_def Graph.augment_cf_empty)

    next
      case (Cons a p)

      from Cons(2,3)
      show ?case  
      apply clarsimp        
      apply (subst Graph.augment_cf_inductive, assumption) 
      apply(rule T_specifies_I)
        apply (vcg'\<open>-\<close> rules:  )   
        apply(rule  augment_edge_impl_refine[THEN T_specifies_rev , THEN T_conseq4])
          apply (auto dest: Graph.isSPath_no_selfloop)
        apply(rule Cons(1)[THEN T_specifies_rev , THEN T_conseq4])
          apply simp apply (auto simp add: emb_eq_Some_conv) []
            apply (drule Graph.augment_cf_inductive(2)[where cap=x]; simp)
        by (auto simp add: emb_eq_Some_conv split: if_splits) 
      (*
      apply (refine_vcg augment_edge_impl_refine[THEN order_trans])
      apply simp
      apply simp
      apply (auto dest: Graph.isSPath_no_selfloop) []
      apply (rule order_trans, rprems)
        apply (drule Graph.augment_cf_inductive(2)[where cap=x]; simp)
        apply simp
      done  *)  
    qed
      
    lemma augment_cf_impl_refine:     
      assumes "Graph.isSimplePath cf s p t"
      shows "augment_cf_impl cf p x \<le> SPECT [Graph.augment_cf cf (set p) x\<mapsto> augment_cf_impl_time (length p)]"
      apply (rule augment_cf_impl_aux)
      using assms cf.E_ss_VxV apply (auto simp: cf.isSimplePath_def dest!: cf.isPath_edgeset) []
      using assms by blast
end

locale EdKa_Res_Up = Network c s t for c :: "'capacity::linordered_idom graph" and s t +
  fixes shortestpath_time :: nat
    and matrix_lookup_time matrix_set_time :: nat
  assumes augment_progress[simp]: "0 \<noteq> enat shortestpath_time"
begin


    definition "augment_with_path_time = RGraph_impl.resCap_cf_impl_time matrix_lookup_time (card V)
           + RGraph_impl.augment_cf_impl_time matrix_lookup_time matrix_set_time (card V)"

    thm  Finite_Graph.isShortestPath_length_less_V

lemma  tTT:
  fixes ss tt cc
  assumes  "Graph.isShortestPath cc ss p tt" "ss\<in>V" "RGraph c s t cc"
  shows "RGraph_impl.resCap_cf_impl_time matrix_lookup_time (length p)
              + RGraph_impl.augment_cf_impl_time matrix_lookup_time matrix_set_time (length p) \<le> augment_with_path_time "
proof -  
  interpret R: RGraph c s t cc by fact
  
  from R.cf.isShortestPath_length_less_V assms have "length p < card V" by simp
  then have le: "length p \<le> card V" by auto

  thm RGraph_impl.augment_cf_impl_time_mono
  term RGraph_impl.resCap_cf_impl_time
  have "RGraph_impl.resCap_cf_impl_time matrix_lookup_time (length p) \<le> RGraph_impl.resCap_cf_impl_time matrix_lookup_time (card V)"
    apply(rule RGraph_impl.resCap_cf_impl_time_mono)
    using assms(3) le RGraph_impl_def by auto
  moreover
  have "RGraph_impl.augment_cf_impl_time matrix_lookup_time matrix_set_time (length p) \<le> RGraph_impl.augment_cf_impl_time matrix_lookup_time matrix_set_time (card V)"
    apply(rule RGraph_impl.augment_cf_impl_time_mono)
    using assms(3) le RGraph_impl_def by auto
  ultimately
  show ?thesis unfolding augment_with_path_time_def by simp
qed
 
    interpretation Ed_Res: EdKa_Res c s t shortestpath_time augment_with_path_time
      apply standard by simp
  
lemmas find_shortest_augmenting_spec_cf = Ed_Res.find_shortest_augmenting_spec_cf_def
 
    abbreviation "resCap_cf_impl' cf p \<equiv> RGraph_impl.resCap_cf_impl c cf matrix_lookup_time p"
    abbreviation "augment_cf_impl' cf p bn \<equiv> RGraph_impl.augment_cf_impl c matrix_lookup_time matrix_set_time cf p bn"
    abbreviation "find_shortest_augmenting_spec_cf \<equiv> Ed_Res.find_shortest_augmenting_spec_cf"

    text \<open>Finally, we arrive at the algorithm where augmentation is 
      implemented algorithmically: \<close>  
    definition "edka3 \<equiv> do {
      cf \<leftarrow> RETURNT c;

      (cf,_) \<leftarrow> whileT 
        (\<lambda>(cf,brk). \<not>brk) 
        (\<lambda>(cf,_). do {
          ASSERT (RGraph c s t cf);
          p \<leftarrow> find_shortest_augmenting_spec_cf cf;
          case p of 
            None \<Rightarrow> RETURNT (cf,True)
          | Some p \<Rightarrow> do {
              ASSERT (p\<noteq>[]);
              ASSERT (Graph.isShortestPath cf s p t);
              bn \<leftarrow> resCap_cf_impl' cf p;
              cf \<leftarrow> augment_cf_impl' cf p bn;
              ASSERT (RGraph c s t cf);
              RETURNT (cf, False)
            }  
        })
        (cf,False);
      ASSERT (RGraph c s t cf);
      f \<leftarrow> RETURNT (flow_of_cf cf);  
      RETURNT f
    }"

 

lemma "s\<in>V" by auto

    lemma edka3_refine: "edka3 \<le> \<Down>Id Ed_Res.edka2"
      unfolding edka3_def Ed_Res.edka2_def
      apply(rule bindT_refine)
       apply(rule RETURNT_refine) 
       apply(rule ccId)
      apply(rule bindT_refine[where R'="Id \<times>\<^sub>r bool_rel"])
       apply(rule WHILET_refine)
         apply simp apply simp
      apply(auto) []
          apply(rule le_ASSERTI)+
       apply(rule ASSERT_leI) apply simp
      apply(auto) []
       apply(rule bindT_mono) apply simp
      apply(auto split: option.splits) []
          apply(rule le_ASSERTI)+
       apply(rule ASSERT_leI) apply simp
       apply(rule ASSERT_leI) apply simp
       apply safe 
      apply(subst nres_bind_assoc[symmetric]) 
       apply(rule bindT_mono)      
      subgoal 
        apply(rule T_specifies_I)   
        apply(vcg'\<open>-\<close> rules: RGraph_impl.resCap_cf_impl_refine[THEN T_specifies_rev , THEN T_conseq4] 
             RGraph_impl.augment_cf_impl_refine[THEN T_specifies_rev , THEN T_conseq4]  )
        unfolding RGraph_impl_def apply simp
           apply(auto intro: Graph.shortestPath_is_simple)[] 
        apply simp
         apply(auto intro: Graph.shortestPath_is_simple)[] 
        apply (auto split: if_splits simp: emb_eq_Some_conv)
        apply(subst tTT ) by auto
      apply simp apply simp done
       (*
      apply (rewrite in "let cf = Graph.augment_cf _ _ _ in _" Let_def)
      apply refine_rcg
      apply refine_dref_type
      apply (vc_solve)
      apply (drule Graph.shortestPath_is_simple)
      apply (frule (1) RGraph.resCap_cf_impl_refine)
      apply (frule (1) RGraph.augment_cf_impl_refine)
      apply (auto simp: pw_le_iff refine_pw_simps)
      done *) 
                                                                         
lemma  edka3_correct: "edka3 \<le> \<Down>Id (SPECT (emb isMaxFlow (enat (EdKa.edka_time c shortestpath_time augment_with_path_time))))"
  unfolding EdKa.edka_time_def
    apply(rule order.trans) apply(rule edka3_refine) 
    using Ed_Res.edka2_correct by simp 
end
 
term Augmenting_Path_BFS.bfs

locale EdKa_Res_Bfs = Network c s t for c :: "'capacity::linordered_idom graph" and s t +
  fixes  set_insert_time map_dom_member_time set_delete_time get_succs_list_time map_update_time set_pick_time :: nat
    and list_append_time map_lookup_time set_empty_time set_isempty_time init_state_time :: nat

    and matrix_lookup_time matrix_set_time :: nat 
  assumes [simp]: "map_lookup_time > 0"
  assumes [simp]: "set_pick_time > 0" 
begin

    interpretation pbi: Pre_BFS_Impl c set_pick_time
      apply standard by simp

    definition "shortest_path_time = Pre_BFS_Impl.pre_bfs_time set_insert_time map_dom_member_time set_delete_time get_succs_list_time map_update_time set_pick_time set_empty_time set_isempty_time init_state_time (card V)
                 + valid_PRED_impl.extract_rpath_time list_append_time map_lookup_time (card V)"
  

lemma [simp]:  "enat shortest_path_time \<noteq> 0"
  unfolding  shortest_path_time_def using Pre_BFS_Impl.pre_bfs_time_progress[unfolded Pre_BFS_Impl_def, of set_pick_time]
    apply(auto)
  by (metis add_is_0 enat_0_iff(1) not_gr_zero)
  

    interpretation edru: EdKa_Res_Up c s t  shortest_path_time matrix_lookup_time matrix_set_time
      apply standard  by auto

    abbreviation "resCap_cf_impl'' cf p \<equiv> edru.resCap_cf_impl' cf p"
    abbreviation "augment_cf_impl'' cf p bn \<equiv> edru.augment_cf_impl' cf p bn"

    definition "MYbfs cf ss tt = Augmenting_Path_BFS.bfs cf set_insert_time map_dom_member_time set_delete_time get_succs_list_time map_update_time set_pick_time  
          list_append_time map_lookup_time set_empty_time set_isempty_time init_state_time ss tt"

    subsection \<open>Refinement to use BFS\<close>

    text \<open>We refine the Edmonds-Karp algorithm to use breadth first search (BFS)\<close>
    definition "edka4 \<equiv> do {
      cf \<leftarrow> RETURNT c;

      (cf,_) \<leftarrow> whileT 
        (\<lambda>(cf,brk). \<not>brk) 
        (\<lambda>(cf,_). do {
          ASSERT (RGraph c s t cf);
          p \<leftarrow> MYbfs cf s t;
          case p of 
            None \<Rightarrow> RETURNT (cf,True)
          | Some p \<Rightarrow> do {
              ASSERT (p\<noteq>[]);
              ASSERT (Graph.isShortestPath cf s p t);
              bn \<leftarrow> edru.resCap_cf_impl' cf p;
              cf \<leftarrow> edru.augment_cf_impl' cf p bn;
              ASSERT (RGraph c s t cf);
              RETURNT (cf, False)
            }  
        })
        (cf,False);
      ASSERT (RGraph c s t cf);
      f \<leftarrow> RETURNT (flow_of_cf cf);  
      RETURNT f
    }"

    text \<open>A shortest path can be obtained by BFS\<close>  
    lemma bfs_refines_shortest_augmenting_spec: fixes cf shows
      "MYbfs cf s t \<le> edru.find_shortest_augmenting_spec_cf cf "
      unfolding edru.find_shortest_augmenting_spec_cf
    proof (rule le_ASSERTI, goal_cases)
      case 1
      interpret BFS: Augmenting_Path_BFS cf set_insert_time map_dom_member_time set_delete_time get_succs_list_time map_update_time set_pick_time  
          list_append_time map_lookup_time set_empty_time set_isempty_time init_state_time
        apply standard by auto
      thm BFS.bfs_correct
      show ?case
      apply (rule order_trans) unfolding MYbfs_def
         apply (rule BFS.bfs_correct)          
      apply (simp add: RPreGraph.resV_netV[OF RGraph.this_loc_rpg, OF 1]  s_node)
      apply (simp add: RPreGraph.resV_netV[OF RGraph.this_loc_rpg, OF 1]) 
      apply(auto intro: embtimeI simp add:  RPreGraph.resV_netV[OF RGraph.this_loc_rpg, OF 1] BFS.bfs_time_def shortest_path_time_def  ) 
        done
    qed

    lemma edka4_refine: "edka4 \<le> \<Down>Id edru.edka3"
      unfolding edka4_def edru.edka3_def        
      apply(rule bindT_refine)
       apply(rule RETURNT_refine) 
       apply(rule ccId)
      apply(rule bindT_refine[where R'="Id \<times>\<^sub>r bool_rel"])
       apply(rule WHILET_refine)
         apply simp apply simp
      apply(auto) []
          apply(rule le_ASSERTI)+
       apply(rule ASSERT_leI) apply simp
      apply(auto) []
       apply(rule bindT_mono)
        apply(rule bfs_refines_shortest_augmenting_spec)
        apply simp
      apply(auto split: option.splits) 
      done

 (*
      apply refine_rcg
      apply refine_dref_type
      apply (vc_solve simp: bfs_refines_shortest_augmenting_spec)
      done *)  
 
  lemma  edka4_correct: "edka4 \<le> \<Down> Id (SPECT (emb isMaxFlow (enat (EdKa.edka_time c shortest_path_time edru.augment_with_path_time))))"
    apply(rule order.trans) apply(rule edka4_refine) 
    using edru.edka3_correct by simp 
end

locale Succ_Impl = Graph c for  c :: "'capacity::linordered_idom graph" +
  fixes list_append_time matrix_lookup_time :: nat    
begin

    subsection \<open>Implementing the Successor Function for BFS\<close>  

    text \<open>We implement the successor function in two steps.
      The first step shows how to obtain the successor function by
      filtering the list of adjacent nodes. This step contains the idea   
      of the implementation. The second step is purely technical, and makes 
      explicit the recursion of the filter function as a recursion combinator
      in the monad. This is required for the Sepref tool.
      \<close>

    text \<open>Note: We use @{term filter_rev} here, as it is tail-recursive, 
      and we are not interested in the order of successors.\<close>
    definition (in Graph) "rg_succ am cf u \<equiv>  
      filter_rev (\<lambda>v. cf (u,v) > 0) (am u)"
  
    lemma (in RGraph) rg_succ_ref1: "\<lbrakk>is_adj_map am\<rbrakk> 
      \<Longrightarrow> (rg_succ am cf u, Graph.E cf``{u}) \<in> \<langle>Id\<rangle>list_set_rel"
      unfolding Graph.E_def
      apply (clarsimp simp: list_set_rel_def br_def rg_succ_def filter_rev_alt; 
        intro conjI)
      using cfE_ss_invE resE_nonNegative 
      apply (auto 
        simp: is_adj_map_def less_le Graph.E_def 
        simp del: cf.zero_cap_simp zero_cap_simp) []
      apply (auto simp: is_adj_map_def) []
      done

    definition ps_get_op :: "_ \<Rightarrow> node \<Rightarrow> node list nrest" 
      where "ps_get_op am u \<equiv> ASSERT (u\<in>V) \<then> RETURNT (am u)"

    definition monadic_filter_rev_aux 
      :: "'a list \<Rightarrow> ('a \<Rightarrow> bool nrest) \<Rightarrow> 'a list \<Rightarrow> 'a list nrest"
    where
      "monadic_filter_rev_aux a P l \<equiv> RECT (\<lambda> D. (\<lambda>(l,a). case l of
        [] \<Rightarrow> RETURNT a 
      | (v#l) \<Rightarrow> do {
          c \<leftarrow> P v;
          a \<leftarrow> (if c then
              mop_append (\<lambda>_. list_append_time) v a
            else
              RETURNT a
          );
          D (l,a)
        }
      )) (l,a)"

    lemma monadic_filter_rev_aux_rule:
      assumes P_rule: "\<And>x. x\<in>set l \<Longrightarrow> P x \<le> SPECT (emb (\<lambda>r. r=Q x) P_t)"
      shows "monadic_filter_rev_aux a P l \<le> SPECT (emb (\<lambda>r. r=filter_rev_aux a Q l) (1+ length l * (P_t+list_append_time)))"
      using assms
    proof (induction l arbitrary: a)
      case Nil
      then show ?case
      apply (unfold monadic_filter_rev_aux_def) []
      apply (subst RECT_unfold, refine_mono)
      apply (fold monadic_filter_rev_aux_def) []
      apply simp unfolding emb'_def by (auto simp: pw_le_iff) 
    next
      case (Cons a l)      
      show ?case 
      apply (unfold monadic_filter_rev_aux_def) []
      apply (subst RECT_unfold, refine_mono)
      apply (fold monadic_filter_rev_aux_def) []
      apply(rule T_specifies_I)
        apply (vcg'\<open>-\<close> rules: mop_append Cons(2)[THEN T_specifies_rev, THEN T_conseq4]
                Cons(1)[THEN T_specifies_rev, THEN T_conseq4] )
           apply simp apply simp
          
        apply safe
         apply(rule Cons(1)[OF Cons(2), THEN T_specifies_rev, THEN T_conseq4] ) 
          apply simp
          apply(simp add: Some_le_emb'_conv Some_eq_emb'_conv)

          apply(rule Cons(1)[OF Cons(2), THEN T_specifies_rev, THEN T_conseq4] )
           apply simp
           apply(simp add: Some_le_emb'_conv Some_eq_emb'_conv) 
        done
    qed


    definition "monadic_filter_rev = monadic_filter_rev_aux []"

    lemma monadic_filter_rev_rule:
      assumes "\<And>x. x\<in>set l \<Longrightarrow> P x \<le> SPECT (emb (\<lambda>r. r=Q x) P_t)"
      shows "monadic_filter_rev P l \<le> SPECT (emb (\<lambda>r. r=filter_rev Q l) (1+ length l * (P_t+list_append_time)))"
      using monadic_filter_rev_aux_rule[where a="[]"] assms
      by (auto simp: monadic_filter_rev_def filter_rev_def)

    definition "rg_succ2 am cf u \<equiv> do {
      l \<leftarrow> ps_get_op am u;
      monadic_filter_rev (\<lambda>v. do {
        x \<leftarrow> RGraph_impl.cf_get c matrix_lookup_time cf (u,v);
        RETURNT (x>0)
      }) l
    }"

    definition "rg_succ_time len = (1+ len * (matrix_lookup_time+list_append_time))"

    lemma rg_succ_ref2: 
      assumes PS: "is_adj_map am" and V: "u\<in>V"
          and RG: "RGraph c s t cf"
      shows "rg_succ2 am cf u \<le> SPECT [rg_succ am cf u \<mapsto> rg_succ_time (length (am u)) ]"
    proof -
      have "\<forall>v\<in>set (am u). valid_edge (u,v)"
        using PS V
        by (auto simp: is_adj_map_def Graph.V_def)

      thm monadic_filter_rev_rule

      thus ?thesis  
        unfolding rg_succ2_def rg_succ_def ps_get_op_def
        unfolding RGraph_impl.cf_get_def[unfolded RGraph_impl_def, OF RG] apply simp
      apply(rule T_specifies_I)
        apply (vcg'\<open>-\<close> rules: monadic_filter_rev_rule[where Q="(\<lambda>v. 0 < cf (u, v))" and P_t="matrix_lookup_time", THEN T_specifies_rev, THEN T_conseq4] )
        subgoal 
          apply(rule T_specifies_I)
          apply (vcg'\<open>-\<close> rules: matrix_get) by(auto simp: Some_le_emb'_conv)
        apply (simp_all add: V Some_le_emb'_conv emb_eq_Some_conv rg_succ_time_def)
 (*
        apply (refine_vcg monadic_filter_rev_rule[
            where Q="(\<lambda>v. 0 < cf (u, v))", THEN order_trans])
        by (vc_solve simp: V) *) done
    qed       
 
    term RPreGraph
    lemma   rg_succ_ref:
      assumes A: "is_adj_map am"
      assumes B: "u\<in>V" and RG: "RGraph c s t cf"
      shows "rg_succ2 am cf u \<le> SPECT (emb (\<lambda>l. (l,(Graph.E cf)``{u}) \<in> \<langle>Id\<rangle>list_set_rel) (rg_succ_time (length (am u))))"      
     

          apply(rule T_specifies_I)
      apply (vcg'\<open>-\<close> rules: rg_succ_ref2[OF A B RG, THEN T_specifies_rev, THEN T_conseq4])
      using  RGraph.rg_succ_ref1[OF RG A, of u]   
      apply(auto simp add:Some_eq_emb'_conv Some_le_emb'_conv split: if_splits)
 (*
      by (auto simp: pw_le_iff refine_pw_simps) *) done

 
  lemma   rg_succ_ref':
      assumes A: "is_adj_map am"
      assumes B: "u\<in>V" and RG: "RGraph c s t cf"
      shows "rg_succ2 am cf u \<le> \<Down> (\<langle>nat_rel\<rangle>list_set_rel) (SPECT [Graph.E cf `` {u} \<mapsto>  (rg_succ_time (length (am u)))])"
    apply(rule order.trans[OF rg_succ_ref[OF assms]])
         apply(rule SPECT_refine)
        by (simp add: Some_eq_emb'_conv list_set_rel_def br_def  )
     


end

locale EdKa_Tab = Network c s t for c :: "'capacity::linordered_idom graph" and s t +
  fixes  set_insert_time map_dom_member_time set_delete_time map_update_time set_pick_time :: nat
    and list_append_time map_lookup_time set_empty_time set_isempty_time init_state_time :: nat

    and matrix_lookup_time matrix_set_time :: nat 
  assumes [simp]: "map_lookup_time > 0"
  assumes [simp]: "set_pick_time > 0" 
begin
 

    definition get_succs_list_time :: nat where
      "get_succs_list_time = (1+ (card V) * (matrix_lookup_time+list_append_time))"


    interpretation edka: EdKa_Res_Bfs c s t set_insert_time map_dom_member_time set_delete_time
      get_succs_list_time
      map_update_time set_pick_time 
      list_append_time map_lookup_time set_empty_time  set_isempty_time init_state_time
      matrix_lookup_time matrix_set_time 
      apply(standard) by auto
    

    definition "MYbfs2 cf succ ss tt = Augmenting_Path_BFS.bfs2 cf set_insert_time map_dom_member_time set_delete_time map_update_time set_pick_time  
          list_append_time map_lookup_time set_empty_time set_isempty_time init_state_time succ ss tt"


    definition "MYrg_succ2 am cf u = Succ_Impl.rg_succ2 c list_append_time matrix_lookup_time am cf u"

    subsection \<open>Adding Tabulation of Input\<close>  
    text \<open>
      Next, we add functions that will be refined to tabulate the input of 
      the algorithm, i.e., the network's capacity matrix and adjacency map,
      into efficient representations. 
      The capacity matrix is tabulated to give the initial residual graph,
      and the adjacency map is tabulated for faster access.

      Note, on the abstract level, the tabulation functions are just identity,
      and merely serve as marker constants for implementation.
      \<close>
    definition init_cf :: "'capacity graph nrest" 
      \<comment> \<open>Initialization of residual graph from network\<close>
      where "init_cf \<equiv> RETURNT c"
    definition init_ps :: "(node \<Rightarrow> node list) \<Rightarrow> _" 
      \<comment> \<open>Initialization of adjacency map\<close>
      where "init_ps am \<equiv> ASSERT (is_adj_map am) \<then> RETURNT am"

    definition compute_rflow :: "'capacity graph \<Rightarrow> 'capacity flow nrest" 
      \<comment> \<open>Extraction of result flow from residual graph\<close>
      where
      "compute_rflow cf \<equiv> ASSERT (RGraph c s t cf) \<then> RETURNT (flow_of_cf cf)"

    definition "bfs2_op am cf \<equiv> MYbfs2 cf (MYrg_succ2 am cf) s t"

    text \<open>We split the algorithm into a tabulation function, and the 
      running of the actual algorithm:\<close>
    definition "edka5_tabulate am \<equiv> do {
      cf \<leftarrow> init_cf;
      am \<leftarrow> init_ps am;
      RETURNT (cf,am)
    }"

    definition "edka5_run cf am \<equiv> do {
      (cf,_) \<leftarrow> whileT 
        (\<lambda>(cf,brk). \<not>brk) 
        (\<lambda>(cf,_). do {
          ASSERT (RGraph c s t cf);
          p \<leftarrow> bfs2_op am cf;
          case p of 
            None \<Rightarrow> RETURNT (cf,True)
          | Some p \<Rightarrow> do {
              ASSERT (p\<noteq>[]);
              ASSERT (Graph.isShortestPath cf s p t);
              bn \<leftarrow> edka.resCap_cf_impl'' cf p;
              cf \<leftarrow> edka.augment_cf_impl'' cf p bn;
              ASSERT (RGraph c s t cf);
              RETURNT (cf, False)
            }  
        })
        (cf,False);
      f \<leftarrow> compute_rflow cf;  
      RETURNT f
    }"

    definition "edka5 am \<equiv> do {
      (cf,am) \<leftarrow> edka5_tabulate am;
      edka5_run cf am
    }"
 
lemma k: "((a, b), aa, ba) \<in> Id \<times>\<^sub>r bool_rel \<Longrightarrow> a=aa" by auto
  


lemma is_adj_mapD_V: "\<And>am u. is_adj_map am \<Longrightarrow> u \<in> V  \<Longrightarrow> distinct (am u) \<and> set (am u) \<subseteq> V"
  unfolding is_adj_map_def unfolding V_def by auto

lemma is_adj_map_app_le_V: "is_adj_map am \<Longrightarrow> u \<in> V  \<Longrightarrow> length (am u) \<le> card V"
  apply(auto dest!: is_adj_mapD_V)
    apply(rule order.trans[where b="card (set (am u))"]) using distinct_card[symmetric] 
  apply fastforce apply(rule card_mono)  
  by auto



    lemma edka5_refine: "\<lbrakk>is_adj_map am\<rbrakk> \<Longrightarrow> edka5 am \<le> \<Down>Id edka.edka4"
      unfolding edka5_def edka5_tabulate_def edka5_run_def
        edka.edka4_def init_cf_def compute_rflow_def 
        init_ps_def Let_def   bfs2_op_def
      unfolding nres_bind_assoc nres_bind_left_identity prod.case 
      apply(rule ASSERT_leI) apply simp
      apply(rule bindT_refine) 
       apply(rule WHILET_refine[where R="Id \<times>\<^sub>r bool_rel"] ) apply simp
      apply simp  apply safe
      apply(rule le_R_ASSERTI)
       apply(rule ASSERT_leI)  apply simp      
       apply(rule bindT_refine[where R'=Id])
      subgoal 
        unfolding MYbfs2_def edka.MYbfs_def  apply(frule k) apply simp  
        apply(rule R_intro) 
        apply(rule Augmenting_Path_BFS.bfs2_refine)
         apply(simp add: Augmenting_Path_BFS_def)
        unfolding  MYrg_succ2_def
        apply(rule order.trans)
         apply(rule Succ_Impl.rg_succ_ref') apply simp  
          apply(simp add: RPreGraph.resV_netV[OF RGraph.this_loc_rpg])
         apply simp
        apply(rule nrest_Rel_mono)
        by (auto simp add: le_fun_def get_succs_list_time_def Succ_Impl.rg_succ_time_def
                RPreGraph.resV_netV[OF RGraph.this_loc_rpg] is_adj_map_app_le_V)
      apply (simp split: prod.split option.split)
      apply(rule le_R_ASSERTI)
      apply(rule ASSERT_leI) apply simp apply simp done
 
       (*
      apply refine_rcg
      apply refine_dref_type
      apply (vc_solve simp: )
      apply (rule refine_IdD)
      apply (rule Graph.bfs2_refine)
      apply (simp add: RPreGraph.resV_netV[OF RGraph.this_loc_rpg])
      apply (simp add: RGraph.rg_succ_ref)
      done *)  

lemma "(enat (EdKa.edka_time c edka.shortest_path_time (EdKa_Res_Up.augment_with_path_time c matrix_lookup_time matrix_set_time))) = foo"
  apply(subst EdKa_Res_Up.augment_with_path_time_def)
  unfolding EdKa_Res_Up_def EdKa_Res_Up_axioms_def apply auto oops

    thm edka.edka4_correct
  lemma  edka5_correct: "\<lbrakk>is_adj_map am\<rbrakk> \<Longrightarrow> edka5 am \<le> \<Down> Id (SPECT (emb isMaxFlow (enat (EdKa.edka_time c edka.shortest_path_time (EdKa_Res_Up.augment_with_path_time c matrix_lookup_time matrix_set_time)))))"
    apply(rule order.trans) apply(rule edka5_refine) 
    using edka.edka4_correct by simp_all 


end    
end