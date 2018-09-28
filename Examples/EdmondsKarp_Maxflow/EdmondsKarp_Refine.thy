section \<open>Implementation of the Edmonds-Karp Algorithm\<close>
theory EdmondsKarp_Refine
imports 
  EdmondsKarp_Algo
  Augmenting_Path_BFS
begin

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
    definition "find_shortest_augmenting_spec_cf_time = 10"
  
    definition "find_shortest_augmenting_spec_cf cf \<equiv> 
      ASSERT (RGraph c s t cf) \<then>
      SPECT (emb (\<lambda>
        None \<Rightarrow> \<not>Graph.connected cf s t 
      | Some p \<Rightarrow> Graph.isShortestPath cf s p t) find_shortest_augmenting_spec_cf_time)"

    lemma (in RGraph) find_shortest_augmenting_spec_cf_refine: 
       "find_shortest_augmenting_spec_cf cf 
      \<le> find_shortest_augmenting_spec (flow_of_cf cf)"
      unfolding f_def[symmetric]
      unfolding find_shortest_augmenting_spec_cf_def 
        and find_shortest_augmenting_spec_def
        and find_shortest_augmenting_spec_cf_time_def shortestpath_time_def
      by (auto 
        simp: pw_le_iff refine_pw_simps Some_eq_emb'_conv numeral_eq_enat
        simp: this_loc rg_is_cf
        simp: f.isAugmentingPath_def Graph.connected_def Graph.isSimplePath_def 
        dest: cf.shortestPath_is_path
        split: option.split)  
      
    text \<open>This leads to the following refined algorithm\<close>  
    definition "edka2 \<equiv> do {
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
              cf \<leftarrow> RETURNT (Graph.augment_cf cf (set p) (resCap_cf cf p));
              ASSERT (RGraph c s t cf);
              RETURNT (cf, False)
            }  
        })
        (cf,False);
      ASSERT (RGraph c s t cf);
      f \<leftarrow> RETURNT (flow_of_cf cf);  
      RETURNT f
    }"

    lemma edka2_refine: "edka2 \<le> \<Down>Id edka"
    proof -
      (* have [refine_dref_RELATES]: "RELATES cfi_rel" by (simp add: RELATES_def) *)

      show ?thesis
        unfolding edka2_def edka_def (*
        (*apply (rewrite in "let f' = NFlow.augmentingFlow c _ _ in _" Let_def)
        apply (rewrite in "let f = flow_of_cf _ in _" Let_def)*)
        apply (refine_rcg)
        apply refine_dref_type
        apply vc_solve

        \<comment> \<open>Solve some left-over verification conditions one by one\<close>
        apply (drule NFlow.is_RGraph; 
            auto simp: cfi_rel_def br_def residualGraph_zero_flow flow_of_c; 
            fail)
        apply (auto simp: cfi_rel_def br_def; fail)
        using RGraph.find_shortest_augmenting_spec_cf_refine
        apply (auto simp: cfi_rel_def br_def; fail)
        apply (auto simp: cfi_rel_def br_def simp: RPreGraph.rg_fo_inv[OF RGraph.this_loc_rpg]; fail)
        apply (drule (1) augment_cf_refine; simp add: cfi_rel_def br_def; fail)
        apply (simp add: augment_cf_refine; fail)
        apply (auto simp: cfi_rel_def br_def; fail)
        apply (auto simp: cfi_rel_def br_def; fail)
        done *)
        sorry
    qed    

    subsection \<open>Implementation of Bottleneck Computation and Augmentation\<close>  
    text \<open>We will access the capacities in the residual graph
      only by a get-operation, which asserts that the edges are valid\<close>
    
    abbreviation (input) valid_edge :: "edge \<Rightarrow> bool" where
      "valid_edge \<equiv> \<lambda>(u,v). u\<in>V \<and> v\<in>V"

    definition cf_get 
      :: "'capacity graph \<Rightarrow> edge \<Rightarrow> 'capacity nrest" 
      where "cf_get cf e \<equiv> ASSERT (valid_edge e) \<then> RETURNT (cf e)"  
    definition cf_set 
      :: "'capacity graph \<Rightarrow> edge \<Rightarrow> 'capacity \<Rightarrow> 'capacity graph nrest"
      where "cf_set cf e cap \<equiv> ASSERT (valid_edge e) \<then> RETURNT (cf(e:=cap))"  

    definition resCap_cf_impl :: "'capacity graph \<Rightarrow> path \<Rightarrow> 'capacity nrest" 
    where "resCap_cf_impl cf p \<equiv> 
      case p of
        [] \<Rightarrow> RETURNT (0::'capacity)
      | (e#p) \<Rightarrow> do {
          cap \<leftarrow> cf_get cf e;
          ASSERT (distinct p);
          nfoldli 
            p (\<lambda>_. True)
            (\<lambda>e cap. do {
              cape \<leftarrow> cf_get cf e;
              RETURNT (min cape cap)
            }) 
            cap
        }"

    definition "resCap_cf_impl_time = 10"

    lemma (in RGraph) resCap_cf_impl_refine:   
      assumes AUG: "cf.isSimplePath s p t"
      shows "resCap_cf_impl cf p \<le> SPECT (emb (\<lambda>r. r = resCap_cf cf p) resCap_cf_impl_time)"
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
        apply (simp only: list.case) (*
        apply (refine_vcg nfoldli_rule[where 
            I = "\<lambda>l l' cap. 
              cap = Min (cf`insert e (set l)) 
            \<and> set (l@l') \<subseteq> Collect valid_edge"])
        apply (auto intro!: arg_cong[where f=Min])
        done *) sorry
    qed    

    definition (in Graph) 
      "augment_edge e cap \<equiv> (c(
                  e := c e - cap, 
        prod.swap e := c (prod.swap e) + cap))"

    (* TODO: This would be much simpler to prove if we had a characterization 
      of simple-path only depending on p. *)    
    lemma (in Graph) augment_cf_inductive:
      fixes e cap
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
        
    definition "augment_edge_impl cf e cap \<equiv> do {
      v \<leftarrow> cf_get cf e; cf \<leftarrow> cf_set cf e (v-cap);
      e \<leftarrow> RETURNT (prod.swap e);
      v \<leftarrow> cf_get cf e; cf \<leftarrow> cf_set cf e (v+cap);
      RETURNT cf
    }"

    definition "augment_edge_impl_time = 10"
  
    lemma augment_edge_impl_refine: 
      assumes "valid_edge e" "\<forall>u. e\<noteq>(u,u)"
      shows "augment_edge_impl cf e cap 
          \<le> SPECT (emb  (\<lambda>r. r = Graph.augment_edge cf e cap) augment_edge_impl_time)"
      using assms
      unfolding augment_edge_impl_def Graph.augment_edge_def 
      unfolding cf_get_def cf_set_def (*
      apply refine_vcg
      apply auto
      done *) sorry
      
    definition augment_cf_impl 
      :: "'capacity graph \<Rightarrow> path \<Rightarrow> 'capacity \<Rightarrow> 'capacity graph nrest" 
      where
      "augment_cf_impl cf p x \<equiv> do {
        RECT (\<lambda>D. \<lambda>
          ([],cf) \<Rightarrow> RETURNT cf
        | (e#p,cf) \<Rightarrow> do {
            cf \<leftarrow> augment_edge_impl cf e x;
            D (p,cf)
          }  
        ) (p,cf)
      }"

    text \<open>Deriving the corresponding recursion equations\<close>  
    lemma augment_cf_impl_simps[simp]: 
      "augment_cf_impl cf [] x = RETURNT cf"
      "augment_cf_impl cf (e#p) x = do { 
        cf \<leftarrow> augment_edge_impl cf e x; 
        augment_cf_impl cf p x}"
      apply (simp add: augment_cf_impl_def)
      apply (subst RECT_unfold, refine_mono)
      apply simp
      
      apply (simp add: augment_cf_impl_def)
      apply (subst RECT_unfold, refine_mono)
      apply simp
      done      

    lemma augment_cf_impl_aux:    
      assumes "\<forall>e\<in>set p. valid_edge e"
      assumes "\<exists>s. Graph.isSimplePath cf s p t"
      shows "augment_cf_impl cf p x \<le> RETURNT (Graph.augment_cf cf (set p) x)"
      using assms
      apply (induction p arbitrary: cf)
      apply (simp add: Graph.augment_cf_empty)

      apply clarsimp
      apply (subst Graph.augment_cf_inductive, assumption)
  (*
      apply (refine_vcg augment_edge_impl_refine[THEN order_trans])
      apply simp
      apply simp
      apply (auto dest: Graph.isSPath_no_selfloop) []
      apply (rule order_trans, rprems)
        apply (drule Graph.augment_cf_inductive(2)[where cap=x]; simp)
        apply simp
      done  *) sorry
      
    lemma (in RGraph) augment_cf_impl_refine:     
      assumes "Graph.isSimplePath cf s p t"
      shows "augment_cf_impl cf p x \<le> RETURNT (Graph.augment_cf cf (set p) x)"
      apply (rule augment_cf_impl_aux)
      using assms cf.E_ss_VxV apply (auto simp: cf.isSimplePath_def dest!: cf.isPath_edgeset) []
      using assms by blast
      
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
              bn \<leftarrow> resCap_cf_impl cf p;
              cf \<leftarrow> augment_cf_impl cf p bn;
              ASSERT (RGraph c s t cf);
              RETURNT (cf, False)
            }  
        })
        (cf,False);
      ASSERT (RGraph c s t cf);
      f \<leftarrow> RETURNT (flow_of_cf cf);  
      RETURNT f
    }"

    lemma edka3_refine: "edka3 \<le> \<Down>Id edka2"
      unfolding edka3_def edka2_def (*
      apply (rewrite in "let cf = Graph.augment_cf _ _ _ in _" Let_def)
      apply refine_rcg
      apply refine_dref_type
      apply (vc_solve)
      apply (drule Graph.shortestPath_is_simple)
      apply (frule (1) RGraph.resCap_cf_impl_refine)
      apply (frule (1) RGraph.augment_cf_impl_refine)
      apply (auto simp: pw_le_iff refine_pw_simps)
      done *) sorry
      
    
    subsection \<open>Refinement to use BFS\<close>

    text \<open>We refine the Edmonds-Karp algorithm to use breadth first search (BFS)\<close>
    definition "edka4 \<equiv> do {
      cf \<leftarrow> RETURNT c;

      (cf,_) \<leftarrow> whileT 
        (\<lambda>(cf,brk). \<not>brk) 
        (\<lambda>(cf,_). do {
          ASSERT (RGraph c s t cf);
          p \<leftarrow> Graph.bfs cf s t;
          case p of 
            None \<Rightarrow> RETURNT (cf,True)
          | Some p \<Rightarrow> do {
              ASSERT (p\<noteq>[]);
              ASSERT (Graph.isShortestPath cf s p t);
              bn \<leftarrow> resCap_cf_impl cf p;
              cf \<leftarrow> augment_cf_impl cf p bn;
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
    lemma bfs_refines_shortest_augmenting_spec: 
      "Graph.bfs cf s t \<le> find_shortest_augmenting_spec_cf cf"
      unfolding find_shortest_augmenting_spec_cf_def
      apply (rule le_ASSERTI)
      apply (rule order_trans)
      apply (rule Graph.bfs_correct)
      apply (simp add: RPreGraph.resV_netV[OF RGraph.this_loc_rpg] s_node)
      apply (simp add: RPreGraph.resV_netV[OF RGraph.this_loc_rpg]) 
      apply(auto intro: embtimeI simp add: bfs_time_def find_shortest_augmenting_spec_cf_time_def) 
      done

    lemma edka4_refine: "edka4 \<le> \<Down>Id edka3"
      unfolding edka4_def edka3_def (*
      apply refine_rcg
      apply refine_dref_type
      apply (vc_solve simp: bfs_refines_shortest_augmenting_spec)
      done *) sorry


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
    definition "rg_succ am cf u \<equiv>  
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
          a \<leftarrow> RETURNT (if c then v#a else a);
          D (l,a)
        }
      )) (l,a)"

    lemma monadic_filter_rev_aux_rule:
      assumes "\<And>x. x\<in>set l \<Longrightarrow> P x \<le> SPECT (emb (\<lambda>r. r=Q x) P_t)"
      shows "monadic_filter_rev_aux a P l \<le> SPECT (emb (\<lambda>r. r=filter_rev_aux a Q l) (1+ length l * P_t))"
      using assms
      apply (induction l arbitrary: a)

      subgoal
      apply (unfold monadic_filter_rev_aux_def) []
      apply (subst RECT_unfold, refine_mono)
      apply (fold monadic_filter_rev_aux_def) []
      apply simp unfolding emb'_def by (auto simp: pw_le_iff) 

      subgoal
      apply (unfold monadic_filter_rev_aux_def) []
      apply (subst RECT_unfold, refine_mono)
      apply (fold monadic_filter_rev_aux_def) []
      apply (auto simp: pw_le_iff refine_pw_simps)
        sorry
      done

    definition "monadic_filter_rev = monadic_filter_rev_aux []"

    lemma monadic_filter_rev_rule:
      assumes "\<And>x. x\<in>set l \<Longrightarrow> P x \<le> SPECT (emb (\<lambda>r. r=Q x) P_t)"
      shows "monadic_filter_rev P l \<le> SPECT (emb (\<lambda>r. r=filter_rev Q l) (1+ length l * P_t))"
      using monadic_filter_rev_aux_rule[where a="[]"] assms
      by (auto simp: monadic_filter_rev_def filter_rev_def)

    definition "rg_succ2 am cf u \<equiv> do {
      l \<leftarrow> ps_get_op am u;
      monadic_filter_rev (\<lambda>v. do {
        x \<leftarrow> cf_get cf (u,v);
        RETURNT (x>0)
      }) l
    }"

    lemma (in RGraph) rg_succ_ref2: 
      assumes PS: "is_adj_map am" and V: "u\<in>V"
      shows "rg_succ2 am cf u \<le> RETURNT (rg_succ am cf u)"
    proof -
      have "\<forall>v\<in>set (am u). valid_edge (u,v)"
        using PS V
        by (auto simp: is_adj_map_def Graph.V_def)
      
      thus ?thesis  
        unfolding rg_succ2_def rg_succ_def ps_get_op_def cf_get_def (*
        apply (refine_vcg monadic_filter_rev_rule[
            where Q="(\<lambda>v. 0 < cf (u, v))", THEN order_trans])
        by (vc_solve simp: V) *) sorry
    qed    

    definition "rg_succ2_time = 10"

    lemma (in RGraph) rg_succ_ref:
      assumes A: "is_adj_map am"
      assumes B: "u\<in>V"
      shows "rg_succ2 am cf u \<le> SPECT (emb (\<lambda>l. (l,cf.E``{u}) \<in> \<langle>Id\<rangle>list_set_rel) rg_succ2_time)"      
      using rg_succ_ref1[OF A, of u] rg_succ_ref2[OF A B] (*
      by (auto simp: pw_le_iff refine_pw_simps) *) sorry


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

    definition "bfs2_op am cf \<equiv> Graph.bfs2 cf (rg_succ2 am cf) s t"

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
              bn \<leftarrow> resCap_cf_impl cf p;
              cf \<leftarrow> augment_cf_impl cf p bn;
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

    lemma edka5_refine: "\<lbrakk>is_adj_map am\<rbrakk> \<Longrightarrow> edka5 am \<le> \<Down>Id edka4"
      unfolding edka5_def edka5_tabulate_def edka5_run_def
        edka4_def init_cf_def compute_rflow_def (*
        init_ps_def Let_def nres_monad_laws bfs2_op_def
      apply refine_rcg
      apply refine_dref_type
      apply (vc_solve simp: )
      apply (rule refine_IdD)
      apply (rule Graph.bfs2_refine)
      apply (simp add: RPreGraph.resV_netV[OF RGraph.this_loc_rpg])
      apply (simp add: RGraph.rg_succ_ref)
      done *) sorry

end    
end