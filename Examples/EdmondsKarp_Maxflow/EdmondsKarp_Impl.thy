theory EdmondsKarp_Impl
  imports EdmondsKarp_Refine  
 (* "../../Refine_Imperative_HOL/IICF" *)                      
    Augmenting_Path_BFS_Impl
    "../../Refine_Imperative_HOL/IICF/Impl/IICF_Array_Matrix"
begin
  subsection \<open>Imperative Implementation\<close>  
  text \<open>In this section we provide an efficient imperative implementation,
    using the Sepref tool. It is mostly technical, setting up the mappings
    from abstract to concrete data structures, and then refining the algorithm,
    function by function.  
    \<close>

  text \<open>
    This is also the point where we have to choose the implementation of 
    capacities. Up to here, they have been a polymorphic type with a
    typeclass constraint of being a linearly ordered integral domain.
    Here, we switch to @{typ [source] capacity_impl} (@{typ capacity_impl}).
    \<close>
  locale Network_Impl = Network c s t for c :: "capacity_impl graph" and s t

  text \<open>Moreover, we assume that the nodes are natural numbers less 
    than some number @{term N}, which will become an additional parameter 
    of our algorithm. \<close>
  locale Edka_Impl = Network_Impl +
    fixes N :: nat
    assumes V_ss: "V\<subseteq>{0..<N}"
  begin  
    lemma this_loc: "Edka_Impl c s t N" by unfold_locales

    lemma E_ss: "E \<subseteq> {0..<N}\<times>{0..<N}" using E_ss_VxV V_ss by auto

    lemma mtx_nonzero_iff[simp]: "mtx_nonzero c = E" unfolding E_def by (auto simp: mtx_nonzero_def)

    lemma mtx_nonzeroN: "mtx_nonzero c \<subseteq> {0..<N}\<times>{0..<N}" using E_ss by simp

    lemma [simp]: "v\<in>V \<Longrightarrow> v<N" using V_ss by auto


    text \<open>Declare some variables to Sepref. \<close>
    lemmas [id_rules] = 
      itypeI[Pure.of N "TYPE(nat)"]  
      itypeI[Pure.of s "TYPE(node)"]  
      itypeI[Pure.of t "TYPE(node)"]  
      itypeI[Pure.of c "TYPE(capacity_impl graph)"]  
    text \<open>Instruct Sepref to not refine these parameters. This is expressed
      by using identity as refinement relation.\<close>
    lemmas [sepref_import_param] = 
      IdI[of N]
      IdI[of s]
      IdI[of t]
      (*IdI[of c]*)

   (* lemma [sepref_fr_rules]: "(uncurry0 (return c),uncurry0 (return c))\<in>unit_assn\<^sup>k \<rightarrow>\<^sub>a pure (nat_rel\<times>\<^sub>rnat_rel \<rightarrow> int_rel)"
      apply sepref_to_hoare by sep_auto *)


    subsubsection \<open>Implementation of Adjacency Map by Array\<close>  
    definition "is_am am psi 
      \<equiv> \<exists>\<^sub>Al. psi \<mapsto>\<^sub>a l 
          * \<up>(length l = N \<and> (\<forall>i<N. l!i = am i) 
              \<and> (\<forall>i\<ge>N. am i = []))"
  (*
    lemma is_am_precise[safe_constraint_rules]: "precise (is_am)"
      apply rule
      unfolding is_am_def
      apply clarsimp
      apply (rename_tac l l')
      apply prec_extract_eqs
      apply (rule ext)
      apply (rename_tac i)
      apply (case_tac "i<length l'")
      apply fastforce+
      done *)

    sepref_decl_intf i_ps is "nat \<Rightarrow> nat list" 

    definition (in -) "ps_get_imp psi u \<equiv> Array.nth psi u"

    (* lemma [def_pat_rules]: "Network.ps_get_op$c \<equiv> UNPROTECT ps_get_op" by simp *)
    sepref_register "PR_CONST ps_get_op" :: "i_ps \<Rightarrow> node \<Rightarrow> node list nrest"

    lemma ps_get_op_refine[sepref_fr_rules]: 
      "(uncurry ps_get_imp, uncurry (PR_CONST ps_get_op)) 
        \<in> is_am\<^sup>k *\<^sub>a (pure Id)\<^sup>k \<rightarrow>\<^sub>a list_assn (pure Id)"
      unfolding list_assn_pure_conv
      apply sepref_to_hoare
      using V_ss unfolding is_am_def   ps_get_imp_def  ps_get_op_def autoref_tag_defs apply simp
      apply(rule hnr_ASSERT)
      apply(rule hn_refine_cons_pre) unfolding entailst_def 
      apply (rule extract_cost_otherway[OF _ nth_rule] )
      apply auto[]
      
      apply (sep_auto simp:  
            simp: is_am_def pure_def ps_get_imp_def 
            simp: ps_get_op_def refine_pw_simps)
      subgoal for b a ai h as n l apply(cases "b<length l")
        apply(subst Array.execute_nth(1)) apply simp
        sorry

    lemma is_pred_succ_no_node: "\<lbrakk>is_adj_map a; u\<notin>V\<rbrakk> \<Longrightarrow> a u = []"
      unfolding is_adj_map_def V_def
      by auto

    lemma [sepref_fr_rules]: "(Array.make N, PR_CONST init_ps) 
      \<in> (pure Id)\<^sup>k \<rightarrow>\<^sub>a is_am" 
      apply sepref_to_hoare
      using V_ss
      apply (sep_auto simp: init_ps_def refine_pw_simps is_am_def pure_def
        intro: is_pred_succ_no_node) sorry

    lemma [def_pat_rules]: "Network.init_ps$c \<equiv> UNPROTECT init_ps" by simp
    sepref_register "PR_CONST init_ps" :: "(node \<Rightarrow> node list) \<Rightarrow> i_ps nrest"

    abbreviation "matrix_lookup_time == 1::nat" 
    abbreviation "matrix_set_time == 1::nat" 
    definition cf_get' where "cf_get' cff e = cf_get cff e matrix_lookup_time"
    definition cf_set' where "cf_set' cff e cap= cf_set cff e cap matrix_set_time"

    subsubsection \<open>Implementation of Capacity Matrix by Array\<close>  
    lemma [def_pat_rules]: "Network.cf_get$c \<equiv> UNPROTECT cf_get" by simp
    lemma [def_pat_rules]: "Network.cf_set$c \<equiv> UNPROTECT cf_set" by simp

    sepref_register 
      "PR_CONST cf_get'" :: "capacity_impl i_mtx \<Rightarrow> edge \<Rightarrow> capacity_impl nrest"
    sepref_register 
      "PR_CONST cf_set'" :: "capacity_impl i_mtx \<Rightarrow> edge \<Rightarrow> capacity_impl 
        \<Rightarrow> capacity_impl i_mtx nrest"

    text \<open>We have to link the matrix implementation, which encodes the bound, 
      to the abstract assertion of the bound\<close>

    sepref_definition cf_get_impl is "uncurry (PR_CONST cf_get')" :: "(asmtx_assn N id_assn)\<^sup>k *\<^sub>a (prod_assn id_assn id_assn)\<^sup>k \<rightarrow>\<^sub>a id_assn"
      unfolding PR_CONST_def cf_get_def[abs_def]
      apply sepref_dbg_preproc
  apply sepref_dbg_cons_init
  apply sepref_dbg_id_keep 
     apply sepref_dbg_monadify

     apply sepref_dbg_opt_init
                                        
  apply sepref_dbg_trans_keep 

  apply sepref_dbg_opt
  apply sepref_dbg_cons_solve \<comment> \<open>Frame rule, recovering the invalidated list 
    or pure elements, propagating recovery over the list structure\<close>
  apply sepref_dbg_cons_solve \<comment> \<open>Trivial frame rule\<close>
  apply sepref_dbg_constraints
      done
    lemmas [sepref_fr_rules] = cf_get_impl.refine
    lemmas [sepref_opt_simps] = cf_get_impl_def

    sepref_definition cf_set_impl is "uncurry2 (PR_CONST cf_set)" :: "(asmtx_assn N id_assn)\<^sup>d *\<^sub>a (prod_assn id_assn id_assn)\<^sup>k *\<^sub>a id_assn\<^sup>k \<rightarrow>\<^sub>a asmtx_assn N id_assn"
      unfolding PR_CONST_def cf_set_def[abs_def]
      by sepref
    lemmas [sepref_fr_rules] = cf_set_impl.refine
    lemmas [sepref_opt_simps] = cf_set_impl_def


    sepref_thm init_cf_impl is "uncurry0 (PR_CONST init_cf)" :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a asmtx_assn N id_assn"
      unfolding PR_CONST_def init_cf_def 
      using E_ss
      apply (rewrite op_mtx_new_def[of c, symmetric])
      apply (rewrite amtx_fold_custom_new[of N N])
      by sepref

    concrete_definition (in -) init_cf_impl uses Edka_Impl.init_cf_impl.refine_raw is "(uncurry0 ?f,_)\<in>_" 
    prepare_code_thms (in -) init_cf_impl_def
    lemmas [sepref_fr_rules] = init_cf_impl.refine[OF this_loc]  

    (* TODO: Use sepref to synthesize the get-operations! *)
    lemma amtx_cnv: "amtx_assn N M id_assn = IICF_Array_Matrix.is_amtx N M" 
      by (simp add: amtx_assn_def)

    (*

    lemma init_cf_imp_refine[sepref_fr_rules]: 
      "(uncurry0 (mtx_new N c), uncurry0 (PR_CONST init_cf)) 
        \<in> (pure unit_rel)\<^sup>k \<rightarrow>\<^sub>a (asmtx_assn N id_assn)"
      unfolding asmtx_cnv
      apply sepref_to_hoare
      using E_ss
      by (sep_auto simp: init_cf_def)
    *)  

    lemma [def_pat_rules]: "Network.init_cf$c \<equiv> UNPROTECT init_cf" by simp
    sepref_register "PR_CONST init_cf" :: "capacity_impl i_mtx nres"

    subsubsection \<open>Representing Result Flow as Residual Graph\<close>
    definition (in Network_Impl) "is_rflow N f cfi 
      \<equiv> \<exists>\<^sub>Acf. asmtx_assn N id_assn cf cfi * \<up>(RGraph c s t cf \<and> f = flow_of_cf cf)"
    lemma is_rflow_precise[safe_constraint_rules]: "precise (is_rflow N)"
      apply rule
      unfolding is_rflow_def
      apply (clarsimp simp: amtx_assn_def)
      apply prec_extract_eqs
      apply simp
      done

    sepref_decl_intf i_rflow is "nat\<times>nat \<Rightarrow> int"

    lemma [sepref_fr_rules]: 
      "(\<lambda>cfi. RETURN cfi, PR_CONST compute_rflow) \<in> (asmtx_assn N id_assn)\<^sup>d \<rightarrow>\<^sub>a is_rflow N"
      unfolding amtx_cnv
      apply sepref_to_hoare
      apply (sep_auto simp: amtx_cnv compute_rflow_def is_rflow_def refine_pw_simps hn_ctxt_def)
      done

    lemma [def_pat_rules]: 
      "Network.compute_rflow$c$s$t \<equiv> UNPROTECT compute_rflow" by simp
    sepref_register 
      "PR_CONST compute_rflow" :: "capacity_impl i_mtx \<Rightarrow> i_rflow nres"


    subsubsection \<open>Implementation of Functions\<close>  

    schematic_goal rg_succ2_impl:
      fixes am :: "node \<Rightarrow> node list" and cf :: "capacity_impl graph"
      notes [id_rules] = 
        itypeI[Pure.of u "TYPE(node)"]
        itypeI[Pure.of am "TYPE(i_ps)"]
        itypeI[Pure.of cf "TYPE(capacity_impl i_mtx)"]
      notes [sepref_import_param] = IdI[of N]
      notes [sepref_fr_rules] = HOL_list_empty_hnr
      shows "hn_refine (hn_ctxt is_am am psi * hn_ctxt (asmtx_assn N id_assn) cf cfi * hn_val nat_rel u ui) (?c::?'c Heap) ?\<Gamma> ?R (rg_succ2 am cf u)"
      unfolding rg_succ2_def APP_def monadic_filter_rev_def monadic_filter_rev_aux_def
      (* TODO: Make setting up combinators for sepref simpler, then we do not need to unfold! *)
      using [[id_debug, goals_limit = 1]]
      by sepref
    concrete_definition (in -) succ_imp uses Edka_Impl.rg_succ2_impl
    prepare_code_thms (in -) succ_imp_def

    lemma succ_imp_refine[sepref_fr_rules]: 
      "(uncurry2 (succ_imp N), uncurry2 (PR_CONST rg_succ2)) 
        \<in> is_am\<^sup>k *\<^sub>a (asmtx_assn N id_assn)\<^sup>k *\<^sub>a (pure Id)\<^sup>k \<rightarrow>\<^sub>a list_assn (pure Id)"
      apply rule
      using succ_imp.refine[OF this_loc]            
      by (auto simp: hn_ctxt_def mult_ac split: prod.split)

    lemma [def_pat_rules]: "Network.rg_succ2$c \<equiv> UNPROTECT rg_succ2" by simp
    sepref_register 
      "PR_CONST rg_succ2" :: "i_ps \<Rightarrow> capacity_impl i_mtx \<Rightarrow> node \<Rightarrow> node list nres"

    
    lemma [sepref_import_param]: "(min,min)\<in>Id\<rightarrow>Id\<rightarrow>Id" by simp


    abbreviation "is_path \<equiv> list_assn (prod_assn (pure Id) (pure Id))"

    schematic_goal resCap_imp_impl:
      fixes am :: "node \<Rightarrow> node list" and cf :: "capacity_impl graph" and p pi
      notes [id_rules] = 
        itypeI[Pure.of p "TYPE(edge list)"]
        itypeI[Pure.of cf "TYPE(capacity_impl i_mtx)"]
      notes [sepref_import_param] = IdI[of N]
      shows "hn_refine 
        (hn_ctxt (asmtx_assn N id_assn) cf cfi * hn_ctxt is_path p pi) 
        (?c::?'c Heap) ?\<Gamma> ?R 
        (resCap_cf_impl cf p)"
      unfolding resCap_cf_impl_def APP_def
      using [[id_debug, goals_limit = 1]]
      by sepref
    concrete_definition (in -) resCap_imp uses Edka_Impl.resCap_imp_impl
    prepare_code_thms (in -) resCap_imp_def

    lemma resCap_impl_refine[sepref_fr_rules]: 
      "(uncurry (resCap_imp N), uncurry (PR_CONST resCap_cf_impl)) 
        \<in> (asmtx_assn N id_assn)\<^sup>k *\<^sub>a (is_path)\<^sup>k \<rightarrow>\<^sub>a (pure Id)"
      apply sepref_to_hnr
      apply (rule hn_refine_preI)
      apply (clarsimp 
        simp: uncurry_def list_assn_pure_conv hn_ctxt_def 
        split: prod.split)
      apply (clarsimp simp: pure_def)
      apply (rule hn_refine_cons[OF _ resCap_imp.refine[OF this_loc] _])
      apply (simp add: list_assn_pure_conv hn_ctxt_def)
      apply (simp add: pure_def)
      apply (sep_auto simp add: hn_ctxt_def pure_def intro!: enttI)
      apply (simp add: pure_def)
      done

    lemma [def_pat_rules]: 
      "Network.resCap_cf_impl$c \<equiv> UNPROTECT resCap_cf_impl" 
      by simp
    sepref_register "PR_CONST resCap_cf_impl" 
      :: "capacity_impl i_mtx \<Rightarrow> path \<Rightarrow> capacity_impl nres"
    
    sepref_thm augment_imp is "uncurry2 (PR_CONST augment_cf_impl)" :: "((asmtx_assn N id_assn)\<^sup>d *\<^sub>a (is_path)\<^sup>k *\<^sub>a (pure Id)\<^sup>k \<rightarrow>\<^sub>a asmtx_assn N id_assn)"
      unfolding augment_cf_impl_def[abs_def] augment_edge_impl_def PR_CONST_def
      using [[id_debug, goals_limit = 1]]
      by sepref 
    concrete_definition (in -) augment_imp uses Edka_Impl.augment_imp.refine_raw is "(uncurry2 ?f,_)\<in>_"
    prepare_code_thms (in -) augment_imp_def
    lemma augment_impl_refine[sepref_fr_rules]: 
      "(uncurry2 (augment_imp N), uncurry2 (PR_CONST augment_cf_impl)) 
        \<in> (asmtx_assn N id_assn)\<^sup>d *\<^sub>a (is_path)\<^sup>k *\<^sub>a (pure Id)\<^sup>k \<rightarrow>\<^sub>a asmtx_assn N id_assn"
      using augment_imp.refine[OF this_loc] .

    lemma [def_pat_rules]: 
      "Network.augment_cf_impl$c \<equiv> UNPROTECT augment_cf_impl" 
      by simp
    sepref_register "PR_CONST augment_cf_impl" 
      :: "capacity_impl i_mtx \<Rightarrow> path \<Rightarrow> capacity_impl \<Rightarrow> capacity_impl i_mtx nres"

    sublocale bfs: Impl_Succ 
      "snd" 
      "TYPE(i_ps \<times> capacity_impl i_mtx)" 
      "PR_CONST (\<lambda>(am,cf). rg_succ2 am cf)" 
      "prod_assn is_am (asmtx_assn N id_assn)" 
      "\<lambda>(am,cf). succ_imp N am cf"
      unfolding APP_def
      apply unfold_locales
      apply (simp add: fold_partial_uncurry)
      apply (rule hfref_cons[OF succ_imp_refine[unfolded PR_CONST_def]])
      by auto
      
    definition (in -) "bfsi' N s t psi cfi 
      \<equiv> bfs_impl (\<lambda>(am, cf). succ_imp N am cf) (psi,cfi) s t"

    lemma [sepref_fr_rules]: 
      "(uncurry (bfsi' N s t),uncurry (PR_CONST bfs2_op)) 
        \<in> is_am\<^sup>k *\<^sub>a (asmtx_assn N id_assn)\<^sup>k \<rightarrow>\<^sub>a option_assn is_path"
      unfolding bfsi'_def[abs_def] bfs2_op_def[abs_def] 
      using bfs.bfs_impl_fr_rule unfolding bfs.op_bfs_def[abs_def]
      apply (clarsimp simp: hfref_def all_to_meta)
      apply (rule hn_refine_cons[rotated])
      apply rprems
      apply (sep_auto simp: pure_def intro!: enttI)
      apply (sep_auto simp: pure_def)
      apply (sep_auto simp: pure_def)
      done

    lemma [def_pat_rules]: "Network.bfs2_op$c$s$t \<equiv> UNPROTECT bfs2_op" by simp
    sepref_register "PR_CONST bfs2_op" 
      :: "i_ps \<Rightarrow> capacity_impl i_mtx \<Rightarrow> path option nres"  


    schematic_goal edka_imp_tabulate_impl:
      notes [sepref_opt_simps] = heap_WHILET_def
      fixes am :: "node \<Rightarrow> node list" and cf :: "capacity_impl graph"
      notes [id_rules] = 
        itypeI[Pure.of am "TYPE(node \<Rightarrow> node list)"]
      notes [sepref_import_param] = IdI[of am]
      shows "hn_refine (emp) (?c::?'c Heap) ?\<Gamma> ?R (edka5_tabulate am)"
      unfolding edka5_tabulate_def
      using [[id_debug, goals_limit = 1]]
      by sepref

    concrete_definition (in -) edka_imp_tabulate 
      uses Edka_Impl.edka_imp_tabulate_impl
    prepare_code_thms (in -) edka_imp_tabulate_def

    lemma edka_imp_tabulate_refine[sepref_fr_rules]: 
      "(edka_imp_tabulate c N, PR_CONST edka5_tabulate) 
      \<in> (pure Id)\<^sup>k \<rightarrow>\<^sub>a prod_assn (asmtx_assn N id_assn) is_am"
      apply (rule)
      apply (rule hn_refine_preI)
      apply (clarsimp 
        simp: uncurry_def list_assn_pure_conv hn_ctxt_def 
        split: prod.split)
      apply (rule hn_refine_cons[OF _ edka_imp_tabulate.refine[OF this_loc]])
      apply (sep_auto simp: hn_ctxt_def pure_def)+
      done

    lemma [def_pat_rules]: 
      "Network.edka5_tabulate$c \<equiv> UNPROTECT edka5_tabulate" 
      by simp
    sepref_register "PR_CONST edka5_tabulate"
      :: "(node \<Rightarrow> node list) \<Rightarrow> (capacity_impl i_mtx \<times> i_ps) nres"


    schematic_goal edka_imp_run_impl:
      notes [sepref_opt_simps] = heap_WHILET_def
      fixes am :: "node \<Rightarrow> node list" and cf :: "capacity_impl graph"
      notes [id_rules] = 
        itypeI[Pure.of cf "TYPE(capacity_impl i_mtx)"]
        itypeI[Pure.of am "TYPE(i_ps)"]
      shows "hn_refine 
        (hn_ctxt (asmtx_assn N id_assn) cf cfi * hn_ctxt is_am am psi) 
        (?c::?'c Heap) ?\<Gamma> ?R  
        (edka5_run cf am)"
      unfolding edka5_run_def
      using [[id_debug, goals_limit = 1]]
      by sepref

    concrete_definition (in -) edka_imp_run uses Edka_Impl.edka_imp_run_impl
    prepare_code_thms (in -) edka_imp_run_def

    thm edka_imp_run_def
    lemma edka_imp_run_refine[sepref_fr_rules]: 
      "(uncurry (edka_imp_run s t N), uncurry (PR_CONST edka5_run)) 
        \<in> (asmtx_assn N id_assn)\<^sup>d *\<^sub>a (is_am)\<^sup>k \<rightarrow>\<^sub>a is_rflow N"
      apply rule
      apply (clarsimp 
        simp: uncurry_def list_assn_pure_conv hn_ctxt_def 
        split: prod.split)
      apply (rule hn_refine_cons[OF _ edka_imp_run.refine[OF this_loc] _])
      apply (sep_auto simp: hn_ctxt_def)+
      done

    lemma [def_pat_rules]: 
      "Network.edka5_run$c$s$t \<equiv> UNPROTECT edka5_run" 
      by simp
    sepref_register "PR_CONST edka5_run" 
      :: "capacity_impl i_mtx \<Rightarrow> i_ps \<Rightarrow> i_rflow nres"


    schematic_goal edka_imp_impl:
      notes [sepref_opt_simps] = heap_WHILET_def
      fixes am :: "node \<Rightarrow> node list" and cf :: "capacity_impl graph"
      notes [id_rules] = 
        itypeI[Pure.of am "TYPE(node \<Rightarrow> node list)"]
      notes [sepref_import_param] = IdI[of am]
      shows "hn_refine (emp) (?c::?'c Heap) ?\<Gamma> ?R (edka5 am)"
      unfolding edka5_def
      using [[id_debug, goals_limit = 1]]
      by sepref

    concrete_definition (in -) edka_imp uses Edka_Impl.edka_imp_impl
    prepare_code_thms (in -) edka_imp_def
    lemmas edka_imp_refine = edka_imp.refine[OF this_loc]

    thm pat_rules TrueI def_pat_rules
    

  end

  export_code edka_imp checking SML_imp

  subsection \<open>Correctness Theorem for Implementation\<close>
  text \<open>We combine all refinement steps to derive a correctness 
    theorem for the implementation\<close>
  context Network_Impl begin
    theorem edka_imp_correct: 
      assumes VN: "Graph.V c \<subseteq> {0..<N}"
      assumes ABS_PS: "is_adj_map am"
      shows "
        <emp> 
          edka_imp c s t N am 
        <\<lambda>fi. \<exists>\<^sub>Af. is_rflow N f fi * \<up>(isMaxFlow f)>\<^sub>t"
    proof -
      interpret Edka_Impl by unfold_locales fact

      note edka5_refine[OF ABS_PS]
      also note edka4_refine                 
      also note edka3_refine    
      also note edka2_refine 
      also note edka_refine
      also note edka_partial_refine
      also note fofu_partial_correct
      finally have "edka5 am \<le> SPEC isMaxFlow" .
      from hn_refine_ref[OF this edka_imp_refine]
      show ?thesis 
        by (simp add: hn_refine_def)
    qed
  end    
end
