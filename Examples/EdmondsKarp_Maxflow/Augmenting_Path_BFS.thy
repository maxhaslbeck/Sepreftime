section \<open>Breadth First Search\<close>
theory Augmenting_Path_BFS
imports 
  (* Maxflow_Lib.Refine_Add_Fofu *)
  Graph_Impl
  "../../Refine_Foreach"
  "../../RefineMonadicVCG"
  "../../Refine_Imperative_HOL/IICF/Intf/IICF_Set"
begin




(* TODO: move *)

 







ML {*
structure Refine = struct

  structure vcg = Named_Thms
    ( val name = @{binding refine_vcg}
      val description = "Refinement Framework: " ^ 
        "Verification condition generation rules (intro)" )

  structure vcg_cons = Named_Thms
    ( val name = @{binding refine_vcg_cons}
      val description = "Refinement Framework: " ^
        "Consequence rules tried by VCG" )

  structure refine0 = Named_Thms
    ( val name = @{binding refine0}
      val description = "Refinement Framework: " ^
        "Refinement rules applied first (intro)" )

  structure refine = Named_Thms
    ( val name = @{binding refine}
      val description = "Refinement Framework: Refinement rules (intro)" )

  structure refine2 = Named_Thms
    ( val name = @{binding refine2}
      val description = "Refinement Framework: " ^
        "Refinement rules 2nd stage (intro)" )

  (* If set to true, the product splitter of refine_rcg is disabled. *)
  val no_prod_split = 
    Attrib.setup_config_bool @{binding refine_no_prod_split} (K false);

  fun rcg_tac add_thms ctxt = 
    let 
      val cons_thms = vcg_cons.get ctxt
      val ref_thms = (refine0.get ctxt 
        @ add_thms @ refine.get ctxt @ refine2.get ctxt);
      val prod_ss = (Splitter.add_split @{thm prod.split} 
        (put_simpset HOL_basic_ss ctxt));
      val prod_simp_tac = 
        if Config.get ctxt no_prod_split then 
          K no_tac
        else
          (simp_tac prod_ss THEN' 
            REPEAT_ALL_NEW (resolve_tac ctxt @{thms impI allI}));
    in
      REPEAT_ALL_NEW_FWD (DETERM o FIRST' [
        resolve_tac ctxt ref_thms,
        resolve_tac ctxt cons_thms THEN' resolve_tac ctxt ref_thms,
        prod_simp_tac
      ])
    end;

  fun post_tac ctxt = REPEAT_ALL_NEW_FWD (FIRST' [
    eq_assume_tac,
    (*match_tac ctxt thms,*)
    SOLVED' (Tagged_Solver.solve_tac ctxt)]) 
         

end;
*}
setup {* Refine.vcg.setup *}
setup {* Refine.vcg_cons.setup *}
setup {* Refine.refine0.setup *}
setup {* Refine.refine.setup *}
setup {* Refine.refine2.setup *}
(*setup {* Refine.refine_post.setup *}*)

method_setup refine_rcg = 
  {* Attrib.thms >> (fn add_thms => fn ctxt => SIMPLE_METHOD' (
    Refine.rcg_tac add_thms ctxt THEN_ALL_NEW_FWD (TRY o Refine.post_tac ctxt)
  )) *} 
  "Refinement framework: Generate refinement conditions"

method_setup refine_vcg = 
  {* Attrib.thms >> (fn add_thms => fn ctxt => SIMPLE_METHOD' (
    Refine.rcg_tac (add_thms @ Refine.vcg.get ctxt) ctxt THEN_ALL_NEW_FWD (TRY o Refine.post_tac ctxt)
  )) *} 
  "Refinement framework: Generate refinement and verification conditions"










 

context
  fixes t ::  "('a \<Rightarrow> 'b option) \<Rightarrow> nat"
begin
  definition "mop_map_update m k v = SPECT [ m(k \<mapsto> v) \<mapsto> t m]"


  lemma  mop_map_update: "tt \<le> TTT Q (SPECT [ m(k \<mapsto> v) \<mapsto> t m]) 
        \<Longrightarrow> tt \<le> TTT Q (mop_map_update m k v)" unfolding mop_map_update_def by simp

  sepref_register "mop_map_update" 
  print_theorems 
end


context
  fixes t ::  "('a \<Rightarrow> 'b option) \<Rightarrow> nat"
begin
  definition "mop_map_dom_member m x = SPECT (emb (\<lambda>b. b \<longleftrightarrow> x\<in>dom m) (t m))"


  lemma  mop_map_dom_member: "tt \<le> TTT Q (SPECT (emb (\<lambda>b. b \<longleftrightarrow> x\<in>dom m) (t m))) 
        \<Longrightarrow> tt \<le> TTT Q (mop_map_dom_member m x)" unfolding mop_map_dom_member_def by simp

  sepref_register "mop_map_dom_member" 
  print_theorems 
end

context
  fixes t ::  "('a \<Rightarrow> 'b option) \<Rightarrow> nat"
begin
definition "mop_map_lookup m x = do {
        ASSERT (x\<in>dom m);
        SPECT [  (the (m x)) \<mapsto> t m]
      }"


lemma  mop_map_lookup: "tt \<le> TTT Q (SPECT [  (the (m x)) \<mapsto> t m])
        \<Longrightarrow> x : dom m 
        \<Longrightarrow> tt \<le> TTT Q (mop_map_lookup m x)" unfolding mop_map_lookup_def by simp

  lemma progress_mop_map_lookup[progress_rules]: "t m > 0 \<Longrightarrow> progress (mop_map_lookup m x)"
      unfolding mop_map_lookup_def by (progress\<open>simp add:   zero_enat_def\<close>) 
  sepref_register "mop_map_lookup" 
  print_theorems 
end



context
  fixes t ::  "'c list \<Rightarrow> nat"
begin

  definition "mop_append x xs = SPECT [ (x#xs) \<mapsto> t xs]"

  lemma progress_mop_append[progress_rules]: "t xs > 0 \<Longrightarrow> progress (mop_append x xs)"
      unfolding mop_append_def by (progress\<open>simp add:   zero_enat_def\<close>) 

  lemma mop_append: "tt \<le> TTT Q (SPECT [ (x#xs) \<mapsto> t xs]) \<Longrightarrow> tt
           \<le> TTT Q (mop_append x xs)" unfolding mop_append_def by simp
end



lemma T_conseq6':
  assumes 
    "TTT Q' f \<ge> Some t"
    "\<And>x t'' M. f = SPECT M \<Longrightarrow> M x \<noteq> None \<Longrightarrow>   (Q x) \<ge> Q' x" 
  shows "TTT Q f \<ge> Some t"
  apply(rule T_conseq6) apply fact   
     by (auto dest: assms(2))

   thm whileIET_rule[THEN T_conseq6']




  text \<open>
    In this theory, we present a verified breadth-first search
    with an efficient imperative implementation.
    It is parametric in the successor function.
    \<close>

  subsection \<open>Algorithm\<close>
  locale pre_bfs_invar = Graph +    
    fixes src dst :: node
  begin  

    abbreviation "ndist v \<equiv> min_dist src v"

    definition Vd :: "nat \<Rightarrow> node set"
    where
      "\<And>d. Vd d \<equiv> {v. connected src v \<and> ndist v = d}"

    lemma Vd_disj: "\<And>d d'. d\<noteq>d' \<Longrightarrow> Vd d \<inter> Vd d' = {}"  
      by (auto simp: Vd_def)

    lemma src_Vd0[simp]: "Vd 0 = {src}"  
      by (auto simp: Vd_def)

    lemma in_Vd_conv: "v\<in>Vd d \<longleftrightarrow> connected src v \<and> ndist v = d"
      by (auto simp: Vd_def)

    lemma Vd_succ: 
      assumes "u\<in>Vd d"  
      assumes "(u,v)\<in>E"
      assumes "\<forall>i\<le>d. v\<notin>Vd i"
      shows "v\<in>Vd (Suc d)"
      using assms
      by (metis connected_append_edge in_Vd_conv le_SucE min_dist_succ)

  end

  locale valid_PRED = pre_bfs_invar +
    fixes PRED :: "node \<rightharpoonup> node"
    assumes SRC_IN_V[simp]: "src\<in>V"
    assumes FIN_V[simp, intro!]: "finite V"
    assumes PRED_src[simp]: "PRED src = Some src"
    assumes PRED_dist: "\<lbrakk>v\<noteq>src; PRED v = Some u\<rbrakk> \<Longrightarrow> ndist v = Suc (ndist u)"
    assumes PRED_E: "\<lbrakk>v\<noteq>src; PRED v = Some u\<rbrakk> \<Longrightarrow> (u,v)\<in>E"
    assumes PRED_closed: "\<lbrakk> PRED v = Some u \<rbrakk> \<Longrightarrow> u\<in>dom PRED"
  begin
    lemma FIN_E[simp, intro!]: "finite E" using E_ss_VxV by simp
    lemma FIN_succ[simp, intro!]: "finite (E``{u})" 
      by (auto intro: finite_Image)
  end  
    
  locale nf_invar' = valid_PRED c src dst PRED for c src dst 
    and PRED :: "node \<rightharpoonup> node"
    and C N :: "node set"
    and d :: nat 
    +
    assumes VIS_eq: "dom PRED = N \<union> {u. \<exists>i\<le>d. u\<in>Vd i}"
    assumes C_ss: "C \<subseteq> Vd d"
    assumes N_eq: "N = Vd (d+1) \<inter> E``(Vd d - C)"
      
    assumes dst_ne_VIS: "dst \<notin> dom PRED"

  locale nf_invar = nf_invar' +   
    assumes empty_assm: "C={} \<Longrightarrow> N={}"

  locale f_invar = valid_PRED c src dst PRED for c src dst 
    and PRED :: "node \<rightharpoonup> node"
    and d :: nat   
    + 
    assumes dst_found: "dst \<in> dom PRED \<inter> Vd d"

  context Graph begin

    abbreviation "outer_loop_invar src dst \<equiv> \<lambda>(f,PRED,C,N,d). 
      (f \<longrightarrow> f_invar c src dst PRED d) \<and>
      (\<not>f \<longrightarrow> nf_invar c src dst PRED C N d)

      "
    abbreviation "assn1 src dst \<equiv> \<lambda>(f,PRED,C,N,d). 
      \<not>f \<and> nf_invar' c src dst PRED C N d"

end

locale Pre_BFS_Impl = Graph + 
  fixes  set_insert_time map_dom_member_time set_delete_time :: nat
    and   get_succs_list_time :: nat and  map_update_time set_pick_time set_empty_time  :: nat
  assumes [simp]: "set_pick_time > 0"
begin 
 

  definition add_succs_spec_time :: "nat \<Rightarrow> nat"  where  "add_succs_spec_time cs = (cs * (map_dom_member_time + (max (set_insert_time + map_update_time) 1)))"
  
  lemma add_succs_spec_time_mono: "n \<le> m \<Longrightarrow> add_succs_spec_time n \<le> add_succs_spec_time m"
    unfolding add_succs_spec_time_def by simp

  definition "add_succs_spec dst succ v PRED N \<equiv> ASSERT (N \<subseteq> dom PRED) \<then> 
    SPECT (emb (\<lambda>(f,PRED',N').
      case f of
        False \<Rightarrow> dst \<notin> succ - dom PRED 
          \<and> PRED' = map_mmupd PRED (succ - dom PRED) v 
          \<and> N' = N \<union> (succ - dom PRED)
      | True \<Rightarrow> dst \<in> succ - dom PRED 
        \<and> PRED \<subseteq>\<^sub>m PRED' 
        \<and> PRED' \<subseteq>\<^sub>m map_mmupd PRED (succ - dom PRED) v 
        \<and> dst\<in>dom PRED'
  ) (add_succs_spec_time (card succ))) "



  definition (in Graph) "max_dist src \<equiv> Max (min_dist src`V)"

  lemma max_dist_ub: "src\<in>V \<Longrightarrow> max_dist src \<le> card V" sorry

  definition body_time :: "nat \<Rightarrow> nat" where
    "body_time cV = set_pick_time + set_delete_time + set_empty_time
               + get_succs_list_time + add_succs_spec_time cV"

  definition Te :: "node \<Rightarrow> bool \<times> (nat \<Rightarrow> nat option) \<times> nat set \<times> nat set \<times> nat
   \<Rightarrow> nat" where "Te src = (\<lambda>(f,PRED,C,N,d). if f then 0
         else (card V * (max_dist src + 1 - d) + card C) * (body_time (card V)) )"



  definition pre_bfs :: "node \<Rightarrow> node \<Rightarrow> (nat \<times> (node\<rightharpoonup>node)) option nrest"
    where "pre_bfs src dst \<equiv> do {
    (f,PRED,_,_,d) \<leftarrow> whileIET (outer_loop_invar src dst) (Te src)
      (\<lambda>(f,PRED,C,N,d). f=False \<and> C\<noteq>{})
      (\<lambda>(f,PRED,C,N,d). do {
        v \<leftarrow> mop_set_pick (\<lambda>_. set_pick_time) C;
        C \<leftarrow> mop_set_del (\<lambda>_. set_delete_time) C v;
        ASSERT (v\<in>V);
        succ \<leftarrow> SPECT (emb (\<lambda>l. distinct l \<and> set l = E``{v}) (enat get_succs_list_time)); 
        ASSERT (distinct succ);
        (f,PRED,N) \<leftarrow> add_succs_spec dst (set succ) v PRED N;
        if f then
          RETURNT (f,PRED,C,N,d+1)
        else do {
          ASSERT (assn1 src dst (f,PRED,C,N,d));
          if (C={}) then do {
            C \<leftarrow> RETURNT N; 
            N \<leftarrow> mop_set_empty (set_empty_time);
            d \<leftarrow> RETURNT (d+1);
            RETURNT (f,PRED,C,N,d)
          } else RETURNT (f,PRED,C,N,d)
        }  
      })
      (False,[src\<mapsto>src],{src},{},0::nat);
    if f then RETURNT (Some (d, PRED)) else RETURNT None
    }"

  subsection "Correctness Proof"

  lemma (in nf_invar') ndist_C[simp]: "\<lbrakk>v\<in>C\<rbrakk> \<Longrightarrow> ndist v = d"  
    using C_ss by (auto simp: Vd_def)
  lemma (in nf_invar) CVdI: "\<lbrakk>u\<in>C\<rbrakk> \<Longrightarrow> u\<in>Vd d"
    using C_ss by (auto)

  lemma (in nf_invar) inPREDD: 
    "\<lbrakk>PRED v = Some u\<rbrakk> \<Longrightarrow> v\<in>N \<or> (\<exists>i\<le>d. v\<in>Vd i)"   
    using VIS_eq by (auto)

  lemma (in nf_invar') C_ss_VIS: "\<lbrakk>v\<in>C\<rbrakk> \<Longrightarrow> v\<in>dom PRED"
    using C_ss VIS_eq by blast  

  lemma (in nf_invar) invar_succ_step:
    assumes "v\<in>C"
    assumes "dst \<notin> E``{v} - dom PRED"
    shows "nf_invar' c src dst 
      (map_mmupd PRED (E``{v} - dom PRED) v) 
      (C-{v}) 
      (N \<union> (E``{v} - dom PRED)) 
      d"
  proof -
    from C_ss_VIS[OF \<open>v\<in>C\<close>] dst_ne_VIS have "v\<noteq>dst" by auto

    show ?thesis  
      using \<open>v\<in>C\<close> \<open>v\<noteq>dst\<close>
      apply unfold_locales
      apply simp
      apply simp
      apply (auto simp: map_mmupd_def) []
  
      apply (erule map_mmupdE)
      using PRED_dist apply blast
      apply (unfold VIS_eq) []
      apply clarify
      apply (metis CVdI Vd_succ in_Vd_conv)
  
      using PRED_E apply (auto elim!: map_mmupdE) []   
      using PRED_closed apply (auto elim!: map_mmupdE dest: C_ss_VIS) [] 
  
      using VIS_eq apply auto []
      using C_ss apply auto []
  
      apply (unfold N_eq) []
      apply (frule CVdI)
      apply (auto) []
      apply (erule (1) Vd_succ)
      using VIS_eq apply (auto) []
      apply (auto dest!: inPREDD simp: N_eq in_Vd_conv) []
  
      using dst_ne_VIS assms(2) apply auto []
      done
  qed  

  lemma invar_init: "\<lbrakk>src\<noteq>dst; src\<in>V; finite V\<rbrakk> 
    \<Longrightarrow> nf_invar c src dst [src \<mapsto> src] {src} {} 0"            
    apply unfold_locales
    apply (auto)
    apply (auto simp: pre_bfs_invar.Vd_def split: if_split_asm)
    done

  lemma (in nf_invar) invar_exit:
    assumes "dst\<in>C"
    shows "f_invar c src dst PRED d"  
    apply unfold_locales
    using assms VIS_eq C_ss by auto

  lemma (in nf_invar) invar_C_ss_V: "u\<in>C \<Longrightarrow> u\<in>V"  
    apply (drule CVdI)
    apply (auto simp: in_Vd_conv connected_inV_iff)
    done

  lemma (in nf_invar) invar_N_ss_Vis: "u\<in>N \<Longrightarrow> \<exists>v. PRED u = Some v"
    using VIS_eq by auto  
    
  lemma (in pre_bfs_invar) Vdsucinter_conv[simp]: 
    "Vd (Suc d) \<inter> E `` Vd d = Vd (Suc d)"
    apply (auto)
    by (metis Image_iff in_Vd_conv min_dist_suc)  

  lemma (in nf_invar') invar_shift:
    assumes [simp]: "C={}"
    shows "nf_invar c src dst PRED N {} (Suc d)"  
    apply unfold_locales
    using VIS_eq N_eq[simplified] apply (auto simp add: le_Suc_eq) []
    using N_eq apply auto []
    using N_eq[simplified] apply auto []
    using dst_ne_VIS apply auto []
    apply simp
    done    

  lemma (in nf_invar') invar_restore:
    assumes [simp]: "C\<noteq>{}"
    shows "nf_invar c src dst PRED C N d"
    apply unfold_locales by auto

  definition (in Graph) "bfs_spec src dst r \<equiv> (
    case r of None \<Rightarrow> \<not> connected src dst
            | Some (d,PRED) \<Rightarrow> connected src dst 
                \<and> min_dist src dst = d 
                \<and> valid_PRED c src PRED 
                \<and> dst\<in>dom PRED)"

  lemma (in f_invar) invar_found:
    shows "bfs_spec src dst (Some (d,PRED))"
    unfolding bfs_spec_def
    apply simp
    using dst_found 
    apply (auto simp: in_Vd_conv)
    by unfold_locales

  lemma (in nf_invar) invar_not_found:
    assumes [simp]: "C={}"
    shows "bfs_spec src dst None"
    unfolding bfs_spec_def
    apply simp
  proof (rule notI)
    have [simp]: "N={}" using empty_assm by simp

    assume C: "connected src dst"
    then obtain d' where dstd': "dst \<in> Vd d'"
      by (auto simp: in_Vd_conv)

    txt {* We make a case-distinction whether @{text "d'\<le>d"}: *}
    have "d'\<le>d \<or> Suc d \<le> d'" by auto  
    moreover {
      assume "d'\<le>d"
      with VIS_eq dstd' have "dst \<in> dom PRED" by auto
      with dst_ne_VIS have False by auto
    } moreover {
      assume "Suc d \<le> d'"
      txt {* In the case @{text "d+1 \<le> d'"}, we also obtain a node
        that has a shortest path of length @{text "d+1"}: *}
      with min_dist_le[OF C] dstd' obtain v' where "v' \<in> Vd (Suc d)"
        by (auto simp: in_Vd_conv)
      txt {* However, the invariant states that such nodes are either in
        @{text "N"} or are successors of @{text "C"}. As @{text "N"} 
        and @{text "C"} are both empty, we again get a contradiction. *}
      with N_eq have False by auto  
    } ultimately show False by blast
  qed

  lemma (in Graph) map_le_mp: "\<lbrakk>m\<subseteq>\<^sub>mm'; m k = Some v\<rbrakk> \<Longrightarrow> m' k = Some v"
    by (force simp: map_le_def)

  lemma (in nf_invar) dst_notin_Vdd[intro, simp]: "i\<le>d \<Longrightarrow> dst\<notin>Vd i"
    using VIS_eq dst_ne_VIS by auto 

  lemma (in nf_invar) invar_exit':
    assumes "u\<in>C" "(u,dst) \<in> E" "dst \<in> dom PRED'"
    assumes SS1: "PRED \<subseteq>\<^sub>m PRED'" 
      and SS2: "PRED' \<subseteq>\<^sub>m map_mmupd PRED (E``{u} - dom PRED) u"
    shows "f_invar c src dst PRED' (Suc d)"
    apply unfold_locales
    apply simp_all

    using map_le_mp[OF SS1 PRED_src] apply simp

    apply (drule map_le_mp[OF SS2])
    apply (erule map_mmupdE)
    using PRED_dist apply auto []
    apply (unfold VIS_eq) []
    apply clarify
    using \<open>u\<in>C\<close>
    apply (metis CVdI Vd_succ in_Vd_conv)

    apply (drule map_le_mp[OF SS2])
    using PRED_E apply (auto elim!: map_mmupdE) []   
    
    apply (drule map_le_mp[OF SS2])
    apply (erule map_mmupdE)
    using map_le_implies_dom_le[OF SS1]
    using PRED_closed apply (blast) []
    using C_ss_VIS[OF \<open>u\<in>C\<close>] map_le_implies_dom_le[OF SS1] apply blast
    using \<open>dst \<in> dom PRED'\<close> apply simp

    using \<open>u\<in>C\<close> CVdI[OF \<open>u\<in>C\<close>] \<open>(u,dst)\<in>E\<close>
    apply (auto) []
    apply (erule (1) Vd_succ)
    using VIS_eq apply (auto) []
    done




  definition "outer_loop_rel src \<equiv> 
    inv_image (
        less_than_bool 
        <*lex*> greater_bounded (max_dist src + 1) 
        <*lex*> finite_psubset) 
      (\<lambda>(f,PRED,C,N,d). (\<not>f,d,C))"
  lemma outer_loop_rel_wf: 
    assumes "finite V"
    shows "wf (outer_loop_rel src)"
    using assms
    unfolding outer_loop_rel_def
    by auto

  lemma (in nf_invar) C_ne_max_dist:
    assumes "C\<noteq>{}"
    shows "d \<le> max_dist src"
  proof -
    from assms obtain u where "u\<in>C" by auto
    with C_ss have "u\<in>Vd d" by auto
    hence "min_dist src u = d" "u\<in>V" 
      by (auto simp: in_Vd_conv connected_inV_iff)
    thus "d\<le>max_dist src" 
      unfolding max_dist_def by auto
  qed    

  lemma (in nf_invar) Vd_ss_V: "Vd d \<subseteq> V"
    by (auto simp: Vd_def connected_inV_iff)

  lemma (in nf_invar) finite_C[simp, intro!]: "finite C"
    using C_ss FIN_V Vd_ss_V by (blast intro: finite_subset)
  
  lemma (in nf_invar) finite_succ: "finite (E``{u})"  
    by auto


  thm outer_loop_rel_wf


  definition pre_bfs_time'   where
    "pre_bfs_time' src = (1 + card V + card V * max_dist src) * body_time (card V)"
  definition pre_bfs_time  where
    "pre_bfs_time cV = (1 + cV + cV * cV) * body_time cV"

lemma body_time_progress: "body_time cV > 0" unfolding body_time_def by simp
lemma pre_bfs_time_progress: "pre_bfs_time cV > 0" using body_time_progress pre_bfs_time_def by simp

lemma Te_start_ub: "src \<in> V \<Longrightarrow> (Te src (False, [src \<mapsto> src], {src}, {}, 0)) \<le> pre_bfs_time (card V)"
  apply (auto simp add: Te_def pre_bfs_time_def) apply(rule max_dist_ub) by simp

lemma Te_start_ub': "(Te src (False, [src \<mapsto> src], {src}, {}, 0)) \<le> pre_bfs_time' src"
  by (simp add: Te_def pre_bfs_time'_def)
     
      (* (f,PRED,C,N,d) *)
  
  lemma TeTF_[simp]: "(Te src (True, a1, b1, c1, d1) \<le>  Te src (False, x, y, z, f)) \<longleftrightarrow> True"
      unfolding Te_def by simp 



lemma hlp: "\<And>a b c::enat. a \<le> c \<Longrightarrow> enat ((a::nat)-b) \<le> c"
 using diff_le_self dual_order.trans enat_ord_simps(1) by blast

lemma hlp_nat: "\<And>a b c::nat. a \<le> c \<Longrightarrow> ((a)-b) \<le> c"
 using diff_le_self dual_order.trans enat_ord_simps(1) by blast

 

lemma (in nf_invar) cardC: "card C \<le> card V"
  by(auto simp: invar_C_ss_V intro!: card_mono)  

lemma (in nf_invar) cardN'_: "x\<in>C \<Longrightarrow> (N \<union> (E `` {x} - dom PRED)) \<subseteq>  V"
  by (smt Diff_iff Graph.connected_inV_iff Graph.succ_ss_V Int_iff N_eq SRC_IN_V UnE mem_Collect_eq pre_bfs_invar.Vd_def subsetCE subsetI)
 

lemma (in nf_invar) cardN':  "x\<in>C \<Longrightarrow> card (N \<union> (E `` {x} - dom PRED)) \<le> card V"
  apply(rule card_mono[OF FIN_V cardN'_]) by simp 



lemma   Te_decr_succ_step: "nf_invar c src dst PRED C N d \<Longrightarrow>   
    x \<in> C \<Longrightarrow>   
    Te src(False, map_mmupd PRED (E `` {x} - dom PRED) x, N \<union> (E `` {x} - dom PRED), {}, Suc d)
    \<le> Te src (False, PRED, C, N, d)"  apply(frule nf_invar.cardN')
  by(auto dest!:  nf_invar.C_ne_max_dist simp: Te_def Suc_diff_le)

lemma [simp]: "nf_invar c src dst PRED C N d \<Longrightarrow> finite V"
  using nf_invar'_def nf_invar.axioms(1) valid_PRED.FIN_V by blast  

lemma  add_succs_spec_ub: "finite V \<Longrightarrow> set_pick_time + set_delete_time + get_succs_list_time + add_succs_spec_time (card (E `` {x})) + set_empty_time
        \<le> body_time (card V)"
  apply (simp add: body_time_def) apply(rule add_succs_spec_time_mono)  
  apply(rule card_mono) by (auto simp add: succ_ss_V)  
lemma hl: "x \<in> C \<Longrightarrow> C \<noteq> {}" by auto
lemma   Te_pays_succ_step: "nf_invar c src dst PRED C N d \<Longrightarrow> 
    x \<in> C \<Longrightarrow>   
    set_pick_time + set_delete_time + get_succs_list_time + add_succs_spec_time (card (E `` {x}))  + set_empty_time
    \<le> Te src (False, PRED, C, N, d) -
       Te src
        (False, map_mmupd PRED (E `` {x} - dom PRED) x, N \<union> (E `` {x} - dom PRED), {}, Suc d)"
  unfolding Te_def apply simp 
  apply(frule  hl)
  apply(frule  nf_invar.C_ne_max_dist) apply simp 
  apply(simp add: Suc_diff_le) 
  apply(frule nf_invar.cardN') apply simp apply(subst diff_mult_distrib[symmetric]) 
  apply(rule dual_order.trans[OF _ add_succs_spec_ub]) 
proof (goal_cases)
  case 1
  then have "card C > 0" 
    using nf_invar.finite_C card_gt_0_iff by fastforce
  with 1  have "1 \<le> (card V + card C - card (N \<union> (E `` {x} - dom PRED)))"
    by auto
  then show ?case by auto 
qed simp

lemma Te_decr_level_step: "nf_invar c src dst PRED C N d \<Longrightarrow> C \<noteq> {} \<Longrightarrow> 
    x \<in> C \<Longrightarrow>   
    Te src
           (False, map_mmupd PRED (E `` {x} - dom PRED) x, C - {x},
            N \<union> (E `` {x} - dom PRED), d)
    \<le> Te src (False, PRED, C, N, d)" apply(frule nf_invar.cardN') 
  apply (auto dest!:  nf_invar.C_ne_max_dist simp: Te_def Suc_diff_le)  
  by (metis card_Diff1_le card_infinite finite.emptyI finite_Diff2 finite_insert less_or_eq_imp_le)  

lemma  Te_pays_level_step: "nf_invar c src dst PRED C N d \<Longrightarrow>  
    C \<noteq> {} \<Longrightarrow> 
    x \<in> C \<Longrightarrow> 
    set_pick_time + set_delete_time + get_succs_list_time + add_succs_spec_time (card (E `` {x}))  
       \<le> Te src (False, PRED, C, N, d) -
          Te src
           (False, map_mmupd PRED (E `` {x} - dom PRED) x, C - {x},
            N \<union> (E `` {x} - dom PRED), d)"
  apply(rule dual_order.trans[OF _ _]) 
  apply(rule dual_order.trans[OF _ add_succs_spec_ub[where x=x]]) 
  unfolding Te_def apply simp unfolding body_time_def[symmetric]
  apply (auto simp add: card_minus1 diff_mult_distrib[symmetric] )
  apply (metis Suc_leI card_0_eq diff_diff_cancel empty_iff less_or_eq_imp_le neq0_conv nf_invar.finite_C)
  done


lemma (in nf_invar) Cge1: "x \<in> C \<Longrightarrow> card C \<ge> 1"  
  using card_0_eq finite_C by force  

lemma   Te_pays_exit: "nf_invar c src dst PRED C N d \<Longrightarrow>   x \<in> C \<Longrightarrow> 
     set_pick_time + set_delete_time + get_succs_list_time + add_succs_spec_time (card (E `` {x}))
       \<le> Te src (False, PRED, C, N, d) - Te src (True, PRED', C - {x}, N', Suc d)"
  apply(rule dual_order.trans[OF _ _]) 
  apply(rule dual_order.trans[OF _ add_succs_spec_ub[where x=x]]) 
  unfolding Te_def body_time_def[symmetric]  using nf_invar.Cge1
  apply force apply simp by simp

ML \<open>map_filter \<close>

theorem pre_bfs_correct':
    assumes [simp]: "src\<in>V" "src\<noteq>dst"       
    assumes [simp]: "finite V"
    shows "pre_bfs src dst \<le> SPECT (emb (bfs_spec src dst) (pre_bfs_time (card V)))"
unfolding pre_bfs_def add_succs_spec_def 
proof (casified_VCG rules: mop_set_pick_def mop_set_del_def  mop_set_empty_def) 
  case while {
    case progress then show ?case by(progress\<open>simp\<close>)
    case precondition then show ?case by (auto simp: invar_init)
    case invariant {
      case ASSERT   then show ?case by (auto simp: nf_invar.invar_C_ss_V)
      case ASSERTa  then show ?case by simp
      case ASSERTb  then show ?case by (auto  simp: nf_invar.invar_N_ss_Vis)  
      case cond {
        case the {
          case time then show ?case by(auto simp: Te_pays_exit)
          case func then show ?case by(auto simp: nf_invar.invar_exit') 
        }
      next
        case els {
          case ASSERT then show ?case by (simp add: nf_invar.invar_succ_step )
          case cond {
            case the {
              case time then show ?case by (auto intro: Te_decr_succ_step  Te_pays_succ_step)
              case func then show ?case by (auto intro!:  nf_invar'.invar_shift  nf_invar.invar_succ_step)
            }
          next
            case els {
              case time then show ?case by (auto intro: Te_decr_level_step  Te_pays_level_step)
              case func then show ?case by (auto intro: nf_invar'.invar_restore nf_invar.invar_succ_step )
            }
          }
        }
      }
    }
  } 
  case postcondition {
    case cond {
      case the {
        case func then show ?case by(auto simp:  f_invar.invar_found)
        case time then show ?case by(auto simp: hlp_nat  Te_start_ub)  
      next
        case els {
          case func then show ?case by(auto simp:  nf_invar.invar_not_found)
          case time then show ?case by(auto simp: hlp_nat  Te_start_ub)  
        }
      }
    }
  }
qed


theorem pre_bfs_correct:
    assumes [simp]: "src\<in>V" "src\<noteq>dst"       
    assumes [simp]: "finite V"
    shows "pre_bfs src dst \<le> SPECT (emb (bfs_spec src dst) (pre_bfs_time (card V)))"
    unfolding pre_bfs_def add_succs_spec_def
    apply(rule T_specifies_I) 

    apply(vcg' \<open>clarsimp\<close> rules: mop_set_pick mop_set_del  mop_set_empty)

    apply (simp_all split: bool.splits add: Some_le_mm3_Some_conv Some_le_emb'_conv)
    apply safe 

      apply ( vc_solve  simp:  domI 
            Te_pays_exit
            Te_decr_succ_step
            Te_pays_succ_step
            Te_decr_level_step
            Te_pays_level_step

            invar_init

            nf_invar.invar_C_ss_V 
            nf_invar.invar_succ_step 
              nf_invar.invar_exit'     
            nf_invar'.invar_shift
            nf_invar'.invar_restore        
            nf_invar.finite_succ
            nf_invar.invar_N_ss_Vis)  
    subgoal by (auto intro:   nf_invar'.invar_shift  nf_invar.invar_succ_step )  
    subgoal by (auto intro:   nf_invar'.invar_shift  nf_invar.invar_succ_step )  
    subgoal by (auto intro:   nf_invar'.invar_restore   nf_invar.invar_succ_step )  
    subgoal by(auto intro: Te_decr_level_step)  
    subgoal by (auto intro: Te_pays_level_step)
    subgoal by (auto intro:   nf_invar'.invar_restore   nf_invar.invar_succ_step )  
    subgoal by(auto intro: Te_decr_level_step) 
    subgoal by (auto intro: Te_pays_level_step)   
    subgoal by(auto simp:  f_invar.invar_found)
    subgoal by(auto simp: hlp_nat  Te_start_ub)  
    subgoal by(auto simp:  nf_invar.invar_not_found)
    subgoal by(auto simp: hlp_nat  Te_start_ub)  
    done 


  (* Presentation for Paper  
  definition bfs_core :: "node \<Rightarrow> node \<Rightarrow> (nat \<times> (node\<rightharpoonup>node)) option nres"
    where "bfs_core src dst \<equiv> do {
    (f,P,_,_,d) \<leftarrow> while\<^sub>T (\<lambda>(f,P,C,N,d). f=False \<and> C\<noteq>{})
      (\<lambda>(f,P,C,N,d). do {
        v \<leftarrow> spec v. v\<in>C; let C = C-{v};
        let succ = (E``{v});
        (f,P,N) \<leftarrow> add_succs_spec dst succ v P N;
        if f then
          return (f,P,C,N,d+1)
        else do {
          if (C={}) then do {
            let C=N; let N={}; let d=d+1;
            return (f,P,C,N,d)
          } else return (f,P,C,N,d)
        }  
      })
      (False,[src\<mapsto>src],{src},{},0::nat);
    if f then return (Some (d, P)) else return None
    }"

  theorem 
    assumes "src\<in>V" "src\<noteq>dst" "finite V"
    shows "bfs_core src dst \<le> (spec p. bfs_spec src dst p)"
    apply (rule order_trans[OF _ pre_bfs_correct])
    apply (rule refine_IdD)
    unfolding bfs_core_def pre_bfs_def
    apply refine_rcg
    apply refine_dref_type
    apply (vc_solve simp: assms)
    done
    *)

end
thm  Pre_BFS_Impl.pre_bfs_correct

locale valid_PRED_impl = valid_PRED +
  fixes list_append_time map_lookup_time :: nat assumes [simp]: "map_lookup_time > 0"

context Graph
begin

      
  subsection \<open>Extraction of Result Path\<close>

    definition "extract_rpath_inv src dst PRED = (\<lambda>(v,p). 
          v\<in>dom PRED 
        \<and> isPath v p dst
        \<and> distinct (pathVertices v p)
        \<and> (\<forall>v'\<in>set (pathVertices v p). 
            pre_bfs_invar.ndist c src v \<le> pre_bfs_invar.ndist c src v')
        \<and> pre_bfs_invar.ndist c src v + length p 
          = pre_bfs_invar.ndist c src dst)"
 


    definition (in valid_PRED_impl) "extract_rpath_time' = ndist dst * (map_lookup_time + list_append_time)"
    definition (in valid_PRED_impl) "extract_rpath_time cV = cV * (map_lookup_time + list_append_time)"

lemma (in valid_PRED) ndist_le_V:  assumes [simp]: "finite V" and conn: "connected src dst"
  shows "ndist dst \<le> card V"
proof -
  from conn obtain p where isP: "isPath src p dst" and dist: "distinct (pathVertices src p)"
    unfolding connected_def  apply auto apply(frule isSPath_pathLE) unfolding isSimplePath_def  by blast

  have "ndist dst \<le> length p"
    unfolding min_dist_def  dist_def apply(rule Least_le) apply(rule exI[where x=p])
    using isP by simp
  also have "\<dots> \<le> length (pathVertices src p)" by(simp add: length_pathVertices_eq)
  also from dist have "\<dots> = card (set (pathVertices src p))"
    by(simp add: distinct_card) 
  also have "\<dots> \<le> card V"
    apply(rule card_mono) apply simp
    using  pathVertices_edgeset[OF _ isP] by auto

  finally  
  show "ndist dst \<le> card V" .
  qed

    definition (in valid_PRED_impl) "Ter  = (\<lambda>(d,_). ndist d * (map_lookup_time + list_append_time))"


    

    term valid_PRED_impl.Ter 
    definition (in valid_PRED_impl) "extract_rpath  \<equiv> do {
      (_,p) \<leftarrow> whileIET (extract_rpath_inv src dst PRED) (Ter)         
        (\<lambda>(v,p). v\<noteq>src) (\<lambda>(v,p). do {
        ASSERT (v\<in>dom PRED);
        u \<leftarrow> mop_map_lookup (\<lambda>_. map_lookup_time) PRED v;
        p \<leftarrow> mop_append (\<lambda>_. list_append_time) (u,v) p;
        v \<leftarrow> RETURNT u;
        RETURNT (v,p)
      }) (dst,[]);
      RETURNT p
    }"

  end  

  context valid_PRED_impl begin
  
    lemma extract_rpath_correct':
      assumes "dst\<in>dom PRED"
      shows "extract_rpath  
        \<le> SPECT (emb (\<lambda>p. isSimplePath src p dst \<and> length p = ndist dst) extract_rpath_time')"
      using assms unfolding extract_rpath_def isSimplePath_def  
      apply simp
      apply(rule T_specifies_I) 
      apply (vcg'\<open>-\<close> rules: mop_map_lookup mop_append)   

      by (auto simp: Some_le_mm3_Some_conv Some_le_emb'_conv
                          extract_rpath_time'_def extract_rpath_inv_def
                               PRED_closed[THEN domD] PRED_E PRED_dist Ter_def)


    lemma extract_rpath_correct:
      assumes "dst\<in>dom PRED"
      shows "extract_rpath 
        \<le> SPECT (emb (\<lambda>p. isSimplePath src p dst \<and> length p = ndist dst) (extract_rpath_time (card V)))"
      apply(rule dual_order.trans[OF _ extract_rpath_correct'])
      apply (auto simp add: emb_le_emb extract_rpath_time_def extract_rpath_time'_def intro!: ndist_le_V)
        using assms  apply auto  
        using Graph.isPath_rtc Graph.isSimplePath_def connected_edgeRtc by blast 
  end

locale Augmenting_Path_BFS = Graph + 
  fixes  set_insert_time map_dom_member_time set_delete_time get_succs_list_time map_update_time set_pick_time :: nat
    and list_append_time map_lookup_time set_empty_time :: nat
  assumes [simp]: "map_lookup_time > 0"
  assumes [simp]: "set_pick_time > 0"
begin 

interpretation pre: Pre_BFS_Impl c set_insert_time map_dom_member_time set_delete_time
    get_succs_list_time map_update_time set_pick_time set_empty_time
  apply standard by simp 


  term Pre_BFS_Impl.pre_bfs
  term valid_PRED_impl.extract_rpath
  
    definition "bfs src dst \<equiv> do {
      if src=dst then RETURNT (Some [])
      else do {
        br \<leftarrow> pre.pre_bfs src dst;
        case br of
          None \<Rightarrow> RETURNT None
        | Some (d,PRED) \<Rightarrow> do {
            p \<leftarrow> valid_PRED_impl.extract_rpath c src dst PRED list_append_time map_lookup_time;
            RETURNT (Some p)
          }  
      }    
    }"  thm pre.pre_bfs_correct

    definition bfs_time   where "bfs_time src dst = pre.pre_bfs_time (card V)   + valid_PRED_impl.extract_rpath_time list_append_time map_lookup_time (card V)"

    lemma bfs_correct:
      assumes "src\<in>V" "finite V" 
      shows "bfs src dst 
        \<le> SPECT (emb (\<lambda>
          None \<Rightarrow> \<not>connected src dst 
        | Some p \<Rightarrow> isShortestPath src p dst) (bfs_time src dst))"
      unfolding bfs_def
      apply(rule T_specifies_I) 
      apply(vcg'\<open>simp\<close> rules: pre.pre_bfs_correct[THEN T_specifies_rev , THEN T_conseq4]
                    valid_PRED_impl.extract_rpath_correct[THEN T_specifies_rev, THEN T_conseq4])
      by (auto simp add: Some_le_mm3_Some_conv Some_le_emb'_conv Some_eq_emb'_conv
              assms bfs_time_def
              isShortestPath_min_dist_def   valid_PRED_impl_def valid_PRED_impl_axioms_def
              bfs_spec_def isSimplePath_def)
 

          
  end

  (* Snippet for paper 
  context Finite_Graph begin
    interpretation Refine_Monadic_Syntax .
    theorem
      assumes "src\<in>V" 
      shows "bfs src dst \<le> (spec p. case p of 
          None \<Rightarrow> \<not>connected src dst 
        | Some p \<Rightarrow> isShortestPath src p dst)"
      unfolding bfs_def
      apply (refine_vcg
        pre_bfs_correct[THEN order_trans]
        valid_PRED.extract_rpath_correct[THEN order_trans]
        )
      using assms
      apply (vc_solve 
        simp: bfs_spec_def isShortestPath_min_dist_def isSimplePath_def)
      done      

  end   *) 

  subsection \<open>Inserting inner Loop and Successor Function\<close>
  context Pre_BFS_Impl begin
                

  definition "foreach_body_time = set_insert_time + 10"

  term "(\<lambda>it (f,PRED',N'). 
        PRED' = map_mmupd PRED ((succ - it) - dom PRED) u 
      \<and> N' = N \<union> ((succ - it) - dom PRED)
      \<and> f = (dst\<in>(succ - it) - dom PRED)
    )"


  definition "inner_loop dst succ u PRED N \<equiv> nfoldliIE  
    (\<lambda>ti it (f,PRED',N'). 
        PRED' = map_mmupd PRED ((set ti) - dom PRED) u 
      \<and> N' = N \<union> ((set ti) - dom PRED)
      \<and> f = (dst\<in>(set ti) - dom PRED)
    )  (map_dom_member_time+(max (set_insert_time+map_update_time) (1::nat)))
    (succ)
    (\<lambda>(f,PRED,N). \<not>f)
    (\<lambda>v (f,PRED,N). do {
      b \<leftarrow> mop_map_dom_member (%_. map_dom_member_time) PRED v;
      if b then SPECT [ (f,PRED,N) \<mapsto> 1]
      else do {
        PRED \<leftarrow> mop_map_update (\<lambda>_. map_update_time) PRED v u;
        ASSERT (v\<notin>N);
        N \<leftarrow> mop_set_insert (%_. set_insert_time) v N;
        RETURNT (v=dst,PRED,N)
      }
    }) 
    (False,PRED,N)"


  lemma inner_loop_refine: 
    (*assumes NSS: "N \<subseteq> dom PRED"*) 
    assumes [simplified, simp]: 
      "(dsti,dst)\<in>Id" "(succi,succ)\<in>Id" "(ui,u)\<in>Id" "(PREDi,PRED)\<in>Id" "(Ni,N)\<in>Id" "ssuc = (set succ)"
    shows  "distinct succ \<Longrightarrow> inner_loop dsti succi ui PREDi Ni 
      \<le> \<Down>Id (add_succs_spec dst ssuc u PRED N)"
    unfolding inner_loop_def add_succs_spec_def apply simp
    apply(rule le_ASSERTI)
    apply(rule nfoldliIE_rule) 
    subgoal by auto 
       (* if I add a subgoal here vcg_split_case breaks, maybe problem with variable names? *)    
       apply(rule T_specifies_I) 
       apply (vcg'\<open>-\<close> rules: mop_map_dom_member T_RESTemb mop_map_update  mop_set_insert ) 
 
         apply(auto simp add: Some_le_mm3_Some_conv Some_le_emb'_conv one_enat_def)    
      subgoal by (auto simp: it_step_insert_iff map_mmupd_def)
      subgoal 
        by(auto simp: map_mmupd_def)
    subgoal  
      by(auto split: bool.split simp add: domIff intro!: map_mmupd_update_less )  
    subgoal by (auto split: bool.split  simp add: domIff ) 
    subgoal 
      by(auto simp:  add_succs_spec_time_def distinct_card )
    done

 

  lemma inner_loop2_correct:
    assumes SR: "(succl,succ)\<in>\<langle>Id\<rangle>list_set_rel"
    assumes [simplified, simp]: 
      "(dsti,dst)\<in>Id" "(ui, u) \<in> Id" "(PREDi, PRED) \<in> Id" "(Ni, N) \<in> Id"
    shows "inner_loop dsti succl ui PREDi Ni \<le> \<Down>Id (add_succs_spec dst succ u PRED N)"   
    apply(rule inner_loop_refine) using SR by (auto simp: list_set_rel_def br_def)
         



  type_synonym bfs_state = "bool \<times> (node \<rightharpoonup> node) \<times> node set \<times> node set \<times> nat"  

    context
      fixes succ :: "node \<Rightarrow> node list nrest"
    begin
      definition init_state :: "node \<Rightarrow> bfs_state nrest"
      where 
        "init_state src \<equiv> RETURNT (False,[src\<mapsto>src],{src},{},0::nat)"

      definition "setpickt S = set_pick_time"
      definition "setdelt S = set_delete_time"

      definition pre_bfs2 :: "node \<Rightarrow> node \<Rightarrow> (nat \<times> (node\<rightharpoonup>node)) option nrest"
        where "pre_bfs2 src dst \<equiv> do {
        s \<leftarrow> init_state src;
        (f,PRED,_,_,d) \<leftarrow> whileT (\<lambda>(f,PRED,C,N,d). f=False \<and> C\<noteq>{})
          (\<lambda>(f,PRED,C,N,d). do {
            ASSERT (C\<noteq>{});
            v \<leftarrow> mop_set_pick setpickt C;
            C \<leftarrow> mop_set_del setdelt C v;
            ASSERT (v\<in>V);
            sl \<leftarrow> succ v;
            (f,PRED,N) \<leftarrow> inner_loop dst sl v PRED N;
            if f then
              RETURNT (f,PRED,C,N,d+1)
            else do {
              ASSERT (assn1 src dst (f,PRED,C,N,d));
              if (C={}) then do {
                C \<leftarrow> RETURNT N; 
                N \<leftarrow> mop_set_empty set_empty_time; 
                d \<leftarrow> RETURNT (d+1);
                RETURNT (f,PRED,C,N,d)
              } else RETURNT (f,PRED,C,N,d)
            }  
          })
          s;
        if f then RETURNT (Some (d, PRED)) else RETURNT None
        }"

 
lemma "\<langle>Id\<rangle>list_rel = Id" by simp
 

  lemma i: "SPECT (emb (\<lambda>l. distinct l \<and> set l = E `` {x}) (enat get_succs_list_time)) \<le> \<Down> (\<langle>Id\<rangle>list_set_rel) (SPECT [E``{x} \<mapsto> enat get_succs_list_time])"
  apply(rule SPECT_refine)
  by(simp add: Some_eq_emb'_conv list_set_rel_def br_def)

    lemma ii: "\<Down> (\<langle>Id\<rangle>list_set_rel) (SPECT [E``{x} \<mapsto> enat get_succs_list_time]) \<le> SPECT (emb (\<lambda>l. distinct l \<and> set l = E `` {x}) (enat get_succs_list_time))"
      using Sup_le_iff by (auto simp: conc_fun_def le_fun_def emb'_def list_set_rel_def br_def )       
 
      

  lemma rew: "SPECT (emb (\<lambda>l. distinct l \<and> set l = E `` {x}) (enat get_succs_list_time)) = \<Down> (\<langle>Id\<rangle>list_set_rel) (SPECT [E``{x} \<mapsto> enat get_succs_list_time])"
    apply(rule antisym) using i ii by auto

    
    lemma "(\<Down>R M) \<bind> f = \<Down>R (M \<bind> f)"
      apply(auto simp: pw_eq_iff refine_pw_simps)
     
      unfolding conc_fun_def  oops



      lemma pre_bfs2_refine: 
        assumes succ_impl: "\<And>ui u. \<lbrakk>(ui,u)\<in>Id; u\<in>V\<rbrakk> 
          \<Longrightarrow> succ ui \<le> \<Down> (\<langle>Id\<rangle>list_set_rel) (SPECT [E``{u} \<mapsto> enat get_succs_list_time])"
        shows "pre_bfs2 src dst \<le>\<Down>Id (pre_bfs src dst)"
        unfolding pre_bfs_def pre_bfs2_def init_state_def
        apply simp unfolding whileIET_def
        apply(rule bindT_mono)
         apply(rule whileT_mono)
         apply(clarsimp split: prod.splits)
        unfolding mop_set_pick_def 
         apply(rule bindT_mono) apply simp
        apply(subst emb_le_emb) apply simp apply(simp add:   setpickt_def)
         apply(rule bindT_mono) apply (simp add: le_fun_def mop_set_del_def setdelt_def)
        
         apply(rule le_ASSERTI) apply(rule ASSERT_leI) apply simp  unfolding rew 
         apply(rule bindT_mono) 
          apply(rule succ_impl) apply simp apply simp  
         apply(rule le_ASSERTI)   
        subgoal 
          apply(rule bindT_refine[OF inner_loop2_correct, where R=Id, simplified])   
          by (auto simp add: list_set_rel_def br_def Some_eq_emb'_conv)
        by simp
          
 
 (*
        apply (subst nres_monad1)
        apply (refine_rcg inner_loop2_correct succ_impl)
        apply refine_dref_type
        apply vc_solve (* Takes some time *)
        done *)  
  
end    
  
  term Pre_BFS_Impl.pre_bfs2

end \<comment> \<open>Pre_BFS_Impl\<close>

context Augmenting_Path_BFS
begin

(*  term pre.pre_bfs2 <- pre is not visible,
  are interpretations only visible in the local context? *)

interpretation pre: Pre_BFS_Impl c set_insert_time map_dom_member_time set_delete_time get_succs_list_time map_update_time set_pick_time
  set_empty_time
  apply standard by simp 

  term pre.pre_bfs2
    

    definition "bfs2 succ src dst \<equiv> do {
      if src=dst then 
        RETURNT (Some [])
      else do {  
        br \<leftarrow> pre.pre_bfs2 succ src dst;
        case br of
          None \<Rightarrow> RETURNT None
        | Some (d,PRED) \<Rightarrow> do {
            p \<leftarrow> valid_PRED_impl.extract_rpath c src dst PRED list_append_time map_lookup_time;
            RETURNT (Some p)
          }  
      }    
    }"
 

    lemma bfs2_refine:
      assumes succ_impl: "\<And>ui u. \<lbrakk>(ui,u)\<in>Id; u\<in>V\<rbrakk> 
        \<Longrightarrow> succ ui \<le> \<Down> (\<langle>Id\<rangle>list_set_rel) (SPECT [E``{u} \<mapsto> enat get_succs_list_time])"
      shows "bfs2 succ src dst \<le> \<Down>Id (bfs src dst)"
      unfolding bfs_def bfs2_def
      apply auto
      apply(rule bindT_mono) 
       apply(rule pre.pre_bfs2_refine[simplified, OF succ_impl]) apply simp
      by (auto )
        
 (*
      apply (refine_vcg pre_bfs2_refine)
      apply refine_dref_type
      using assms
      apply (vc_solve)
      done      *)  

  end  \<comment> \<open>Augmenting_Path_BFS\<close>


thm Augmenting_Path_BFS.bfs2_refine

interpretation Augmenting_Path_BFS  set_insert_time map_dom_member_time set_delete_time get_succs_list_time map_update_time set_pick_time 
     list_append_time map_lookup_time set_empty_time
  oops

  (*
  lemma bfs2_refine_succ: 
    assumes  "\<And>ui u. \<lbrakk>(ui,u)\<in>Id; u\<in>Graph.V c\<rbrakk> 
      \<Longrightarrow> succi ui \<le> \<Down>Id (succ u)"
    assumes [simplified, simp]: "(si,s)\<in>Id" "(ti,t)\<in>Id" "(ci,c)\<in>Id"
    shows "Graph.bfs2 ci succi si ti \<le> \<Down>Id (Graph.bfs2 c succ s t)"
    unfolding Graph.bfs2_def Graph.pre_bfs2_def (*
    apply (refine_rcg 
      param_nfoldli[param_fo, THEN nres_relD] nres_relI fun_relI)
    apply refine_dref_type
    apply vc_solve
    done *) sorry *)


end
