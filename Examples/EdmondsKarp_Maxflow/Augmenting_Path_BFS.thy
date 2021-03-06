section \<open>Breadth First Search\<close>
theory Augmenting_Path_BFS
imports 
  (* Maxflow_Lib.Refine_Add_Fofu *)
  Graph_Impl
  "../../Refine_Foreach"
(*  "NREST.RefineMonadicVCG" *)
  "../../Refine_Imperative_HOL/IICF/IICF"
  "../../Refine_Heuristics"
begin

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
  fixes  set_insert_time map_dom_member_time :: nat
    and   get_succs_list_time :: nat and  map_update_time set_pick_extract_time set_empty_time  :: nat
    and set_isempty_time init_state_time init_get_succs_list_time :: nat
  assumes [simp]: "set_pick_extract_time > 0"
begin 

  definition (in -) "hh v1 v2 v3 == (v1 + ((v2 + v3) + (Suc 0)))"

  definition (in -) add_succs_spec_time_aux   where  "add_succs_spec_time_aux cs v1 v2 v3 = (cs * hh v1 v2 v3)"
  abbreviation  "hhh == hh map_dom_member_time set_insert_time map_update_time + get_succs_list_time" 
  abbreviation "add_succs_spec_time cs == add_succs_spec_time_aux cs map_dom_member_time set_insert_time map_update_time"
  lemma add_succs_spec_time_mono: "n \<le> m \<Longrightarrow> add_succs_spec_time n \<le> add_succs_spec_time m"
    unfolding add_succs_spec_time_aux_def  
    using mult_le_cancel2 by blast  

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
 
 

 
  definition "Vvisited src C d \<equiv> (\<Union>x\<in>{0..<d}. pre_bfs_invar.Vd c src x) \<union> (pre_bfs_invar.Vd c src d - C)"
  abbreviation "outedges Vs \<equiv> {(x, y). (x, y) \<in> E \<and> x \<in> Vs}"
  abbreviation "inedges Vs \<equiv> {(y,x). (y,x) \<in> E \<and> x \<in> Vs}"
  lemma u: "\<And>Vs. inedges Vs = {(y,x). (x,y) \<in> E\<inverse> \<and> x \<in> Vs}" by simp

  lemma card_outedges_singleton: "card (outedges {x}) = card (E``{x})"
  proof - 
    have *: "outedges {x} = {x} \<times>  E``{x}" unfolding u by auto 
    show ?thesis unfolding * card_cartesian_product_singleton ..
  qed

  lemma card_inedges_singleton: "card (inedges {x}) = card (E\<inverse>``{x})"
  proof -
    thm card_cartesian_product_singleton
    have "inedges {x} = E\<inverse>``{x} \<times> {x}" unfolding u by auto
    then have "card (inedges {x}) = card (E\<inverse>``{x} \<times> {x})" by simp
    also have "\<dots> = card (E\<inverse>``{x})" by(simp add: card_cartesian_product) 
    finally show ?thesis .
  qed

abbreviation "bod \<equiv> (set_pick_extract_time + init_get_succs_list_time
                       + 2 * set_isempty_time + set_empty_time)"

definition Te :: "node \<Rightarrow> bool \<times> (nat \<Rightarrow> nat option) \<times> nat set \<times> nat set \<times> nat
   \<Rightarrow> nat" where "Te src = (\<lambda>(f,PRED,C,N,d). if f then 0
         else (card (E - (outedges (Vvisited src C d))) * (hhh+bod))
              +  (card (E - (inedges (Vvisited src C d))) * (get_succs_list_time))                                                    

                 + (card N) * (bod) + card C * bod  )"



  definition pre_bfs :: "node \<Rightarrow> node \<Rightarrow> (nat \<times> (node\<rightharpoonup>node)) option nrest"
    where "pre_bfs src dst \<equiv> do {
        s \<leftarrow> SPECT [(False,[src\<mapsto>src],{src},{},0::nat) \<mapsto> init_state_time];
    (f,PRED,_,_,d) \<leftarrow> monadic_WHILEIE (outer_loop_invar src dst) (Te src)
      (\<lambda>(f,PRED,C,N,d). SPECT [ f=False \<and> C\<noteq>{} \<mapsto> set_isempty_time])
      (\<lambda>(f,PRED,C,N,d). do {
        ASSERT (card C\<le>card V);
        (v,C) \<leftarrow> mop_set_pick_extract (\<lambda>_. set_pick_extract_time)  C;
        ASSERT (v\<in>V);
        succ \<leftarrow> SPECT (emb (\<lambda>l. distinct l \<and> set l = E``{v}) (enat ( init_get_succs_list_time + ((card (E``{v})) + (card (E\<inverse>``{v}))  )*get_succs_list_time))); 
        ASSERT (distinct succ);
        ASSERT (finite V);
        ASSERT (dom PRED \<subseteq> V);
        ASSERT (set succ \<subseteq> V);
        ASSERT (N \<subseteq> V);
        (f,PRED,N) \<leftarrow> add_succs_spec dst (set succ) v PRED N;
        if f then
          RETURNT (f,PRED,C,N,d+1)
        else do {
          ASSERT (assn1 src dst (f,PRED,C,N,d));
          b \<leftarrow> mop_set_isempty (\<lambda>_. set_isempty_time) C;
          if (b) then do {
            C \<leftarrow> RETURNT N; 
            N \<leftarrow> mop_set_empty (\<lambda>_. set_empty_time);
            d \<leftarrow> RETURNT (d+1);
            RETURNT (f,PRED,C,N,d)
          } else RETURNT (f,PRED,C,N,d)
        }  
      })
      s;
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

    txt \<open>We make a case-distinction whether \<open>d'\<le>d\<close>:\<close>
    have "d'\<le>d \<or> Suc d \<le> d'" by auto  
    moreover {
      assume "d'\<le>d"
      with VIS_eq dstd' have "dst \<in> dom PRED" by auto
      with dst_ne_VIS have False by auto
    } moreover {
      assume "Suc d \<le> d'"
      txt \<open>In the case \<open>d+1 \<le> d'\<close>, we also obtain a node
        that has a shortest path of length \<open>d+1\<close>:\<close>
      with min_dist_le[OF C] dstd' obtain v' where "v' \<in> Vd (Suc d)"
        by (auto simp: in_Vd_conv)
      txt \<open>However, the invariant states that such nodes are either in
        \<open>N\<close> or are successors of \<open>C\<close>. As \<open>N\<close> 
        and \<open>C\<close> are both empty, we again get a contradiction.\<close>
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
 
  lemma (in nf_invar) Vd_ss_V: "Vd d \<subseteq> V"
    by (auto simp: Vd_def connected_inV_iff)

  lemma (in nf_invar) finite_C[simp, intro!]: "finite C"
    using C_ss FIN_V Vd_ss_V by (blast intro: finite_subset)
  
  lemma (in nf_invar) finite_succ: "finite (E``{u})"  
    by auto
 
  definition (in -) pre_bfs_time_aux :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
    "pre_bfs_time_aux cE v1 v2 v3 v4 v5 = v1 + v2 + ( cE * (v3+v4+v5) + v4) "

  lemma (in -)  pre_bfs_time_aux_mono: "cE1 \<le> cE2 \<Longrightarrow> pre_bfs_time_aux cE1 v1 v2 v3 v4 v5
              \<le> pre_bfs_time_aux cE2 v1 v2 v3 v4 v5" 
    by(auto simp: pre_bfs_time_aux_def)

  abbreviation "pre_bfs_time cE \<equiv> pre_bfs_time_aux cE init_state_time set_isempty_time hhh bod get_succs_list_time"
                                           
  lemma pre_bfs_time_progress: "pre_bfs_time cE > 0"   by (simp add: pre_bfs_time_aux_def)
  
  lemma Te_start_ub: assumes "valid_PRED c src PRED"                                                  
    shows "set_isempty_time +  init_state_time + (Te src (False, [src \<mapsto> src], {src}, {}, 0)) \<le> pre_bfs_time (card E)"
  proof -
    from assms have "finite E"  
      using valid_PRED.FIN_E by blast
    then have "card (E - outedges (Vvisited src {src} 0))  \<le> card E"
          "card (E - inedges (Vvisited src {src} 0))  \<le> card E"
      by(auto intro: card_mono)
    then have "Te src (False, [src \<mapsto> src], {src}, {}, 0) \<le> card E * (hhh + bod) + card E * get_succs_list_time + bod"
      apply (auto simp add: Te_def pre_bfs_time_aux_def ) 
      using mlex_leI mult_le_mono1 by blast
    also have "set_isempty_time +  init_state_time + \<dots> \<le>  pre_bfs_time (card E)"
      apply(auto simp: pre_bfs_time_aux_def)  
      by (simp add: distrib_left)
    finally show ?thesis by auto
  qed
  
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



  lemma   Te_decr_succ_step: assumes "nf_invar c src dst PRED C N d"
      and Cx: "C = {x}"
    shows
      "Te src(False, map_mmupd PRED (E `` {x} - dom PRED) x, N \<union> (E `` {x} - dom PRED), {}, Suc d)
      \<le> Te src (False, PRED, C, N, d)" (is "?L \<le> ?R")
    and "set_isempty_time + set_pick_extract_time +  (init_get_succs_list_time + (card (E `` {x}) + card (E\<inverse> `` {x})) * get_succs_list_time) + add_succs_spec_time (card (E `` {x}))  + set_isempty_time + set_empty_time
      \<le> Te src (False, PRED, C, N, d) -
         Te src
          (False, map_mmupd PRED (E `` {x} - dom PRED) x, N \<union> (E `` {x} - dom PRED), {}, Suc d)" (is "?P \<le> _")
  proof -
    from assms(2) have xC: "x\<in>C" by auto
    from  assms(1) have fE: "finite E" unfolding nf_invar_def nf_invar'_def
      using valid_PRED.FIN_E  by auto
    from assms(1) have fC: "finite C"  
      using nf_invar.finite_C by blast   
      
    have i: "(pre_bfs_invar.Vd c src (Suc d) - (N \<union> (E `` {x} - dom PRED))) = {}"
      unfolding nf_invar'.N_eq[OF assms(1)[unfolded nf_invar_def, THEN conjunct1]] assms(2)
      apply auto
      subgoal using pre_bfs_invar.Vdsucinter_conv by fastforce
      subgoal
        by (metis IntE Suc_n_not_le_n \<open>N = pre_bfs_invar.Vd c src (d + 1) \<inter> E `` (pre_bfs_invar.Vd c src d - C)\<close> assms(1) assms(2) nf_invar.inPREDD pre_bfs_invar.in_Vd_conv)  
      done
  
    have k: "Vvisited src (N \<union> (E `` {x} - dom PRED)) (Suc d)
        = Vvisited src {} d"
      unfolding Vvisited_def unfolding i by (simp add: Un_commute atLeast0_lessThan_Suc) 
  
    have l: "?L \<le> card (E - outedges (Vvisited src {} d)) * (hhh + bod) + card (E - inedges (Vvisited src {} d)) * get_succs_list_time +
      (card N) *(bod)  + (card (E `` {x} - dom PRED)) * (bod)"
      unfolding Te_def                        apply simp unfolding k  
      apply (subst card_Un_disjoint)
      subgoal using assms(1)  
        by (meson Efin_imp_Vfin xC fE finite_subset le_sup_iff nf_invar.cardN'_)   
      subgoal using fE by auto   subgoal using assms(1) 
        by (metis (no_types, lifting) DiffD2 Int_emptyI UnCI nf_invar'.VIS_eq nf_invar_def)
      by (auto simp: add_mult_distrib)   
  
    have Ein: "E - inedges (Vvisited src C d) = (E - inedges (Vvisited src {} d)) \<union> inedges C"
      unfolding Vvisited_def apply auto 
      by (metis assms(1) nat_neq_iff nf_invar.CVdI pre_bfs_invar.in_Vd_conv)
    have Ein2: "card (E - inedges (Vvisited src {} d) \<union> inedges C) = card (E - inedges (Vvisited src {} d)) + card (inedges C)"
      apply(rule card_Un_disjoint) apply rule apply fact 
      subgoal using \<open>finite C\<close>      by (metis (no_types, lifting) Collect_mem_eq Diff_iff Ein UnCI \<open>finite E\<close> finite_subset mem_Collect_eq subsetI) 
      apply (auto simp: Vvisited_def)    using assms(1) nf_invar.CVdI by blast 
  
    have E: "E - outedges (Vvisited src C d) = (E - outedges (Vvisited src {} d)) \<union> outedges C"
      unfolding Vvisited_def apply auto 
      by (metis assms(1) nat_neq_iff nf_invar.CVdI pre_bfs_invar.in_Vd_conv)
    have E2: "card (E - outedges (Vvisited src {} d) \<union> outedges C) = card (E - outedges (Vvisited src {} d)) + card (outedges C)"
      apply(rule card_Un_disjoint) apply rule apply fact 
      subgoal using \<open>finite C\<close>      by (metis (no_types, lifting) Collect_mem_eq Diff_iff E UnCI \<open>finite E\<close> finite_subset mem_Collect_eq subsetI) 
      apply (auto simp: Vvisited_def)    using assms(1) nf_invar.CVdI by blast 
  
    have "card (E `` {x} - dom PRED) \<le> card (E `` {x}) " apply(rule card_mono) using fE by auto
    also have "\<dots> = card (outedges C)" using card_outedges_singleton Cx  by simp 
    finally have c: "card (E `` {x} - dom PRED) \<le> card (outedges C)" by auto
  
    have r: "(card (E - outedges (Vvisited src {} d)) ) * (hhh + bod)  + card (outedges C) * (hhh+bod)
            + card (E - inedges (Vvisited src {} d)) * get_succs_list_time + card (inedges C) * get_succs_list_time  +
         (card N)*(bod) + (card C) * (bod) \<le> ?R"  
      unfolding Te_def apply clarsimp   unfolding E E2 Ein Ein2
      by (simp add: distrib_right) 
  
    show "?L \<le> ?R" apply(rule order.trans[OF l]) apply(rule order.trans[OF _ r])  using c apply auto  
      by (simp add: mult_le_mono trans_le_add1)  
   
    show "?P \<le> ?R - ?L" apply(rule order.trans[OF _ diff_le_mono[OF r]] )
        apply(rule order.trans[OF _ diff_le_mono2[OF l]] )
        unfolding assms(2) card_outedges_singleton card_inedges_singleton apply (simp add:    add_succs_spec_time_aux_def )  
      apply(rule dual_order.trans[OF diff_le_mono2[where n="card (E `` {x}) * bod"]]) 
      subgoal by (auto intro!: card_mono simp: fE)       
      apply (simp add: add.commute add.left_commute distrib_left distrib_right)  
      done
  qed

  lemma [simp]: "nf_invar c src dst PRED C N d \<Longrightarrow> finite V"
    using nf_invar'_def nf_invar.axioms(1) valid_PRED.FIN_V by blast  
 

  lemma hl: "x \<in> C \<Longrightarrow> C \<noteq> {}" by auto
 

  lemma Te_decr_level_step: assumes "nf_invar c src dst PRED C N d"
    "C \<noteq> {}" and  xC: "x \<in> C"
  shows "Te src
             (False, map_mmupd PRED (E `` {x} - dom PRED) x, C - {x},
              N \<union> (E `` {x} - dom PRED), d)
      \<le> Te src (False, PRED, C, N, d)" (is "?L \<le> ?R")
    and "set_isempty_time + set_pick_extract_time  + (init_get_succs_list_time+ (card (E `` {x}) + card (E\<inverse> `` {x})) * get_succs_list_time) + add_succs_spec_time (card (E `` {x}))  + set_isempty_time
         \<le> Te src (False, PRED, C, N, d) -
            Te src
             (False, map_mmupd PRED (E `` {x} - dom PRED) x, C - {x},
              N \<union> (E `` {x} - dom PRED), d)" (is "?P \<le> _")
  proof - 
    from  assms(1) have fE: "finite E" unfolding nf_invar_def nf_invar'_def
      using valid_PRED.FIN_E  by auto
    from assms(1) have fC: "finite C"  
      using nf_invar.finite_C by blast  
   
  
    have f: "outedges {x} = {x} \<times> E `` {x}" by auto
    have f2: "{(xa, y). (xa, y) \<in> E \<and> xa = x} = {x} \<times> E `` {x}" by auto
   
  
    have v: "Vvisited src (C - {x}) d = Vvisited src C d \<union> {x}" unfolding Vvisited_def apply auto  
      using assms(1) nf_invar.CVdI xC by blast
    have ve: " Vvisited src C d \<inter> {x} = {}" unfolding Vvisited_def 
      by (smt Diff_iff Int_emptyI UN_iff UnE assms(1) atLeastLessThan_iff less_not_refl nf_invar.CVdI pre_bfs_invar.in_Vd_conv singletonD xC) 
  
    have 1: "(E - outedges (Vvisited src (C - {x}) d)) \<union> (outedges {x}) = (E - outedges (Vvisited src C d))"
      unfolding v using ve by blast
  
    have 11: "card ((E - outedges (Vvisited src (C - {x}) d)) \<union> (outedges {x}))
        = card (E - outedges (Vvisited src (C - {x}) d)) + card (outedges {x})"
      apply(rule card_Un_disjoint) subgoal using fE by auto
      subgoal apply(rule finite_subset[OF _ fE]) by auto
      subgoal apply auto  
        by (simp add: v)  
      done
  
    have in1: "(E - inedges (Vvisited src (C - {x}) d)) \<union> (inedges {x}) = (E - inedges (Vvisited src C d))"
      unfolding v using ve by blast
  
    have in11: "card ((E - inedges (Vvisited src (C - {x}) d)) \<union> (inedges {x}))
        = card (E - inedges (Vvisited src (C - {x}) d)) + card (inedges {x})"
      apply(rule card_Un_disjoint) subgoal using fE by auto
      subgoal apply(rule finite_subset[OF _ fE]) by auto
      subgoal apply auto  
        by (simp add: v)  
      done
  
    have fN: "finite N"  
      by (meson Efin_imp_Vfin assms(1) fE le_sup_iff nf_invar.cardN'_ rev_finite_subset xC)  
   
    have "(card (E - outedges (Vvisited src (C - {x}) d)))* (hhh + bod) + (card (E `` {x})) * (hhh + bod)
        + (card (E - inedges (Vvisited src (C - {x}) d)))* get_succs_list_time + (card (E\<inverse> `` {x})) * get_succs_list_time
           + card N * bod + card C * bod
            = card (E - outedges (Vvisited src C d)) * (hhh + bod) + 
            card (E - inedges (Vvisited src C d)) * get_succs_list_time  + (card N) *(bod) + card C * bod"
       unfolding 1[symmetric] 11[unfolded card_outedges_singleton] in1[symmetric] in11[unfolded card_inedges_singleton] 
      by (simp add: add_mult_distrib) 
    also have r: "... = ?R" unfolding Te_def by simp 
    finally have r: " ?R= (card (E - outedges (Vvisited src (C - {x}) d)))* (hhh + bod) + (card (E `` {x})) * (hhh + bod)
        + (card (E - inedges (Vvisited src (C - {x}) d)))* get_succs_list_time + (card (E\<inverse> `` {x})) * get_succs_list_time
           + card N * bod + card C * bod"
        by auto
  
      have l1: "?L \<le> card (E - outedges (Vvisited src (C - {x}) d)) * (hhh + bod) +
                card (E - inedges (Vvisited src (C - {x}) d)) * get_succs_list_time + 
               (card N + card (E `` {x}))*(bod) + card (C - {x}) * bod"
      unfolding Te_def apply simp apply(rule order.trans[OF card_Un_le]) apply simp apply(rule card_mono) using fE fN by auto   
    also have l: "\<dots> \<le> (card (E - outedges (Vvisited src (C - {x}) d)) + card (E `` {x})) * (hhh + bod)
                + card (E - inedges (Vvisited src (C - {x}) d)) * get_succs_list_time  
                 + (card N) * (bod) + card (C - {x}) * bod"
      by (simp add: add_mult_distrib) 
    finally have l: "?L \<le> (card (E - outedges (Vvisited src (C - {x}) d)) + card (E `` {x})) * (hhh + bod)
                + card (E - inedges (Vvisited src (C - {x}) d)) * get_succs_list_time  
               + (card N) * (bod) + card (C - {x}) * bod" .
    
  
    show "?L \<le> ?R" apply(rule order.trans[OF l]) unfolding  r apply (simp add: add_mult_distrib)
      apply(rule order.trans[where b ="card C * bod "])
      subgoal apply simp apply(rule card_mono) using fC by auto
      subgoal by simp
      done
    have z: "card {(xa, y). (xa, y) \<in> E \<and> xa = x} = card (E `` {x})" unfolding f2 card_cartesian_product_singleton by auto
  
    have k: "(card N + card (E `` {x})) * bod  = card N * bod + card (E `` {x}) * bod"  
      by (simp add: add_mult_distrib2 mult.commute)  
    have k2: "card (E `` {x}) * (hhh + bod)   = card (E `` {x}) * hhh + card (E `` {x}) *bod "  
      by (simp add: add_mult_distrib2 mult.commute)   
    have k3: "(card (E `` {x}) + card (E\<inverse> `` {x})) * get_succs_list_time = card (E `` {x}) * get_succs_list_time + card (E\<inverse> `` {x}) * get_succs_list_time"
      by (simp add: add_mult_distrib2 mult.commute)   
    have d: "(card C - card (C - {x})) = 1" using xC fC
      by (simp add: Suc_leI assms(2) card_gt_0_iff) 
  
    show "?P \<le> ?R - ?L"  unfolding r
        apply(rule order.trans[OF _ diff_le_mono2[OF l1]] )
      apply (simp add:  add_succs_spec_time_aux_def )  
      unfolding k unfolding k2 unfolding k3 apply simp
      apply(subst (3) add.assoc[symmetric])
      apply(subst diff_add_assoc)  apply (auto intro!: card_mono simp: d fC diff_mult_distrib[symmetric]) 
      by (simp add: add_mult_distrib2)  
  qed
   


  lemma (in nf_invar) Cge1: "x \<in> C \<Longrightarrow> card C \<ge> 1"  
    using card_0_eq finite_C by force  

  lemma   Te_pays_exit: assumes "nf_invar c src dst PRED C N d"
    "x \<in> C"
       shows "set_isempty_time + set_pick_extract_time  + (init_get_succs_list_time + (card (E `` {x}) + card (E\<inverse> `` {x})) * get_succs_list_time) + add_succs_spec_time (card (E `` {x}))
         \<le> Te src (False, PRED, C, N, d) - Te src (True, PRED', C - {x}, N', Suc d)" (is "?P \<le> ?R - ?L")
  proof -
    from  assms(1) have fE: "finite E" unfolding nf_invar_def nf_invar'_def
      using valid_PRED.FIN_E  by auto
    have l: "?L = 0" by(auto simp: Te_def)
  
  
    have "card (E``{x}) = card (outedges {x})" unfolding card_outedges_singleton ..
    also    
    from assms(2) have "outedges {x} \<subseteq> E - outedges (Vvisited src C d)"
      unfolding Vvisited_def apply auto  
      by (metis assms(1) less_not_refl nf_invar.CVdI pre_bfs_invar.in_Vd_conv)  
    then have "card (outedges {x}) \<le> card (E - outedges (Vvisited src C d))"
      apply (rule card_mono[rotated]) apply rule apply fact done
    finally have out: "card (E``{x}) \<le> card (E - outedges (Vvisited src C d))" .
  
    then have outr1: "card (E - outedges (Vvisited src C d)) * (hhh + bod) \<ge> card (E``{x}) * (hhh+bod)"
      by(simp only: mult_le_mono)
  
  
    have "card (E\<inverse>``{x}) = card (inedges {x})" unfolding card_inedges_singleton ..
    also    
    from assms(2) have "inedges {x} \<subseteq> E - inedges (Vvisited src C d)"
      unfolding Vvisited_def apply auto  
      by (metis assms(1) less_not_refl nf_invar.CVdI pre_bfs_invar.in_Vd_conv)  
    then have "card (inedges {x}) \<le> card (E - inedges (Vvisited src C d))"
      apply (rule card_mono[rotated]) apply rule apply fact done
    finally have out: "card (E\<inverse>``{x}) \<le> card (E - inedges (Vvisited src C d))" .
  
    then have inr1: "card (E - inedges (Vvisited src C d)) * get_succs_list_time \<ge> card (E\<inverse>``{x}) * get_succs_list_time"
      by(simp only: mult_le_mono)
  
    have "card C \<ge> 1" using assms(2)  
      using assms(1) nf_invar.Cge1 by blast  
    then have p: "bod \<le> card C * bod" by simp
    have "card (E``{x}) * hhh  +  bod  + card (E\<inverse>``{x}) * get_succs_list_time\<le> card (E``{x}) * (hhh+bod)  + card N * bod + card C * bod + card (E\<inverse>``{x}) * get_succs_list_time"
      using p apply auto 
      by (simp add: add_le_mono trans_le_add1) 
    also  have  "\<dots> \<le> ?R" unfolding Te_def apply simp
      using outr1 inr1 by presburger
    finally have r: "card (E``{x}) * hhh  +  bod  + card (E\<inverse>``{x}) * get_succs_list_time \<le> ?R" .
    show "?P \<le> ?R - ?L" unfolding l
      apply(rule dual_order.trans[OF _ ] )   apply simp
      apply(rule r)
      apply(simp add: add_succs_spec_time_aux_def  comm_semiring_class.distrib distrib_left)
      done
  qed
     

(*
theorem pre_bfs_correct':
    assumes [simp]: "src\<in>V" "src\<noteq>dst"       
    assumes [simp]: "finite V"
    shows "pre_bfs src dst \<le> SPECT (emb (bfs_spec src dst) (pre_bfs_time (card V)))"
  unfolding pre_bfs_def add_succs_spec_def  
  apply(labeled_VCG rules: mop_set_pick_def mop_set_del_def  mop_set_empty_def mop_set_isempty_def)                                                                                  
proof casify
  case monwhile {
    case progress then show ?case by(progress\<open>simp\<close>)
    case precondition then show ?case by (auto simp: invar_init)
    case invariant {
      case cond2 {
        case the {
          case ASSERT   then show ?case by (auto simp: nf_invar.invar_C_ss_V)
          case ASSERTa  then show ?case by (auto simp: nf_invar.invar_C_ss_V)
          case ASSERTb  then show ?case by (auto simp: nf_invar.invar_C_ss_V)
          case ASSERTc  then show ?case by (auto  simp: nf_invar.invar_N_ss_Vis)  
          case cond {
            case the {
              case cond2 {
                case (the ) { 
                  case (time s a b ca d e x xa xb aa ba caa )  then show ?case by(auto simp: Te_pays_exit)
                }

                case func then show ?case by(auto simp: nf_invar.invar_exit') 
              }
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
*)
 

  lemma if_splitI: "\<And>B. (b \<Longrightarrow> t \<le> A) \<Longrightarrow> (~b \<Longrightarrow> t \<le> B) \<Longrightarrow> t \<le> (if b then A else B)"
    by auto
  
  lemma GI: "(b \<Longrightarrow> t \<le> t') \<Longrightarrow> (b) \<Longrightarrow> Some t \<le> G b t'"
    by (auto simp: G_def)
  
  
  lemma rr: "\<And>B. A \<le> B \<Longrightarrow> a \<le> A \<Longrightarrow> (A::enat)-a \<le> B -a"
    by (simp add: helper) 
  
  lemma r: "(a + enat b) - enat b = (a::enat)"  apply(cases a) by auto 

  lemma HI: "((Es0 \<ge> Es) \<Longrightarrow> Some (t' + t + (Es0 - Es)) \<le> Qs)  \<Longrightarrow> (Es0 \<ge> Es) \<Longrightarrow> Some t' \<le> H Qs t Es0 Es"
    unfolding H_def unfolding mm3_def apply simp
    unfolding mm2_def apply simp apply(cases Qs)   apply auto
    subgoal  
      using leD less_le_trans by fastforce  
    subgoal for i apply(cases t) defer apply simp 
      apply simp
  proof (goal_cases)
    case (1 a)
    from 1(2) have gl: "a + (Es0 - Es) = a + Es0 - Es" by auto
    thm rr[OF 1(1), where a="t + enat (Es0 - Es)"]
    have "t' = (t' + enat (a + (Es0 - Es))) - (enat (a + (Es0 - Es)))" by(simp add: r)   
    also have "\<dots> \<le> i - (enat (a + (Es0 - Es)))"
      apply(rule rr)
      subgoal using 1(1) by (simp add: add.assoc)  
      by simp 
    finally show ?case unfolding gl .
  qed 
    done


  lemma Te_decr: "nf_invar c src dst f {} N d \<Longrightarrow> Te src (False, PRED, {}, N, d) \<le> Te src (False, [src \<mapsto> src], {src}, {}, 0)"
    unfolding Te_def apply clarsimp
  proof (goal_cases)
    case 1
    with nf_invar.empty_assm have Ne: "N= {}" by blast 
    from 1 have "finite (Graph.V c)"  
      by simp  
    have "Graph.V c = V" by auto
    from 1 have "finite (Graph.E c)"  
      by simp
    moreover have "Graph.E c = E" by auto
    ultimately have fE: "finite E" by auto
  
    have v_e: "Vvisited src {src} 0 = {}" apply (simp add: Vvisited_def) using pre_bfs_invar.src_Vd0 by auto
    from v_e have "E - (outedges (Vvisited src {} d)) \<subseteq> E - (outedges (Vvisited src {src} 0))" by auto
    have Aout: "card (E - (outedges (Vvisited src {} d))) \<le> card (E - (outedges (Vvisited src {src} 0)))"
      apply(rule card_mono) apply(rule finite_Diff) apply fact
      apply fact done
  
    from v_e have "E - (inedges (Vvisited src {} d)) \<subseteq> E - (inedges (Vvisited src {src} 0))" by auto
    have Ain: "card (E - (inedges (Vvisited src {} d))) \<le> card (E - (inedges (Vvisited src {src} 0)))"
      apply(rule card_mono) apply(rule finite_Diff) apply fact
      apply fact done
  
      show ?case  unfolding Ne apply simp 
        apply(rule order.trans[OF add_le_mono])
          apply(rule mult_le_mono1) apply fact
         apply(rule mult_le_mono1) apply fact
        by simp
  qed 
     
             
  lemma (in nf_invar') domPREDV: "dom PRED \<subseteq> V"
    unfolding VIS_eq N_eq Vd_def V_def apply auto  
    by (smt Graph.min_dist_is_dist SRC_IN_V V_def dist_cases mem_Collect_eq)   
  
  
               
  lemma (in nf_invar') N_V: "N \<subseteq> V"
    unfolding   N_eq Vd_def V_def by auto 

  theorem pre_bfs_correct:
    assumes [simp]: "src\<in>V" "src\<noteq>dst"       
    assumes [simp]: "finite V"
    shows "pre_bfs src dst \<le> SPECT (emb (bfs_spec src dst) (pre_bfs_time (card E)))"
    unfolding pre_bfs_def add_succs_spec_def
    apply(rule T_specifies_I) 

    apply(vcg' \<open>clarsimp\<close> rules: if_splitI GI HI  mop_set_pick_extract    mop_set_empty mop_set_isempty)
    apply (simp_all split: bool.splits add: Some_le_mm3_Some_conv Some_le_emb'_conv)
    apply safe 

      apply ( vc_solve  simp:  domI 
            Te_pays_exit
            
            
            Te_decr_level_step(1)
            Te_decr_level_step(2)
            

            invar_init

            nf_invar.invar_C_ss_V 
            nf_invar.invar_succ_step 
              nf_invar.invar_exit'     
            nf_invar'.invar_shift
            nf_invar'.invar_restore        
            nf_invar.finite_succ
            nf_invar.invar_N_ss_Vis)  
    subgoal apply(subst (asm) Te_decr_succ_step(2)) by auto   
    subgoal apply(subst (asm) Te_decr_succ_step(2)) by auto    
    subgoal by (auto intro!: Te_decr_succ_step)   
    subgoal by (auto intro!: Te_decr_succ_step)  
    subgoal by (auto intro: Te_decr_level_step(2))
    subgoal by (auto intro: Te_decr_level_step(2))
    subgoal by (auto intro:   nf_invar'.invar_restore   nf_invar.invar_succ_step )  
    subgoal by(auto intro: Te_decr_level_step) 
    subgoal by (auto intro:   nf_invar'.invar_restore   nf_invar.invar_succ_step )  
    subgoal by(auto intro: Te_decr_level_step) 
    subgoal by (auto  simp: nf_invar_def dest: nf_invar'.N_V)
    subgoal using V_def by blast 
    subgoal by (auto  simp: nf_invar_def dest: nf_invar'.domPREDV)
    subgoal by(auto dest: nf_invar.cardC) 
    subgoal by(auto simp:  f_invar.invar_found)
    subgoal unfolding f_invar_def  using Te_start_ub by(auto intro!:  hlp_nat  )  
    subgoal by(auto simp:  nf_invar.invar_not_found)                   
    subgoal unfolding nf_invar'_def nf_invar_def  using Te_start_ub by(auto intro!:  hlp_nat  )  
    subgoal using Te_decr by auto
    subgoal for a b d e apply(cases a) subgoal   by auto using Te_decr by auto
    done 

end

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
  definition (in -) "extract_rpath_time_aux cV v1 v2 = cV * (v1 + v2)"
  abbreviation (in valid_PRED_impl) "extract_rpath_time cV \<equiv> extract_rpath_time_aux cV map_lookup_time list_append_time"

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
    definition (in -) "extract_rpath src dst PRED map_lookup_time list_append_time V   \<equiv> do {
      (d,p) \<leftarrow> whileT        
        (\<lambda>(v,p). v\<noteq>src) (\<lambda>(v,p). do {
        ASSERT (v\<in>dom PRED);
        ASSERT (v\<in>V);
        ASSERT (card (dom PRED) \<le> card V);
        u \<leftarrow> mop_map_lookup (\<lambda>_. map_lookup_time) PRED v;
        p \<leftarrow> mop_append (\<lambda>_. list_append_time) (u,v) p;
        v \<leftarrow> RETURNT u;
        RETURNT (v,p)
      }) (dst,[]);
      RETURNT p
    }"

  end  

  context valid_PRED_impl begin

  thm FIN_V
  lemma domPREDV: "dom PRED \<subseteq> V"
    apply auto subgoal for x y 
      apply(cases "x=src") using SRC_IN_V apply simp
      apply(frule PRED_E) apply simp unfolding V_def by auto
    done


    lemma extract_rpath_correct':
      assumes "dst\<in>dom PRED" 
      shows "extract_rpath src dst PRED   map_lookup_time list_append_time V
        \<le> SPECT (emb (\<lambda>p. isSimplePath src p dst \<and> length p = ndist dst) extract_rpath_time')"
      using assms unfolding extract_rpath_def isSimplePath_def  
      apply(subst whileIET_def[symmetric, where I="extract_rpath_inv src dst PRED" and E =Ter  ])
      apply simp
      apply(rule T_specifies_I) 
      apply (vcg'\<open>-\<close> rules: mop_map_lookup mop_append)   

      apply (auto simp: Some_le_mm3_Some_conv Some_le_emb'_conv
                          extract_rpath_time'_def extract_rpath_inv_def
                               PRED_closed[THEN domD] PRED_E PRED_dist Ter_def)
      subgoal apply(rule card_mono) by (simp_all add: domPREDV)
      subgoal using domPREDV by auto 
      done

    lemma extract_rpath_correct:
      assumes "dst\<in>dom PRED"
      shows "extract_rpath  src dst PRED map_lookup_time list_append_time V
        \<le> SPECT (emb (\<lambda>p. isSimplePath src p dst \<and> length p = ndist dst) (extract_rpath_time (card V)))"
      apply(rule dual_order.trans[OF _ extract_rpath_correct'])
      apply (auto simp add: emb_le_emb extract_rpath_time_aux_def extract_rpath_time'_def intro!: ndist_le_V)
        using assms  apply auto  
        using Graph.isPath_rtc Graph.isSimplePath_def connected_edgeRtc by blast 
  end

locale Augmenting_Path_BFS = Graph + 
  fixes  set_insert_time map_dom_member_time  get_succs_list_time map_update_time set_pick_extract_time :: nat
    and list_append_time map_lookup_time set_empty_time set_isempty_time init_state_time init_get_succs_list_time :: nat
  assumes [simp]: "map_lookup_time > 0"
  assumes [simp]: "set_pick_extract_time > 0"
begin 

interpretation pre: Pre_BFS_Impl c set_insert_time map_dom_member_time 
    get_succs_list_time map_update_time set_pick_extract_time set_empty_time set_isempty_time init_state_time init_get_succs_list_time
  apply standard by simp 


  term Pre_BFS_Impl.pre_bfs 
  
    definition "bfs src dst \<equiv> do {
      if src=dst then RETURNT (Some [])
      else do {
        br \<leftarrow> pre.pre_bfs src dst;
        case br of
          None \<Rightarrow> RETURNT None
        | Some (d,PRED) \<Rightarrow> do {
            p \<leftarrow> extract_rpath src dst PRED map_lookup_time list_append_time V;
            RETURNT (Some p)
          }  
      }    
    }"  thm pre.pre_bfs_correct

    definition bfs_time   where "bfs_time src dst = pre.pre_bfs_time  (card E)   + valid_PRED_impl.extract_rpath_time list_append_time map_lookup_time (card V)"

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
      \<and> f = (dst\<in>(set ti) - dom PRED) \<and> dom PRED \<subseteq> V
    )  (map_dom_member_time+((set_insert_time+map_update_time) + (1::nat)))
    (succ)
    (\<lambda>(f,PRED,N). \<not>f)
    (\<lambda>v (f,PRED,N). do {
      ASSERT (card (dom PRED) \<le> card V); 
      ASSERT (v\<in>V);
      b \<leftarrow> mop_map_dom_member (%_. map_dom_member_time) PRED v;
      if b then RETURNT (f,PRED,N)
      else do {
        PRED \<leftarrow> mop_map_update (\<lambda>_. map_update_time) PRED v u;
        ASSERT (v\<notin>N);
        ASSERT (card N \<le> card V);
        N \<leftarrow> mop_set_insert (%_. set_insert_time) v N;
        RETURNT (v=dst,PRED,N)
      }
    }) 
    (False,PRED,N)"


  lemma GG: "N \<subseteq> V \<Longrightarrow> A \<subseteq> V \<Longrightarrow> finite V \<Longrightarrow> card (N \<union> (A - dom PRED)) \<le> card V"
    apply(rule card_mono) by auto 

  lemma inner_loop_refine: 
    (*assumes NSS: "N \<subseteq> dom PRED"*) 
    assumes [simplified, simp]: 
      "(dsti,dst)\<in>Id" "(succi,succ)\<in>Id" "(ui,u)\<in>Id" "(PREDi,PRED)\<in>Id" "(Ni,N)\<in>Id" "ssuc = (set succ)"
      "finite V"
      and PRED: "dom PRED \<subseteq> V" and ssuvV: "set succ \<subseteq> V" and  N: "N \<subseteq> V"
    shows  "distinct succ \<Longrightarrow> inner_loop dsti succi ui PREDi Ni 
      \<le> \<Down>Id (add_succs_spec dst ssuc u PRED N)"
    unfolding inner_loop_def add_succs_spec_def apply simp
    apply(rule le_ASSERTI)
    apply(rule nfoldliIE_rule) 
    subgoal using PRED by auto  
       (* if I add a subgoal here vcg_split_case breaks, maybe problem with variable names? *)    
       apply(rule T_specifies_I) 
       apply (vcg'\<open>-\<close> rules: mop_map_dom_member T_RESTemb mop_map_update  mop_set_insert ) 
 
         apply(auto simp add: Some_le_mm3_Some_conv Some_le_emb'_conv one_enat_def)    
      subgoal by (auto simp: it_step_insert_iff map_mmupd_def)
      subgoal 
        by(auto simp: map_mmupd_def)
      subgoal apply(subst (asm) GG) using ssuvV N by auto   
      subgoal apply(subst (asm) GG) using ssuvV N by auto
      subgoal using ssuvV by auto 
      subgoal using ssuvV by auto  
      subgoal apply(rule card_mono) using ssuvV  by auto  
      subgoal apply(rule card_mono) using ssuvV  by auto 
    subgoal by (auto split: bool.split simp add: domIff intro!: map_mmupd_update_less )  
    subgoal by (auto split: bool.split  simp add: domIff ) 
    subgoal by (auto simp: hh_def add_succs_spec_time_aux_def distinct_card )
    done

 

  lemma inner_loop2_correct:
    assumes SR: "(succl,succ)\<in>\<langle>Id\<rangle>list_set_rel"
    assumes [simplified, simp]: 
      "(dsti,dst)\<in>Id" "(ui, u) \<in> Id" "(PREDi, PRED) \<in> Id" "(Ni, N) \<in> Id" "finite V"
      and PRED: "dom PRED \<subseteq> V" and ssuvV: "set succl \<subseteq> V" and  N: "N \<subseteq> V"
    shows "inner_loop dsti succl ui PREDi Ni \<le> \<Down>Id (add_succs_spec dst succ u PRED N)"   
    apply(rule inner_loop_refine) using SR ssuvV PRED N by (auto simp: list_set_rel_def br_def)
         



  type_synonym bfs_state = "bool \<times> (node \<rightharpoonup> node) \<times> node set \<times> node set \<times> nat"  

    context
      fixes succ :: "node \<Rightarrow> node list nrest"
      fixes init_state :: "node \<Rightarrow> bfs_state nrest"
    begin
        

      definition "loopguard f C = do {
                  b \<leftarrow> mop_set_isempty (\<lambda>_. set_isempty_time) C;
                  RETURNT (f=False \<and> ~b) }"
      
      lemma loopguard_correct: "(f,f')\<in>Id \<Longrightarrow> (C,C')\<in>Id \<Longrightarrow> loopguard f C \<le> \<Down>Id ( SPECT [f' = False \<and> C' \<noteq> {} \<mapsto> enat set_isempty_time] )" 
        unfolding loopguard_def apply simp
        apply(rule T_specifies_I) 
        by (vcg'\<open>simp\<close> rules: mop_set_isempty )   
      

    

      definition pre_bfs2 :: "node \<Rightarrow> node \<Rightarrow> (nat \<times> (node\<rightharpoonup>node)) option nrest"
        where "pre_bfs2 src dst \<equiv> do {
        s \<leftarrow> init_state src;
        (f,PRED,ttt,tt,d) \<leftarrow> monadic_WHILE (\<lambda>(f,PRED,C,N,d). loopguard f C)
          (\<lambda>(f,PRED,C,N,d). do {
            ASSERT (C\<noteq>{});
            ASSERT (card C\<le>card V);
            (v,C) \<leftarrow> mop_set_pick_extract (\<lambda>_. set_pick_extract_time) C;
            ASSERT (v\<in>V);
            sl \<leftarrow> succ v;
            ASSERT (finite V);
            ASSERT (dom PRED \<subseteq> V);
            ASSERT (set sl \<subseteq> V);
            ASSERT (N \<subseteq> V);
            (f,PRED,N) \<leftarrow> inner_loop dst sl v PRED N;
            if f then
              RETURNT (f,PRED,C,N,d+(1::nat))
            else do {
              ASSERT (assn1 src dst (f,PRED,C,N,d));
              b \<leftarrow> mop_set_isempty (\<lambda>_. set_isempty_time) C;
              if b then do {
                C \<leftarrow> RETURNT N; 
                N \<leftarrow> mop_set_empty (\<lambda>_. set_empty_time); 
                d \<leftarrow> RETURNT (d+(1::nat));
                RETURNT (f,PRED,C,N,d)
              } else RETURNT (f,PRED,C,N,d)
            }  
          })
          s;
        if f then RETURNT (Some (d, PRED)) else RETURNT None
        }"
 
  lemma distinct_in_list_set_rel: "distinct l \<Longrightarrow> (l, set l) \<in> \<langle>Id\<rangle>list_set_rel"
      by (auto simp add: list_set_rel_def br_def Some_eq_emb'_conv) 

  lemma pre_bfs2_refine: 
    assumes succ_impl: "\<And>ui u. \<lbrakk>(ui,u)\<in>Id; u\<in>V\<rbrakk> 
        \<Longrightarrow> succ ui \<le> \<Down> (\<langle>Id\<rangle>list_set_rel) (SPECT [E``{u} \<mapsto> enat (init_get_succs_list_time+ (card (E``{u}) + card (E\<inverse>``{u}))*get_succs_list_time )])"
      and init_state_impl: "\<And>src. init_state src \<le> \<Down>Id (SPECT [ (False,[src\<mapsto>src],{src},{},0::nat) \<mapsto> init_state_time ])"
    shows "pre_bfs2 src dst \<le>\<Down>Id (pre_bfs src dst)"
  proof -
    have i: "\<And>t x. SPECT (emb (\<lambda>l. distinct l \<and> set l = E `` {x}) (enat t)) \<le> \<Down> (\<langle>Id\<rangle>list_set_rel) (SPECT [E``{x} \<mapsto> enat t])"
      apply(rule SPECT_refine)
      by(simp add: Some_eq_emb'_conv list_set_rel_def br_def)

    have ii: "\<And>t x. \<Down> (\<langle>Id\<rangle>list_set_rel) (SPECT [E``{x} \<mapsto> enat t]) \<le> SPECT (emb (\<lambda>l. distinct l \<and> set l = E `` {x}) (enat t))"
      using Sup_le_iff by (auto simp: conc_fun_def le_fun_def emb'_def list_set_rel_def br_def )       

    have rew: "\<And>tt x. SPECT (emb (\<lambda>l. distinct l \<and> set l = E `` {x}) (enat tt)) = \<Down> (\<langle>Id\<rangle>list_set_rel) (SPECT [E``{x} \<mapsto> enat tt])"
      apply(rule antisym) using i ii by auto

    have succ_impl': "\<And>v va. (v,va)\<in>Id \<Longrightarrow> va\<in>V \<Longrightarrow> succ v \<le> \<Down> (\<langle>nat_rel\<rangle>list_rel) (SPECT (emb (\<lambda>l. distinct l \<and> set l = E `` {va}) (enat (init_get_succs_list_time + (card (E `` {va}) + card (E\<inverse> `` {va})) * get_succs_list_time))))"
      unfolding rew apply simp apply(rule succ_impl) by auto  

    show ?thesis
    unfolding pre_bfs_def pre_bfs2_def monadic_WHILEIE_def
    apply (refine_rcg init_state_impl monadic_WHILE_refine loopguard_correct inner_loop2_correct succ_impl') 
                        apply refine_dref_type   
    by (auto split: if_splits  simp: distinct_in_list_set_rel)
 
  qed

end    
  

end \<comment> \<open>Pre_BFS_Impl\<close>

context Augmenting_Path_BFS
begin

  interpretation pre: Pre_BFS_Impl c set_insert_time map_dom_member_time  get_succs_list_time map_update_time set_pick_extract_time
    set_empty_time set_isempty_time init_state_time init_get_succs_list_time
    apply standard by simp 
     

    definition "bfs2 succ init_state src dst \<equiv> do {
      if src=dst then 
        RETURNT (Some [])
      else do {           
        br \<leftarrow> pre.pre_bfs2 succ init_state src dst;
        case br of
          None \<Rightarrow> RETURNT None
        | Some (d,PRED) \<Rightarrow> do {
            p \<leftarrow> extract_rpath  src dst PRED  map_lookup_time list_append_time V;
            RETURNT (Some p)
          }  
      }    
    }"
 

    lemma bfs2_refine:
      assumes succ_impl: "\<And>ui u. \<lbrakk>(ui,u)\<in>Id; u\<in>V\<rbrakk> 
        \<Longrightarrow> succ ui \<le> \<Down> (\<langle>Id\<rangle>list_set_rel) (SPECT [E``{u} \<mapsto> enat (init_get_succs_list_time + (card (E``{u}) + card (E\<inverse>``{u}))*get_succs_list_time)])"
          and init_state_impl: "\<And>src. init_state src \<le> SPECT [ (False,[src\<mapsto>src],{src},{},0::nat) \<mapsto> init_state_time ]"
      shows "bfs2 succ init_state src dst \<le> \<Down>Id (bfs src dst)"
      unfolding bfs_def bfs2_def
      apply auto
      apply(rule bindT_mono) 
       apply(rule pre.pre_bfs2_refine[simplified, OF succ_impl init_state_impl])  
      by (auto ) 
  end  \<comment> \<open>Augmenting_Path_BFS\<close>

end
