section \<open>Matrices by Array (Row-Major)\<close>
theory IICF_Array_Matrix
imports "../Intf/IICF_Matrix" (* Separation_Logic_Imperative_HOL.Array_Blit *)
begin

  definition is_amtx where [rewrite_ent]:   "is_amtx N M c mtx = (\<exists>\<^sub>Al. mtx \<mapsto>\<^sub>a l * \<up>( 
      length l = N*M 
    \<and> (\<forall>i<N. \<forall>j<M. l!(i*M+j) = c (i,j))
    \<and> (\<forall>i j. (i\<ge>N \<or> j\<ge>M) \<longrightarrow> c (i,j) = 0)))"

(*
  lemma is_amtx_precise[safe_constraint_rules]: "precise (is_amtx N M)"
    apply rule
    unfolding is_amtx_def
    apply clarsimp (* 
    apply prec_extract_eqs
    apply (rule ext)
    apply (rename_tac x)
    apply (case_tac x; simp)                                       
    apply (rename_tac i j)
    apply (case_tac "i<N"; case_tac "j<M"; simp)
    done *) sorry
*)
    
  lemma is_amtx_bounded:
    shows "rdomp (is_amtx N M) m \<Longrightarrow> mtx_nonzero m \<subseteq> {0..<N}\<times>{0..<M}"
    unfolding rdomp_def 
    apply (clarsimp simp: mtx_nonzero_def is_amtx_def)
    by (meson not_less)


  (*definition "mtx_new N M c \<equiv> do {
    Array_Time.make (N*M) (\<lambda>i. c (i div M, i mod M))
  }"*)


partial_function (heap_time) imp_for' :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> 'a \<Rightarrow> 'a Heap) \<Rightarrow> 'a \<Rightarrow> 'a Heap" where
  "imp_for' i u f s = (if i \<ge> u then return s else f i s \<bind> imp_for' (i + 1) u f)"

declare imp_for'.simps[code]

lemma imp_for'_simps[simp]:
  "i \<ge> u \<Longrightarrow> imp_for' i u f s = return s"
  "i < u \<Longrightarrow> imp_for' i u f s = f i s \<bind> imp_for' (i + 1) u f"
  by (auto simp: imp_for'.simps)

lemma "a=b \<Longrightarrow> timeCredit_assn a \<Longrightarrow>\<^sub>A timeCredit_assn b" by auto




lemma imp_for'_rule:
  assumes LESS: "l\<le>u" 
  assumes STEP: "\<And>i s. \<lbrakk> l\<le>i; i<u \<rbrakk> \<Longrightarrow> <I i s * timeCredit_assn t> f i s <I (i+1)>\<^sub>t"
  shows "<I l s * timeCredit_assn (t*(u-l)+1)> imp_for' l u f s <I u>\<^sub>t"
  using LESS 
proof (induction arbitrary: s rule: inc_induct)  
  case base thus ?case by auto2
next
  case (step k)
  then have f: "(t * (u - k)) = t + (t * (u - (k+1)))"  
    by (metis Suc_diff_Suc add.assoc add.commute mult_Suc_right plus_1_eq_Suc)  
  have s: "Suc k = k + 1" by simp
  show ?case                 
    using step.hyps 
    by (sep_auto heap: STEP step.IH[unfolded s] simp: f simp del: add_Suc One_nat_def)  
qed 


lemma imp_for'_rule':
  assumes LESS: "l\<le>u"
  assumes PRE: "P \<Longrightarrow>\<^sub>A I l s * timeCredit_assn (t*(u-l)+1)"
  assumes STEP: "\<And>i s. \<lbrakk> l\<le>i; i<u \<rbrakk> \<Longrightarrow> <I i s * timeCredit_assn t> f i s <I (i+1)>\<^sub>t"
  shows "<P> imp_for' l u f s <I u>\<^sub>t"
  apply (rule pre_rule[OF PRE])  
  apply(rule imp_for'_rule) by fact+


  definition "mtx_tabulate N M c \<equiv> do {
    m \<leftarrow> Array_Time.new (N*M) 0;
    (_,_,m) \<leftarrow> imp_for' 0 (N*M) (\<lambda>k (i,j,m). do {
      Array_Time.upd k (c (i,j)) m;
      let j=j+1;
      if j<M then return (i,j,m)
      else return (i+1,0,m)
    }) (0,0,m); 
    return m
  }"
      
      (*
  definition "amtx_copy \<equiv> array_copy"
*)

  definition [rewrite]: "amtx_dflt N M v = Array_Time.make (N*M) (\<lambda>i. v)"

  definition [rewrite]: "mtx_get M mtx e = Array_Time.nth mtx (fst e * M + snd e)"
  definition  [rewrite]: "mtx_set M mtx e v = Array_Time.upd (fst e * M + snd e) v mtx"


  lemma mtx_idx_unique_conv[simp]: 
    fixes M :: nat
    assumes "j<M" "j'<M"
    shows "(i * M + j = i' * M + j') \<longleftrightarrow> (i=i' \<and> j=j')"
    using assms  
    apply auto  
    subgoal
      by (metis add_right_cancel div_if div_mult_self3 linorder_neqE_nat not_less0)
    subgoal
      using \<open>\<lbrakk>j < M; j' < M; i * M + j = i' * M + j'\<rbrakk> \<Longrightarrow> i = i'\<close> by auto  
    done
      
  lemma mtx_index_unique[simp]: "\<lbrakk>i<(N::nat); j<M; i'<N; j'<M\<rbrakk> \<Longrightarrow> i*M+j = i'*M+j' \<longleftrightarrow> i=i' \<and> j=j'"
    by (metis ab_semigroup_add_class.add.commute add_diff_cancel_right' div_if div_mult_self3 gr0I not_less0)


  

declare [[print_trace]]
  
 
 


  lemma mtx_tabulate_rl[sep_heap_rules]:
    assumes NONZ: "mtx_nonzero c \<subseteq> {0..<N}\<times>{0..<M}"
    shows "<timeCredit_assn (N*M*3+3)> mtx_tabulate N M c <IICF_Array_Matrix.is_amtx N M c>\<^sub>t"
  proof (cases "M=0")
    case True thus ?thesis
      unfolding mtx_tabulate_def  
      using mtx_nonzeroD[OF _ NONZ]
      by (sep_auto simp: is_amtx_def zero_time simp del: add_Suc One_nat_def add_2_eq_Suc') 
  next
    case False hence M_POS: "0<M" by auto
    show ?thesis
      unfolding mtx_tabulate_def  
apply (sep_auto 
        decon: 
          imp_for'_rule'[where 
            I="\<lambda>k (i,j,mi). \<exists>\<^sub>Am. mi \<mapsto>\<^sub>a m 
            * \<up>( k=i*M+j \<and> j<M \<and> k\<le>N*M \<and> length m = N*M )
            * \<up>( \<forall>i'<i. \<forall>j<M. m!(i'*M+j) = c (i',j) )
            * \<up>( \<forall>j'<j. m!(i*M+j') = c (i,j') )* timeCredit_assn 1 " and t="2"
          ]    
        simp: nth_list_update M_POS dest: Suc_lessI simp del: One_nat_def add_2_eq_Suc'
      ) (* the setup is wrong here, somehow I need to ensure that
            within $ expressions, natural numbers are not rewritten,
            but the simplification rules should be applied when solving side-conditions
          *)
        (* apply (auto  simp del: One_nat_def add_2_eq_Suc') [] *) apply auto[]
          apply auto[]
       apply (auto simp: nth_list_update M_POS dest: Suc_lessI)[]
      apply (sep_auto)
      unfolding is_amtx_def
      using mtx_nonzeroD[OF _ NONZ] 
      apply sep_auto  
      by (metis add.right_neutral M_POS mtx_idx_unique_conv) 
  qed
  

(*
  lemma mtx_copy_rl[sep_heap_rules]:
    "<is_amtx N M c mtx> amtx_copy mtx <\<lambda>r. is_amtx N M c mtx * is_amtx N M c r>"
    by (sep_auto simp: amtx_copy_def is_amtx_def)
*)

  definition "PRES_ZERO_UNIQUE A \<equiv> (A``{0}={0} \<and> A\<inverse>``{0} = {0})"
  lemma IS_ID_imp_PRES_ZERO_UNIQUE[constraint_rules]: "IS_ID A \<Longrightarrow> PRES_ZERO_UNIQUE A"
    unfolding IS_ID_def PRES_ZERO_UNIQUE_def by auto

  definition op_amtx_dfltNxM :: "nat \<Rightarrow> nat \<Rightarrow> 'a::zero \<Rightarrow> nat\<times>nat\<Rightarrow>'a" where
    [simp]: "op_amtx_dfltNxM N M v = (\<lambda>(i,j). if i<N \<and> j<M then v else 0)"

lemma opt_amtx_dfltNxM[rewrite]: "op_amtx_dfltNxM N M v (i,j) = (if i<N \<and> j<M then v else 0)"
  unfolding op_amtx_dfltNxM_def by simp

(*
context fixes N M::nat begin  
  sepref_decl_op (no_def) op_amtx_dfltNxM: "op_amtx_dfltNxM N M" :: "A \<rightarrow> \<langle>A\<rangle>mtx_rel"
    where "CONSTRAINT PRES_ZERO_UNIQUE A"
    apply (rule fref_ncI) unfolding op_amtx_dfltNxM_def[abs_def] mtx_rel_def
    apply parametricity
    by (auto simp add: PRES_ZERO_UNIQUE_def)
end  
*)

declare [[print_trace]]
 
lemma "length [0..<N * M] = N * M" by auto2
lemma "i< length[0..<N] \<Longrightarrow> map (\<lambda>i. k) [0..<N] ! i = k" by auto2
lemma "i<   N \<Longrightarrow> map (\<lambda>i. k) [0..<N] ! i = k" 
@proof
  @have "i< length [0..<N]"
@qed
declare upt_zero_length [rewrite_arg]
lemma "i<   N*M \<Longrightarrow> map (\<lambda>i. k) [0..<N*M] ! i = k"  by auto2
 


lemma mtx_idx_valid[simp,backward]: "\<lbrakk>i < (N::nat); j < M\<rbrakk> \<Longrightarrow> i * M + j < N * M"
  by (rule mlex_bound)
lemma "i<N \<Longrightarrow> j<M \<Longrightarrow>    map (\<lambda>i. k) [0..<N * M] ! (i * M + j) = k"
@proof
 @have "i * M + j < N*M"  
@qed

lemma "i<N \<Longrightarrow> j<M \<Longrightarrow>  map (\<lambda>i. k) [0..<N * M] ! (i * M + j) = (if i < N \<and> j < M then k else 0)"
@proof
 @have "i * M + j < N*M"  
  oops

  lemma mtx_dflt_rl: "<timeCredit_assn (N*M+1)> amtx_dflt N M k <is_amtx N M (op_amtx_dfltNxM N M k)>"
    (* by (sep_auto simp: amtx_dflt_def is_amtx_def) *) 
    by auto2

  lemma ij[backward]: "i<N \<Longrightarrow> j<M \<Longrightarrow> i * M + j < N* (M::nat)" by auto2

  lemma mtx_get_rl': "\<lbrakk>i<N; j<M \<rbrakk> \<Longrightarrow> <timeCredit_assn 1 * is_amtx N M c mtx> mtx_get M mtx (i,j) <\<lambda>r. is_amtx N M c mtx * \<up>(r = c (i,j))>"
    by auto2
  lemma mtx_get_rl: "\<lbrakk>fst k<N; snd k<M \<rbrakk> \<Longrightarrow> <timeCredit_assn 1 * is_amtx N M c mtx> mtx_get M mtx k <\<lambda>r. is_amtx N M c mtx * \<up>(r = c k)>"
    by auto2


lemma "n<length l \<Longrightarrow> l[n:=1] ! n = 1" by auto2
 
lemma "i<N \<Longrightarrow> j<M \<Longrightarrow> ia<N \<Longrightarrow> ja<M \<Longrightarrow> length l = N * M \<Longrightarrow>
      l[i * M + j := v] ! (ia * M + ja) = (if i * M + j = ia * M + ja then v else l ! (ia * M + ja))"
@proof 
  @have "ia * M + ja < length l" 
  @qed

lemma "j<J \<Longrightarrow> snd (i, j) < J " by auto2

lemma a[rewrite]: "length l = N * M \<Longrightarrow> ia<N \<Longrightarrow> ja<M \<Longrightarrow> l[k := v] ! (ia * M + ja) = (if k = ia * M + ja then v else l ! (ia * M + ja))"
@proof 
  @have "ia * M + ja < length l"
@qed 

  thm nth_list_update
  thm sep_heap_rules
  lemma mtx_set_rl': "\<lbrakk>i<N; j<M \<rbrakk> 
    \<Longrightarrow> <timeCredit_assn 1 * is_amtx N M c mtx> mtx_set M mtx (i,j) v <\<lambda>r. is_amtx N M (c((i,j) := v)) r>"
    unfolding mtx_set_def is_amtx_def
    by (sep_auto simp del: One_nat_def) 

  lemma mtx_set_rl: "\<lbrakk>fst k<N; snd k<M \<rbrakk> 
    \<Longrightarrow> <timeCredit_assn 1 * is_amtx N M c mtx> mtx_set M mtx k v <\<lambda>r. is_amtx N M (c(k := v)) r>"
    using mtx_set_rl' 
    by force


  definition "amtx_assn N M A \<equiv> hr_comp (is_amtx N M) (\<langle>the_pure A\<rangle>mtx_rel)"
  lemmas [fcomp_norm_unfold] = amtx_assn_def[symmetric]
  lemmas [safe_constraint_rules] = CN_FALSEI[of is_pure "amtx_assn N M A" for N M A]

  lemma [intf_of_assn]: "intf_of_assn A TYPE('a) \<Longrightarrow> intf_of_assn (amtx_assn N M A) TYPE('a i_mtx)"
    by simp

  abbreviation "asmtx_assn N A \<equiv> amtx_assn N N A"  

  lemma mtx_rel_pres_zero:
    assumes "PRES_ZERO_UNIQUE A" 
    assumes "(m,m')\<in>\<langle>A\<rangle>mtx_rel"
    shows "m ij = 0 \<longleftrightarrow> m' ij = 0"
    using assms
    apply1 (clarsimp simp: IS_PURE_def PRES_ZERO_UNIQUE_def is_pure_conv mtx_rel_def)
    apply (drule fun_relD) applyS (rule IdI[of ij]) applyS auto
    done
    

  lemma amtx_assn_bounded:
    assumes "CONSTRAINT (IS_PURE PRES_ZERO_UNIQUE) A"
    shows "rdomp (amtx_assn N M A) m \<Longrightarrow> mtx_nonzero m \<subseteq> {0..<N}\<times>{0..<M}"
    apply (clarsimp simp: mtx_nonzero_def amtx_assn_def rdomp_hrcomp_conv)
    apply (drule is_amtx_bounded)
    using assms
    by (fastforce simp: IS_PURE_def is_pure_conv mtx_rel_pres_zero[symmetric] mtx_nonzero_def)
(*
  lemma mtx_tabulate_aref: 
    "(mtx_tabulate N M, RETURN o op_mtx_new) 
      \<in> [\<lambda>c. mtx_nonzero c \<subseteq> {0..<N}\<times>{0..<M}]\<^sub>a id_assn\<^sup>k \<rightarrow> IICF_Array_Matrix.is_amtx N M"  
    by sepref_to_hoare sep_auto
        
  lemma mtx_copy_aref: 
    "(amtx_copy, RETURN o op_mtx_copy) \<in> (is_amtx N M)\<^sup>k \<rightarrow>\<^sub>a is_amtx N M"  
    apply rule apply rule
    apply (sep_auto simp: pure_def)
    done
*)
  lemma mtx_nonzero_bid_eq:
    assumes "R\<subseteq>Id"
    assumes "(a, a') \<in> Id \<rightarrow> R" 
    shows "mtx_nonzero a = mtx_nonzero a'"
    using assms
    apply (clarsimp simp: mtx_nonzero_def)
    apply (metis fun_relE2 pair_in_Id_conv subsetCE)
    done

  lemma mtx_nonzero_zu_eq:
    assumes "PRES_ZERO_UNIQUE R"
    assumes "(a, a') \<in> Id \<rightarrow> R" 
    shows "mtx_nonzero a = mtx_nonzero a'"
    using assms
    apply (clarsimp simp: mtx_nonzero_def PRES_ZERO_UNIQUE_def)
    by (metis (no_types, hide_lams) IdI Image_singleton_iff converse_iff singletonD tagged_fun_relD_none)



  subsection "implementation of interface"

  thm mtx_set_rl

lemma p: "the_pure id_assn = Id" by simp

lemma extractpureD: "h \<Turnstile> pure R a c * F \<Longrightarrow> (c,a) \<in> R \<and> h \<Turnstile> F"
  by (simp add: pure_def)
  
 

lemma mop_matrix_update_rule[sepref_fr_rules]:
  "1 \<le> t  \<Longrightarrow> fst k' < M \<Longrightarrow> snd k' < M \<Longrightarrow>
      hn_refine (hn_val Id v' v * hn_val Id k' k * hn_ctxt (asmtx_assn M (pure Id)) m' m)
       (PR_CONST (mtx_set M) m k v)                                                             
       (hn_val Id v' v * hn_val Id k' k * hn_invalid (asmtx_assn M (pure Id)) m' m) (asmtx_assn M (pure Id)) ( PR_CONST (mop_matrix_set t) $ m' $ k' $ v')"
  apply(rule  hn_refine_preI)
  unfolding mop_matrix_set_def autoref_tag_defs
  apply (rule extract_cost_otherway[OF _  mtx_set_rl, where F="hn_val Id v' v * hn_val Id k' k * hn_invalid (asmtx_assn M (pure Id)) m' m" ])


  oops

lemma mop_matrix_update_rule[sepref_fr_rules]:
  "1 \<le> t  \<Longrightarrow> fst k' < M \<Longrightarrow> snd k' < M \<Longrightarrow>
      hn_refine (hn_val Id v' v * hn_ctxt (prod_assn id_assn id_assn) k' k * hn_ctxt (asmtx_assn M (pure Id)) m' m)
       (PR_CONST (mtx_set M) m k v)                                                             
       (hn_val Id v' v * hn_ctxt (prod_assn id_assn id_assn) k' k * hn_invalid (asmtx_assn M (pure Id)) m' m) (asmtx_assn M (pure Id)) ( PR_CONST (mop_matrix_set t) $ m' $ k' $ v')"
  apply(rule  hn_refine_preI)
  unfolding mop_matrix_set_def autoref_tag_defs
  apply (rule extract_cost_otherway[OF _  mtx_set_rl, where F="hn_val Id v' v * hn_val Id k' k * hn_invalid (asmtx_assn M (pure Id)) m' m" ])
  unfolding mult.assoc
    apply(rotatel) apply(rotatel)
    apply rotater apply rotater apply rotater apply rotater   apply swapr    apply taker apply(rule isolate_first)
       apply (simp add: gr_def hn_ctxt_def) apply(rule ent_trans) 
        apply(rule invalidate_clone[where R="asmtx_assn M id_assn"]) apply(rule match_first)
   unfolding amtx_assn_def  apply simp  apply (rule entails_triv)
   unfolding hn_ctxt_def apply(rotatel)
      
       apply(rule match_first) apply(rule isolate_first)
        subgoal by simp
        apply (rule entails_triv)
  subgoal by(auto dest: extractpureD)  
  subgoal by(auto dest: extractpureD)  
  subgoal apply rotatel apply rotatel apply rotatel apply rotater apply rotater apply (rule match_first) apply simp
    apply(simp only: ex_distrib_star' pure_def hr_comp_def)
    apply(auto simp add: ex_distrib_star')
    apply(rule ent_ex_postI[where x="m'(k' := v')"]) by simp   
  subgoal by simp
  done
 

lemma mop_matrix_get_rule[sepref_fr_rules]:
  "1 \<le> t \<Longrightarrow> fst k' < M \<Longrightarrow> snd k' < M \<Longrightarrow>
    hn_refine (hn_ctxt (prod_assn id_assn id_assn) k' k * hn_ctxt (asmtx_assn M (pure Id)) m' m)
    (PR_CONST (mtx_get M) m k)      
     (hn_ctxt (prod_assn id_assn id_assn) k' k* hn_ctxt (asmtx_assn M (pure Id)) m' m) id_assn ( PR_CONST (mop_matrix_get t) $ m' $ k')"
  apply(rule  hn_refine_preI)
  unfolding autoref_tag_defs mop_matrix_get_def
  apply (rule extract_cost_otherway[OF _  mtx_get_rl]) unfolding mult.assoc
  unfolding hn_ctxt_def
    apply rotatel apply rotatel apply(rule match_first) apply rotater apply(rule match_first)       
      apply(simp add: amtx_assn_def) apply (rule entails_triv)
  subgoal by(auto dest: extractpureD)  
  subgoal by(auto dest: extractpureD)  
  subgoal 
    apply rotater  unfolding amtx_assn_def
      apply (simp add:  ) apply (simp add: pure_def  )    apply safe
    apply(rule inst_ex_assn[where x="m' k'"]) by (auto simp: ) 
    subgoal by auto 
    done




(*
  lemma op_mtx_new_fref': 
    "CONSTRAINT PRES_ZERO_UNIQUE A \<Longrightarrow> (RETURN \<circ> op_mtx_new, RETURN \<circ> op_mtx_new) \<in> (nat_rel \<times>\<^sub>r nat_rel \<rightarrow> A) \<rightarrow>\<^sub>f \<langle>\<langle>A\<rangle>mtx_rel\<rangle>nrest_rel"
    by (rule op_mtx_new.fref)
    

  sepref_decl_impl (no_register) amtx_new_by_tab: mtx_tabulate_aref uses op_mtx_new_fref'
    by (auto simp: mtx_nonzero_zu_eq)

  sepref_decl_impl amtx_copy: mtx_copy_aref .
   *) 
  definition [simp]: "op_amtx_new (N::nat) (M::nat) \<equiv> op_mtx_new"  
(*  lemma amtx_fold_custom_new:
    "op_mtx_new \<equiv> op_amtx_new N M"
    apply simp done
 
    "mop_mtx_new \<equiv> \<lambda>c. RETURN (op_amtx_new N M c)"
    by (auto simp: mop_mtx_new_alt[abs_def]) *)



context fixes N M :: nat
    and t :: "nat \<Rightarrow> nat \<Rightarrow> nat"  
    begin

    definition "mop_amtx_new c =  SPECT [op_amtx_new N M c \<mapsto> t N M] "


    sepref_register "mop_amtx_new"


  end


  lemma is_amtx_impl_amtx_assn: "(xi, x) \<in> Id \<rightarrow> the_pure A \<Longrightarrow> is_amtx N M xi r \<Longrightarrow>\<^sub>A amtx_assn N M A x r"  
    by (simp add: hr_compI mtx_rel_def amtx_assn_def)  

  lemma amtx_new_hnr[sepref_fr_rules]: 
    fixes A :: "'a::zero \<Rightarrow> 'b::{zero,heap} \<Rightarrow> assn"
    shows "CONSTRAINT (IS_PURE PRES_ZERO_UNIQUE) A \<Longrightarrow>
      N*M*3+3 \<le> t N M    \<Longrightarrow>
    (mtx_tabulate N M, ( PR_CONST (mop_amtx_new N M t)))
    \<in> [\<lambda>x. mtx_nonzero x \<subseteq> {0..<N} \<times> {0..<M}]\<^sub>a (pure (nat_rel \<times>\<^sub>r nat_rel \<rightarrow> the_pure A))\<^sup>k \<rightarrow> amtx_assn N M A"
    apply sepref_to_hoare
    apply(rule hn_refine_preI)    
    unfolding autoref_tag_defs constraint_abbrevs   mop_amtx_new_def 
    subgoal for x xi
      apply (rule extract_cost_otherway[OF _  mtx_tabulate_rl, where F = "\<up> ((xi, x) \<in> nat_rel \<times>\<^sub>r nat_rel \<rightarrow> the_pure A)"])
         apply sep_auto
          subgoal by (auto dest: mtx_nonzero_zu_eq)  
      subgoal  apply sep_auto apply(rule isolate_first) apply(rule is_amtx_impl_amtx_assn) by auto  
        subgoal by auto
        done
      done
   (*
    lemma amtx_fold_custom_new:
        "\<And>c tt. SPECT [op_mtx_new c \<mapsto> tt N] =  mop_amtx_new N M (\<lambda>N M. tt N N) c" by(auto simp: mop_amtx_new_def)
 *)
(*
  lemma [def_pat_rules]: "op_amtx_new$N$M \<equiv> UNPROTECT (op_amtx_new N M)" by simp


  context fixes N M :: nat notes [param] = IdI[of N] IdI[of M] begin  

    lemma mtx_dflt_aref: 
      "(amtx_dflt N M, RETURN o PR_CONST (op_amtx_dfltNxM N M)) \<in> id_assn\<^sup>k \<rightarrow>\<^sub>a is_amtx N M"  
      apply rule apply rule
      apply (sep_auto simp: pure_def)
      done
    sepref_decl_impl amtx_dflt: mtx_dflt_aref . 

    lemma amtx_get_aref: 
      "(uncurry (mtx_get M), uncurry (RETURN oo op_mtx_get)) \<in> [\<lambda>(_,(i,j)). i<N \<and> j<M]\<^sub>a (is_amtx N M)\<^sup>k *\<^sub>a (prod_assn nat_assn nat_assn)\<^sup>k \<rightarrow> id_assn"
      apply rule apply rule
      apply (sep_auto simp: pure_def)
      done
    sepref_decl_impl amtx_get: amtx_get_aref .
    
    lemma amtx_set_aref: "(uncurry2 (mtx_set M), uncurry2 (RETURN ooo op_mtx_set)) 
      \<in> [\<lambda>((_,(i,j)),_). i<N \<and> j<M]\<^sub>a (is_amtx N M)\<^sup>d *\<^sub>a (prod_assn nat_assn nat_assn)\<^sup>k *\<^sub>a id_assn\<^sup>k \<rightarrow> is_amtx N M"
      apply rule apply (rule hn_refine_preI) apply rule
      apply (sep_auto simp: pure_def hn_ctxt_def invalid_assn_def)
      done
  
    sepref_decl_impl amtx_set: amtx_set_aref .

    lemma amtx_get_aref': 
      "(uncurry (mtx_get M), uncurry (RETURN oo op_mtx_get)) \<in> (is_amtx N M)\<^sup>k *\<^sub>a (prod_assn (pure (nbn_rel N)) (pure (nbn_rel M)))\<^sup>k \<rightarrow>\<^sub>a id_assn"
      apply rule apply rule
      apply (sep_auto simp: pure_def IS_PURE_def IS_ID_def)
      done

    sepref_decl_impl amtx_get': amtx_get_aref' .
      
    lemma amtx_set_aref': "(uncurry2 (mtx_set M), uncurry2 (RETURN ooo op_mtx_set)) 
      \<in> (is_amtx N M)\<^sup>d *\<^sub>a (prod_assn (pure (nbn_rel N)) (pure (nbn_rel M)))\<^sup>k *\<^sub>a id_assn\<^sup>k \<rightarrow>\<^sub>a is_amtx N M"
      apply rule apply (rule hn_refine_preI) apply rule
      apply (sep_auto simp: pure_def hn_ctxt_def invalid_assn_def IS_PURE_def IS_ID_def)
      done

    sepref_decl_impl amtx_set': amtx_set_aref' .

  end  

  subsection \<open>Pointwise Operations\<close>
  context
    fixes M N :: nat
  begin
    sepref_decl_op amtx_lin_get: "\<lambda>f i. op_mtx_get f (i div M, i mod M)" :: "\<langle>A\<rangle>mtx_rel \<rightarrow> nat_rel \<rightarrow> A"
      unfolding op_mtx_get_def mtx_rel_def
      by (rule frefI) (parametricity; simp)
  
    sepref_decl_op amtx_lin_set: "\<lambda>f i x. op_mtx_set f (i div M, i mod M) x" :: "\<langle>A\<rangle>mtx_rel \<rightarrow> nat_rel \<rightarrow> A \<rightarrow> \<langle>A\<rangle>mtx_rel"
      unfolding op_mtx_set_def mtx_rel_def
      apply (rule frefI) apply parametricity by simp_all

    lemma op_amtx_lin_get_aref: "(uncurry Array_Time.nth, uncurry (RETURN oo PR_CONST op_amtx_lin_get)) \<in> [\<lambda>(_,i). i<N*M]\<^sub>a (is_amtx N M)\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> id_assn"  
      apply sepref_to_hoare
      unfolding is_amtx_def     
      apply sep_auto
      apply (metis mult.commute div_eq_0_iff div_mult2_eq div_mult_mod_eq mod_less_divisor mult_is_0 not_less0)
      done
  
    sepref_decl_impl amtx_lin_get: op_amtx_lin_get_aref by auto 
    
    lemma op_amtx_lin_set_aref: "(uncurry2 (\<lambda>m i x. Array_Time.upd i x m), uncurry2 (RETURN ooo PR_CONST op_amtx_lin_set)) \<in> [\<lambda>((_,i),_). i<N*M]\<^sub>a (is_amtx N M)\<^sup>d *\<^sub>a nat_assn\<^sup>k *\<^sub>a id_assn\<^sup>k \<rightarrow> is_amtx N M"  
    proof -
      have [simp]: "i < N * M \<Longrightarrow> \<not>(M \<le> i mod M)" for i
        by (cases "N = 0 \<or> M = 0") (auto simp add: not_le) 
      have [simp]: "i < N * M \<Longrightarrow> \<not>(N \<le> i div M)" for i
        apply (cases "N = 0 \<or> M = 0")
         apply (auto simp add: not_le)
        apply (metis mult.commute div_eq_0_iff div_mult2_eq neq0_conv)
        done
      show ?thesis  
        apply sepref_to_hoare
        unfolding is_amtx_def     
        by (sep_auto simp: nth_list_update)
    qed    

    sepref_decl_impl amtx_lin_set: op_amtx_lin_set_aref by auto 
  end

  lemma amtx_fold_lin_get: "m (i div M, i mod M) = op_amtx_lin_get M m i" by simp
  lemma amtx_fold_lin_set: "m ((i div M, i mod M) := x) = op_amtx_lin_set M m i x" by simp



  locale amtx_pointwise_unop_impl = mtx_pointwise_unop_loc +
    fixes A :: "'a \<Rightarrow> 'ai::{zero,heap} \<Rightarrow> assn"
    fixes fi :: "nat\<times>nat \<Rightarrow> 'ai \<Rightarrow> 'ai Heap"
    assumes fi_hnr:
      "(uncurry fi,uncurry (RETURN oo f)) \<in> (prod_assn nat_assn nat_assn)\<^sup>k *\<^sub>a A\<^sup>k \<rightarrow>\<^sub>a A"  
  begin

    lemma this_loc: "amtx_pointwise_unop_impl N M f A fi" by unfold_locales

    context
      assumes PURE: "CONSTRAINT (IS_PURE PRES_ZERO_UNIQUE) A"
    begin  
      context 
        notes [[sepref_register_adhoc f N M]]
        notes [sepref_import_param] = IdI[of N] IdI[of M]
        notes [sepref_fr_rules] = fi_hnr
        notes [safe_constraint_rules] = PURE
        notes [simp] = algebra_simps
      begin
        sepref_thm opr_fold_impl1 is "RETURN o opr_fold_impl" :: "(amtx_assn N M A)\<^sup>d \<rightarrow>\<^sub>a amtx_assn N M A"
          unfolding opr_fold_impl_def fold_prod_divmod_conv'
          apply (rewrite amtx_fold_lin_set)
          apply (rewrite in "f _ \<hole>" amtx_fold_lin_get)
          by sepref
      end    
    end  
    concrete_definition (in -) amtx_pointwise_unnop_fold_impl1 uses amtx_pointwise_unop_impl.opr_fold_impl1.refine_raw
    prepare_code_thms (in -) amtx_pointwise_unnop_fold_impl1_def
  
    lemma op_hnr[sepref_fr_rules]: 
      assumes PURE: "CONSTRAINT (IS_PURE PRES_ZERO_UNIQUE) A"
      shows "(amtx_pointwise_unnop_fold_impl1 N M fi, RETURN \<circ> PR_CONST (mtx_pointwise_unop f)) \<in> (amtx_assn N M A)\<^sup>d \<rightarrow>\<^sub>a amtx_assn N M A"
      unfolding PR_CONST_def
      apply (rule hfref_weaken_pre'[OF _ amtx_pointwise_unnop_fold_impl1.refine[OF this_loc PURE,FCOMP opr_fold_impl_refine]])
      by (simp add: amtx_assn_bounded[OF PURE])
  end    


  locale amtx_pointwise_binop_impl = mtx_pointwise_binop_loc +
    fixes A :: "'a \<Rightarrow> 'ai::{zero,heap} \<Rightarrow> assn"
    fixes fi :: "'ai \<Rightarrow> 'ai \<Rightarrow> 'ai Heap"
    assumes fi_hnr: "(uncurry fi,uncurry (RETURN oo f)) \<in> A\<^sup>k *\<^sub>a A\<^sup>k \<rightarrow>\<^sub>a A"  
  begin
  
    lemma this_loc: "amtx_pointwise_binop_impl f A fi"
      by unfold_locales
  
    context 
      notes [[sepref_register_adhoc f N M]]
      notes [sepref_import_param] = IdI[of N] IdI[of M]
      notes [sepref_fr_rules] = fi_hnr
      assumes PURE[safe_constraint_rules]: "CONSTRAINT (IS_PURE PRES_ZERO_UNIQUE) A"
      notes [simp] = algebra_simps
    begin
      sepref_thm opr_fold_impl1 is "uncurry (RETURN oo opr_fold_impl)" :: "(amtx_assn N M A)\<^sup>d*\<^sub>a(amtx_assn N M A)\<^sup>k \<rightarrow>\<^sub>a amtx_assn N M A"
        unfolding opr_fold_impl_def[abs_def] fold_prod_divmod_conv'
        apply (rewrite amtx_fold_lin_set)
        apply (rewrite in "f \<hole> _" amtx_fold_lin_get)
        apply (rewrite in "f _ \<hole>" amtx_fold_lin_get)
        by sepref
        
    end    
  
    concrete_definition (in -) amtx_pointwise_binop_fold_impl1 for fi N M
      uses amtx_pointwise_binop_impl.opr_fold_impl1.refine_raw is "(uncurry ?f,_)\<in>_"
    prepare_code_thms (in -) amtx_pointwise_binop_fold_impl1_def
  
    lemma op_hnr[sepref_fr_rules]: 
      assumes PURE: "CONSTRAINT (IS_PURE PRES_ZERO_UNIQUE) A"
      shows "(uncurry (amtx_pointwise_binop_fold_impl1 fi N M), uncurry (RETURN oo PR_CONST (mtx_pointwise_binop f))) \<in> (amtx_assn N M A)\<^sup>d *\<^sub>a (amtx_assn N M A)\<^sup>k \<rightarrow>\<^sub>a amtx_assn N M A"
      unfolding PR_CONST_def
      apply (rule hfref_weaken_pre'[OF _ amtx_pointwise_binop_fold_impl1.refine[OF this_loc PURE,FCOMP opr_fold_impl_refine]])
      apply (auto dest: amtx_assn_bounded[OF PURE])
      done
  
  end

  locale amtx_pointwise_cmpop_impl = mtx_pointwise_cmpop_loc +
    fixes A :: "'a \<Rightarrow> 'ai::{zero,heap} \<Rightarrow> assn"
    fixes fi :: "'ai \<Rightarrow> 'ai \<Rightarrow> bool Heap"
    fixes gi :: "'ai \<Rightarrow> 'ai \<Rightarrow> bool Heap"
    assumes fi_hnr:
      "(uncurry fi,uncurry (RETURN oo f)) \<in> A\<^sup>k *\<^sub>a A\<^sup>k \<rightarrow>\<^sub>a bool_assn"  
    assumes gi_hnr:
      "(uncurry gi,uncurry (RETURN oo g)) \<in> A\<^sup>k *\<^sub>a A\<^sup>k \<rightarrow>\<^sub>a bool_assn"  
  begin
  
    lemma this_loc: "amtx_pointwise_cmpop_impl f g A fi gi"
      by unfold_locales
  
    context 
      notes [[sepref_register_adhoc f g N M]]
      notes [sepref_import_param] = IdI[of N] IdI[of M]
      notes [sepref_fr_rules] = fi_hnr gi_hnr
      assumes PURE[safe_constraint_rules]: "CONSTRAINT (IS_PURE PRES_ZERO_UNIQUE) A"
    begin
      sepref_thm opr_fold_impl1 is "uncurry opr_fold_impl" :: "(amtx_assn N M A)\<^sup>d*\<^sub>a(amtx_assn N M A)\<^sup>k \<rightarrow>\<^sub>a bool_assn"
        unfolding opr_fold_impl_def[abs_def] nfoldli_prod_divmod_conv
        apply (rewrite in "f \<hole> _" amtx_fold_lin_get)
        apply (rewrite in "f _ \<hole>" amtx_fold_lin_get)
        apply (rewrite in "g \<hole> _" amtx_fold_lin_get)
        apply (rewrite in "g _ \<hole>" amtx_fold_lin_get)
        by sepref        
    end    
  
    concrete_definition (in -) amtx_pointwise_cmpop_fold_impl1 for N M fi gi
      uses amtx_pointwise_cmpop_impl.opr_fold_impl1.refine_raw is "(uncurry ?f,_)\<in>_"
    prepare_code_thms (in -) amtx_pointwise_cmpop_fold_impl1_def
  
    lemma op_hnr[sepref_fr_rules]: 
      assumes PURE: "CONSTRAINT (IS_PURE PRES_ZERO_UNIQUE) A"
      shows "(uncurry (amtx_pointwise_cmpop_fold_impl1 N M fi gi), uncurry (RETURN oo PR_CONST (mtx_pointwise_cmpop f g))) \<in> (amtx_assn N M A)\<^sup>d *\<^sub>a (amtx_assn N M A)\<^sup>k \<rightarrow>\<^sub>a bool_assn"
      unfolding PR_CONST_def
      apply (rule hfref_weaken_pre'[OF _ amtx_pointwise_cmpop_fold_impl1.refine[OF this_loc PURE,FCOMP opr_fold_impl_refine]])
      apply (auto dest: amtx_assn_bounded[OF PURE])
      done
  
  end


  subsection \<open>Regression Test and Usage Example\<close>

  context begin
    text \<open>To work with a matrix, the dimension should be fixed in a context\<close>
    context
      fixes N M :: nat
      \<comment> \<open>We also register the dimension as an operation, such that we can 
        use it like a constant\<close>
      notes [[sepref_register_adhoc N M]] 
      notes [sepref_import_param] = IdI[of N] IdI[of M]
      \<comment> \<open>Finally, we fix a type variable with the required type classes for matrix entries\<close>
      fixes dummy:: "'a::{times,zero,heap}"
    begin

      text \<open>First, we implement scalar multiplication with destructive update 
        of the matrix:\<close>
      private definition scmul :: "'a \<Rightarrow> 'a mtx \<Rightarrow> 'a mtx nres" where
        "scmul x m \<equiv> nfoldli [0..<N] (\<lambda>_. True) (\<lambda>i m. 
          nfoldli [0..<M] (\<lambda>_. True) (\<lambda>j m. do {
              let mij = m(i,j);
              RETURN (m((i,j) := x * mij))
            }
          ) m
        ) m"
    
      text \<open>After declaration of an implementation for multiplication,
        refinement is straightforward. Note that we use the fixed @{term N} in
        the refinement assertions.\<close>
      private lemma times_param: "(( * ),( * )::'a\<Rightarrow>_) \<in> Id \<rightarrow> Id \<rightarrow> Id" by simp
  
      context
        notes [sepref_import_param] = times_param
      begin
        sepref_definition scmul_impl 
          is "uncurry scmul" :: "(id_assn\<^sup>k *\<^sub>a (amtx_assn N M id_assn)\<^sup>d \<rightarrow>\<^sub>a amtx_assn N M id_assn)"
          unfolding scmul_def[abs_def]
          by sepref
      end    

      text \<open>Initialization with default value\<close>
      private definition "init_test \<equiv> do {
        let m = op_amtx_dfltNxM 10 5 (0::nat);
        RETURN (m(1,2))
      }"
      private sepref_definition init_test_impl is "uncurry0 init_test" :: "unit_assn\<^sup>k\<rightarrow>\<^sub>anat_assn"
        unfolding init_test_def
        by sepref

      text \<open>Initialization from function diagonal is more complicated:
        First, we have to define the function as a new constant\<close>  
      (* TODO: PR_CONST option for sepref-register! *)  
      qualified definition "diagonalN k \<equiv> \<lambda>(i,j). if i=j \<and> j<N then k else 0"  
      text \<open>If it carries implicit parameters, we have to wrap it into a @{term PR_CONST} tag:\<close>
      private sepref_register "PR_CONST diagonalN"
      private lemma [def_pat_rules]: "IICF_Array_Matrix.diagonalN$N \<equiv> UNPROTECT diagonalN" by simp

      text \<open>Then, we have to implement the constant, where the result assertion must be for a 
        pure function. Note that, due to technical reasons, we need the \<open>the_pure\<close> in the function type,
        and the refinement rule to be parameterized over an assertion variable (here \<open>A\<close>).
        Of course, you can constrain \<open>A\<close> further, e.g., @{term "CONSTRAINT (IS_PURE IS_ID) (A::int \<Rightarrow> int \<Rightarrow> assn)"}
        \<close>      
      private lemma diagonalN_hnr[sepref_fr_rules]:
        assumes "CONSTRAINT (IS_PURE PRES_ZERO_UNIQUE) A"
        (*assumes "CONSTRAINT (IS_PURE IS_ID) (A::int \<Rightarrow> int \<Rightarrow> assn)"*)
        shows "(return o diagonalN, RETURN o (PR_CONST diagonalN)) \<in> A\<^sup>k \<rightarrow>\<^sub>a pure (nat_rel \<times>\<^sub>r nat_rel \<rightarrow> the_pure A)"
        using assms
        apply sepref_to_hoare
        apply (sep_auto simp: diagonalN_def is_pure_conv IS_PURE_def PRES_ZERO_UNIQUE_def (*IS_ID_def*))
        done

      text \<open>In order to discharge preconditions, we need to prove some auxiliary lemma 
        that non-zero indexes are within range\<close>
      lemma diagonal_nonzero_ltN[simp]: "(a,b)\<in>mtx_nonzero (diagonalN k) \<Longrightarrow> a<N \<and> b<N"  
        by (auto simp: mtx_nonzero_def diagonalN_def split: if_split_asm)

      private definition "init_test2 \<equiv> do {
        ASSERT (N>2); \<comment> \<open>Ensure that the coordinate \<open>(1,2)\<close> is valid\<close>
        let m = op_mtx_new (diagonalN (1::int));
        RETURN (m(1,2))
      }"
      private sepref_definition init_test2_impl is "uncurry0 init_test2" :: "unit_assn\<^sup>k\<rightarrow>\<^sub>aint_assn"
        unfolding init_test2_def amtx_fold_custom_new[of N N]
        by sepref

    end  
  
    export_code scmul_impl in SML_imp
  end  
  hide_const scmul_impl


*)


  hide_const(open) is_amtx

end
