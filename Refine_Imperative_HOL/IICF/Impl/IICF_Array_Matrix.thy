section \<open>Implementation of Matrices by Array (Row-Major)\<close>
theory IICF_Array_Matrix
imports "../Intf/IICF_Matrix"
begin

definition is_amtx where [rewrite_ent]:   "is_amtx N M c mtx = (\<exists>\<^sub>Al. mtx \<mapsto>\<^sub>a l * \<up>( 
    length l = N*M 
  \<and> (\<forall>i<N. \<forall>j<M. l!(i*M+j) = c (i,j))
  \<and> (\<forall>i j. (i\<ge>N \<or> j\<ge>M) \<longrightarrow> c (i,j) = 0)))"
  
lemma is_amtx_bounded:
  shows "rdomp (is_amtx N M) m \<Longrightarrow> mtx_nonzero m \<subseteq> {0..<N}\<times>{0..<M}"
  unfolding rdomp_def 
  apply (clarsimp simp: mtx_nonzero_def is_amtx_def)
  by (meson not_less)


partial_function (heap_time) imp_for' :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> 'a \<Rightarrow> 'a Heap) \<Rightarrow> 'a \<Rightarrow> 'a Heap" where
  "imp_for' i u f s = (if i \<ge> u then return s else f i s \<bind> imp_for' (i + 1) u f)"

declare imp_for'.simps[code]

lemma imp_for'_simps[simp]:
  "i \<ge> u \<Longrightarrow> imp_for' i u f s = return s"
  "i < u \<Longrightarrow> imp_for' i u f s = f i s \<bind> imp_for' (i + 1) u f"
  by (auto simp: imp_for'.simps)



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
    by (metis Suc_diff_Suc add.commute mult_Suc_right plus_1_eq_Suc)  
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
    by (metis add_right_cancel div_if div_mult_self3 not_less0)
  subgoal
    using \<open>\<lbrakk>j < M; j' < M; i * M + j = i' * M + j'\<rbrakk> \<Longrightarrow> i = i'\<close> by auto  
  done
    
lemma mtx_index_unique[simp]: "\<lbrakk>i<(N::nat); j<M; i'<N; j'<M\<rbrakk> \<Longrightarrow> i*M+j = i'*M+j' \<longleftrightarrow> i=i' \<and> j=j'"
  by (metis ab_semigroup_add_class.add.commute add_diff_cancel_right'
          div_if div_mult_self3 not_less0)



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
        heap: 
        imp_for'_rule'[where 
          I="\<lambda>k (i,j,mi). \<exists>\<^sub>Am. mi \<mapsto>\<^sub>a m 
          * \<up>( k=i*M+j \<and> j<M \<and> k\<le>N*M \<and> length m = N*M )
          * \<up>( \<forall>i'<i. \<forall>j<M. m!(i'*M+j) = c (i',j) )
          * \<up>( \<forall>j'<j. m!(i*M+j') = c (i,j') )* timeCredit_assn 1 " and t="2"
          ]    
        simp: nth_list_update M_POS is_amtx_def dest: Suc_lessI)
    subgoal by (metis add.right_neutral M_POS mtx_idx_unique_conv)  
    subgoal using mtx_nonzeroD[OF _ NONZ] by auto
    done
     
qed

definition "PRES_ZERO_UNIQUE A \<equiv> (A``{0}={0} \<and> A\<inverse>``{0} = {0})"
lemma IS_ID_imp_PRES_ZERO_UNIQUE[constraint_rules]: "IS_ID A \<Longrightarrow> PRES_ZERO_UNIQUE A"
  unfolding IS_ID_def PRES_ZERO_UNIQUE_def by auto

definition op_amtx_dfltNxM :: "nat \<Rightarrow> nat \<Rightarrow> 'a::zero \<Rightarrow> nat\<times>nat\<Rightarrow>'a" where
  [simp]: "op_amtx_dfltNxM N M v = (\<lambda>(i,j). if i<N \<and> j<M then v else 0)"

lemma opt_amtx_dfltNxM[rewrite]: "op_amtx_dfltNxM N M v (i,j) = (if i<N \<and> j<M then v else 0)"
  unfolding op_amtx_dfltNxM_def by simp


declare upt_zero_length [rewrite_arg]

lemma mtx_idx_valid[simp,backward]: "\<lbrakk>i < (N::nat); j < M\<rbrakk> \<Longrightarrow> i * M + j < N * M"
  by (rule mlex_bound)

lemma mtx_dflt_rl: "<timeCredit_assn (N*M+1)> amtx_dflt N M k <is_amtx N M (op_amtx_dfltNxM N M k)>"
  by auto2

lemma mtx_get_rl: "\<lbrakk>i<N; j<M \<rbrakk> \<Longrightarrow> <timeCredit_assn 1 * is_amtx N M c mtx> mtx_get M mtx (i,j) <\<lambda>r. is_amtx N M c mtx * \<up>(r = c (i,j))>"
  by auto2

lemma mtx_set_rl: "\<lbrakk>i<N; j<M \<rbrakk> 
  \<Longrightarrow> <timeCredit_assn 1 * is_amtx N M c mtx> mtx_set M mtx (i,j) v <\<lambda>r. is_amtx N M (c((i,j) := v)) r>"
  unfolding mtx_set_def is_amtx_def
  by (sep_auto simp del: One_nat_def) 

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

lemma extractpureD: "h \<Turnstile> pure R a c * F \<Longrightarrow> (c,a) \<in> R \<and> h \<Turnstile> F"
  by (simp add: pure_def)

lemma the_pure_id_assn_is_Id: "the_pure (\<lambda>a c. \<up> (c = a)) = Id" 
proof -
  have "the_pure (\<lambda>a c. \<up> (c = a)) = the_pure id_assn" by (simp add: pure_def)
  also have "\<dots> = Id" by simp
  finally show ?thesis .
qed
                 

context 
  notes [intro!] = hfrefb_to_hoare_triple
  notes [simp] = pure_def hn_ctxt_def invalid_assn_def uncurry_t_def
                noparam_t_def oneparam_t_def uncurry2_t_def
begin   
  
  lemma mop_matrix_set_rule_aux: "(uncurry2 (PR_CONST (mtx_set M)), uncurry2_t mop_matrix_set)
      \<in> [\<lambda>((a, b), v').
             fst b < M \<and> snd b < M, \<lambda>_. 1]\<^sub>b (asmtx_assn M id_assn)\<^sup>d *\<^sub>a (nat_assn \<times>\<^sub>a nat_assn)\<^sup>k *\<^sub>a id_assn\<^sup>k \<rightarrow> asmtx_assn M id_assn"
    by (sep_auto heap: mtx_set_rl   simp: amtx_assn_def hr_comp_def mop_matrix_set_def the_pure_id_assn_is_Id)

  lemmas mop_matrix_set_rule[sepref_fr_rules] = mop_matrix_set_rule_aux[hfb_to_hnr]


  lemma mop_matrix_get_rule_aux: "(uncurry (PR_CONST (mtx_get M)), uncurry_t mop_matrix_get)
      \<in> [\<lambda>(a, b). fst b < M \<and> snd b < M, \<lambda>_. 1]\<^sub>b (asmtx_assn M id_assn)\<^sup>k *\<^sub>a (nat_assn \<times>\<^sub>a nat_assn)\<^sup>k \<rightarrow> id_assn"
    by (sep_auto heap: mtx_get_rl   simp: amtx_assn_def hr_comp_def mop_matrix_get_def the_pure_id_assn_is_Id)

  lemmas mop_matrix_get_rule[sepref_fr_rules] = mop_matrix_get_rule_aux[hfb_to_hnr]
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

hide_const(open) is_amtx

end