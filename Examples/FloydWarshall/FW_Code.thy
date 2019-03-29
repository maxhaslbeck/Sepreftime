(* Authors: Lammich, Wimmer *)
theory FW_Code
  imports
    Recursion_Combinators
    Floyd_Warshall.Floyd_Warshall
  "../../Refine_Imperative_HOL/IICF/IICF_Misc"
  "SepLogicTime_RBTreeBasic.Asymptotics_1D" 
begin
 
section \<open>Refinement to Efficient Imperative Code\<close>

text \<open>
  We will now refine the recursive version of the \fw to an efficient imperative version.
  To this end, we use the Imperative Refinement Framework, yielding an implementation in Imperative HOL.
\<close>

definition fw_upd' :: "('a::linordered_ab_monoid_add) mtx \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a mtx nrest" where
  "fw_upd' m k i j =
    do {
        mij \<leftarrow> mop_matrix_get 1 m (i, j);
        mik \<leftarrow> mop_matrix_get 1 m (i, k);
        mkj \<leftarrow> mop_matrix_get 1 m (k, j);
        s \<leftarrow> mop_plus 1 mik mkj;
        ss \<leftarrow> mop_min 1 mij s;
        mop_matrix_set 1 m (i, j) ss
  }"

definition fwi' ::  "('a::linordered_ab_monoid_add) mtx \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a mtx nrest"
where
  "fwi' m n k i j = RECT (\<lambda> fw (m, k, i, j).
      case (i, j) of
        (0, 0) \<Rightarrow> fw_upd' m k 0 0 |
        (Suc i, 0) \<Rightarrow> do {m' \<leftarrow> fw (m, k, i, n); fw_upd' m' k (Suc i) 0} |
        (i, Suc j) \<Rightarrow> do {m' \<leftarrow> fw (m, k, i, j); fw_upd' m' k i (Suc j)}
    ) (m, k, i, j)"

lemma fwi'_simps:
  "fwi' m n k 0       0        = fw_upd' m k 0 0"
  "fwi' m n k (Suc i) 0        = do {m' \<leftarrow> fwi' m n k i n; fw_upd' m' k (Suc i) 0}"
  "fwi' m n k i       (Suc j)  = do {m' \<leftarrow> fwi' m n k i j; fw_upd' m' k i (Suc j)}"
unfolding fwi'_def by (subst RECT_unfold, (refine_mono; fail), (auto split: nat.split; fail))+


lemma fw_upd'_spec: "fw_upd' m k i j \<le> SPEC (\<lambda>r. r = uncurry (fw_upd (curry m) k i j)) (\<lambda>_. enat 6)"
  unfolding SPEC_def 
  unfolding fw_upd'_def fw_upd_def upd_def
  apply(rule T_specifies_I)
  apply(vcg' \<open>-\<close> rules: matrix_set matrix_get mop_min mop_plus)
  by(auto split: if_splits )  
  

lemma
  "fwi' m n k i j \<le> SPEC (\<lambda> r. r = uncurry (fwi (curry m) n k i j)) (\<lambda>_. 6*((j+1)+i*(n+1)))"
proof (induction "curry m" n k i j arbitrary: m rule: fwi.induct)
  case (1 n k)
  then show ?case apply (simp add:   fwi'_simps)  by (rule fw_upd'_spec)  
next
  case (2 n k i) 
  show ?case apply (simp add:   fwi'_simps)
    unfolding SPEC_def
    apply(rule T_specifies_I)
    apply(vcg' \<open>simp\<close> rules: 2(1)[unfolded SPEC_def, THEN T_specifies_rev, THEN T_conseq4]
               fw_upd'_spec[unfolded SPEC_def, THEN T_specifies_rev, THEN T_conseq4]       )
    by(auto split: if_splits)    
next
  case (3 n k i j)
  show ?case  apply (simp add:   fwi'_simps)
    unfolding SPEC_def
    apply(rule T_specifies_I)
    apply(vcg' \<open>simp\<close> rules: 3(1)[unfolded SPEC_def, THEN T_specifies_rev, THEN T_conseq4]
               fw_upd'_spec[unfolded SPEC_def, THEN T_specifies_rev, THEN T_conseq4]       )
    by(auto split: if_splits)    
qed 
 

definition "fw_time (n::nat) = 6*((n+1)*(n+1))*(n+1)"
definition "fwi_time (i::nat) (j::nat) (n::nat) = 6*((j+1)+i*(n+1))"

lemma fw_time_fwi_time: "fw_time n = (n+1)* fwi_time n n n" unfolding fw_time_def fwi_time_def
  by auto  
     

lemma for_rec2_fwi:
  "for_rec2 (\<lambda> M. fw_upd' M k) M n i j \<le> SPEC (\<lambda> M'. M' = uncurry (fwi (curry M) n k i j)) (\<lambda>_. fwi_time i j n)"
  unfolding fwi_time_def
proof (induction "\<lambda> M. fw_upd' (M :: (nat \<times> nat \<Rightarrow> 'a)) k" M n i j rule: for_rec2.induct)
  case (1 a n)
  then show ?case apply simp  by (rule fw_upd'_spec)  
next
  case (2 a n i)
  show ?case apply simp 
    unfolding SPEC_def
    apply(rule T_specifies_I)
    apply(vcg' \<open>simp\<close> rules:  2[unfolded SPEC_def, THEN T_specifies_rev, THEN T_conseq4]
               fw_upd'_spec[unfolded SPEC_def, THEN T_specifies_rev, THEN T_conseq4]       )
    by(auto split: if_splits)    
next
  case (3 a n i j)
  show ?case apply simp 
    unfolding SPEC_def
    apply(rule T_specifies_I)
    apply(vcg' \<open>simp\<close> rules:  3[unfolded SPEC_def, THEN T_specifies_rev, THEN T_conseq4]
               fw_upd'_spec[unfolded SPEC_def, THEN T_specifies_rev, THEN T_conseq4]       )
    by(auto split: if_splits)    
qed 

definition fw' ::  "('a::linordered_ab_monoid_add) mtx \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a mtx nrest" where
  "fw' m n k = nfoldli [0..<k + 1] (\<lambda> _. True) (\<lambda> k M. do { for_rec2 (\<lambda> M. fw_upd' M k) M n n n }) m"

lemma fw'_spec:
  "fw' m n k \<le> SPEC (\<lambda> M'. M' = uncurry (fw (curry m) n k))  (\<lambda>_. (k+1)*fwi_time n n n)"
  unfolding fw'_def
proof (induction k)
  case 0
  then show ?case apply simp unfolding SPEC_def 
    apply(rule T_specifies_I)
    apply(vcg' \<open>simp\<close> rules:   
               for_rec2_fwi[unfolded SPEC_def, THEN T_specifies_rev, THEN T_conseq4]       )
    apply simp apply (vcg' \<open>-\<close>) by(auto split: if_splits simp: curry_def)
next
  case (Suc k)
  have dec: "[0..<Suc k + 1] = [0..<k + 1] @ [k+1]" by auto
  show ?case apply(simp only: dec nfoldli_append)  unfolding SPEC_def
    apply(rule T_specifies_I)
    apply(vcg' \<open>simp\<close> rules:   
               Suc(1)[unfolded SPEC_def, THEN T_specifies_rev, THEN T_conseq4]
                     )
    apply simp apply (vcg' \<open>-\<close> rules: for_rec2_fwi[unfolded SPEC_def, THEN T_specifies_rev, THEN T_conseq4] )
    apply simp apply (vcg' \<open>-\<close>) by(auto split: if_splits simp: curry_def)
qed



context
  fixes n :: nat
  fixes dummy :: "'a::{linordered_ab_monoid_add,zero,heap}"
begin

(*lemma [sepref_import_param]: "((+),(+)::'a\<Rightarrow>_) \<in> Id \<rightarrow> Id \<rightarrow> Id" by simp
lemma [sepref_import_param]: "(min,min::'a\<Rightarrow>_) \<in> Id \<rightarrow> Id \<rightarrow> Id" by simp*)

abbreviation "node_assn \<equiv> nat_assn"
abbreviation "mtx_assn \<equiv> asmtx_assn (Suc n) id_assn::('a mtx \<Rightarrow>_)"

lemma ff: "(bb ::\<^sub>iTYPE('a i_mtx)) \<Longrightarrow> (bb ::\<^sub>iTYPE(nat \<times> nat \<Rightarrow>'a))" by auto

sepref_definition fw_upd_impl is
  "uncurry2 (uncurry fw_upd')" ::
  "[\<lambda> (((_,k),i),j). k \<le> n \<and> i \<le> n \<and> j \<le> n]\<^sub>a mtx_assn\<^sup>d *\<^sub>a node_assn\<^sup>k *\<^sub>a node_assn\<^sup>k *\<^sub>a node_assn\<^sup>k
  \<rightarrow> mtx_assn"
  unfolding fw_upd'_def[abs_def] 
  apply sepref_dbg_preproc 
   apply sepref_dbg_cons_init
  apply(drule ff)       (* ----------------- TODO -------------- *)
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

declare fw_upd_impl.refine[sepref_fr_rules]

sepref_register fw_upd' :: "'a i_mtx \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a i_mtx nrest"

definition
  "fwi_impl' (M :: 'a mtx) k = for_rec2 (\<lambda> M. fw_upd' M k) M n n n"

definition
  "fw_impl' (M :: 'a mtx) = fw' M n n"

context
  notes [id_rules] = itypeI[of n "TYPE (nat)"]
    and [sepref_import_param] = IdI[of n]
begin

sepref_definition fw_impl is
  "fw_impl'" :: "mtx_assn\<^sup>d \<rightarrow>\<^sub>a mtx_assn"      using [[id_debug, goals_limit = 1]]
  unfolding fw_impl'_def[abs_def] fw'_def
  unfolding for_rec2_eq apply(subst (2) nfoldli_assert'[symmetric])
      apply(subst (1) nfoldli_assert'[symmetric])
      apply(subst (0) nfoldli_assert'[symmetric])
    unfolding nfoldli_def
    by sepref
 

sepref_definition fwi_impl is
  "uncurry fwi_impl'" :: "[\<lambda> (_,k). k \<le> n]\<^sub>a mtx_assn\<^sup>d *\<^sub>a node_assn\<^sup>k \<rightarrow> mtx_assn"
unfolding fwi_impl'_def[abs_def] for_rec2_eq  
      apply(subst (1) nfoldli_assert'[symmetric])
      apply(subst (0) nfoldli_assert'[symmetric])
    unfolding nfoldli_def  
    by sepref

end (* End of sepref setup *)

end (* End of n *)


export_code fw_impl checking SML_imp

text \<open>
  A compact specification for the characteristic property of the \fw.
\<close>
definition fw_spec where
  "fw_spec n M \<equiv> SPEC (\<lambda> M'.
    if (\<exists> i \<le> n. M' i i < 0)
    then \<not> cyc_free M n
    else \<forall>i \<le> n. \<forall>j \<le> n. M' i j = D M i j n \<and> cyc_free M n) (\<lambda>_. fw_time n)"

lemma D_diag_nonnegI:
  assumes "cycle_free M n" "i \<le> n"
  shows "D M i i n \<ge> 0"
using assms D_dest''[OF refl, of M i i n] unfolding cycle_free_def by auto


lemma fw_fw_spec:
  "SPECT [FW M n \<mapsto> enat (fw_time n)] \<le> fw_spec n M"
unfolding fw_spec_def cycle_free_diag_equiv SPEC_def apply (simp add: le_fun_def)
proof (safe, goal_cases)
  case prems: (1 i)
  with fw_shortest_path[unfolded cycle_free_diag_equiv, OF prems(3)] D_diag_nonnegI show ?case
    by fastforce
next
  case 2 then show ?case using FW_neg_cycle_detect[unfolded cycle_free_diag_equiv]
    by (force intro: fw_shortest_path[symmetric, unfolded cycle_free_diag_equiv])
next
  case 3 then show ?case using FW_neg_cycle_detect[unfolded cycle_free_diag_equiv] by blast
qed

definition
  "mat_curry_rel = {(Mu, Mc). curry Mu = Mc}"

definition
  "mtx_curry_assn n = hr_comp (mtx_assn n) (br curry (\<lambda>_. True))"

declare mtx_curry_assn_def[symmetric, fcomp_norm_unfold]

lemma fw_impl'_correct:
  "(fw_impl', fw_spec) \<in> Id \<rightarrow> br curry (\<lambda> _. True) \<rightarrow> \<langle>br curry (\<lambda> _. True)\<rangle> nrest_rel"
 unfolding fw_impl'_def[abs_def]  using fw'_spec fw_fw_spec  
 by (fastforce simp: in_br_conv pw_le_iff refine_pw_simps fw_time_fwi_time intro!: nrest_relI ) 
 

subsection \<open>Main Result\<close>

text \<open>This is one way to state that \<open>fw_impl\<close> fulfills the specification \<open>fw_spec\<close>.\<close>
theorem fw_impl_correct:
  "(fw_impl n, fw_spec n) \<in> (mtx_curry_assn n)\<^sup>d \<rightarrow>\<^sub>a mtx_curry_assn n"
using fw_impl.refine[FCOMP fw_impl'_correct[THEN fun_relD, OF IdI]] .

text \<open>An alternative version: a Hoare triple for total correctness.\<close>
corollary fw_correct:
  "<mtx_curry_assn n M Mi * $(fw_time n)> fw_impl n Mi <\<lambda> Mi'. \<exists>\<^sub>A M'. mtx_curry_assn n M' Mi' * \<up>
    (if (\<exists> i \<le> n. M' i i < 0)
    then \<not> cyc_free M n
    else \<forall>i \<le> n. \<forall>j \<le> n. M' i j = D M i j n \<and> cyc_free M n)>\<^sub>t"
unfolding cycle_free_diag_equiv
  thm fw_impl_correct[THEN hfrefD] fw_spec_def 
  apply (rule ht_cons_rule[OF _ _ extract_cost_ub_SPEC[OF fw_impl_correct[THEN hfrefD, unfolded fw_spec_def[unfolded cycle_free_diag_equiv]] ]])
  by sep_auto+ 

lemma fw_time_n_cube: "fw_time \<in> \<Theta>(\<lambda>n. n*n*n)"
  unfolding fw_time_def by auto2

subsection \<open>Alternative Versions for Uncurried Matrices.\<close>

definition "FWI' = uncurry ooo FWI o curry"


lemma fwi_impl'_refine_FWI':
  "(fwi_impl' n, (\<lambda>x. SPECT [ x \<mapsto> fwi_time n n n])  oo PR_CONST (\<lambda> M. FWI' M n)) \<in> Id \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle> nrest_rel"
unfolding fwi_impl'_def[abs_def] FWI_def[abs_def] FWI'_def using for_rec2_fwi
by (force simp: pw_nrest_rel_iff pw_le_iff refine_pw_simps fw_time_fwi_time) 
 
lemmas fwi_impl_refine_FWI' = fwi_impl.refine[FCOMP fwi_impl'_refine_FWI']

definition "FW' = uncurry oo FW o curry"

definition "FW'' n M = FW' M n"

lemma fw_impl'_refine_FW'':
  "(fw_impl' n, (\<lambda>x. SPECT [ x \<mapsto> fw_time n]) o PR_CONST (FW'' n)) \<in> Id \<rightarrow> \<langle>Id\<rangle> nrest_rel"
unfolding fw_impl'_def[abs_def] FW''_def[abs_def] FW'_def using fw'_spec
by (force simp: pw_le_iff pw_nrest_rel_iff refine_pw_simps fw_time_fwi_time)

lemmas fw_impl_refine_FW'' = fw_impl.refine[FCOMP fw_impl'_refine_FW'']

end
