theory BinarySearch
  imports "../Refine_Imperative_HOL/IICF/Impl/IICF_Array_ListN" 
     "../RefineMonadicVCG" "SepLogicTime_RBTreeBasic.Asymptotics_1D"
begin
section "Binary Search"

definition avg :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "avg l r = (l + r) div 2"

definition "listlookup_time = 1"

function binarysearch_time :: "nat \<Rightarrow> nat" where
  "n < 2 \<Longrightarrow> binarysearch_time n = 2 + listlookup_time"
| "n \<ge> 2 \<Longrightarrow> binarysearch_time n = 2 + listlookup_time + binarysearch_time (n div 2)"
by force simp_all
termination by (relation "Wellfounded.measure (\<lambda>n. n)") auto

definition binarysearch_time' :: "nat \<Rightarrow> real" where
  "binarysearch_time' n = real (binarysearch_time n)"

lemma div_2_to_rounding:
  "n - n div 2 = nat \<lceil>n / 2\<rceil>" "n div 2 = nat \<lfloor>n / 2\<rfloor>" by linarith+

lemma binarysearch_time'_Theta: "(\<lambda>n. binarysearch_time' n) \<in> \<Theta>(\<lambda>n. ln (real n))"
  apply (master_theorem2 2.3 recursion: binarysearch_time.simps(2) rew: binarysearch_time'_def div_2_to_rounding)
  unfolding listlookup_time_def
  prefer 2 apply auto2
  by (auto simp: binarysearch_time'_def)

lemma binarysearch_mono:
  "m \<le> n \<Longrightarrow> binarysearch_time m \<le> binarysearch_time n" 
proof (induction n arbitrary: m rule: less_induct)
  case (less n)
  show ?case
  proof (cases "m<2")
    case True
    then show ?thesis apply (cases "n<2") by auto
  next
    case False
    then show ?thesis using less(2) by (auto intro: less(1))
  qed
qed

definition binarysearch_SPEC :: "nat \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> bool nrest" where
  "binarysearch_SPEC l r xs x
   = SPECT (emb (\<lambda>s. s \<longleftrightarrow> (\<exists>i. l \<le> i \<and> i < r \<and> xs ! i = x)) (binarysearch_time (r-l)) )"

definition "binarysearch l r x xs \<equiv>
    RECT (\<lambda>fw (l,r).
      if l \<ge> r then RETURNT False
    else if l + 1 \<ge> r then do {
              ASSERT (l < length xs);
             xsi \<leftarrow> mop_lookup_list listlookup_time xs l;
                                RETURNT (xsi = x) }
    else do {
        m \<leftarrow> RETURNT (avg l r);
        ASSERT (m < length xs);
        xm \<leftarrow> mop_lookup_list listlookup_time xs m;
      (if xm = x then RETURNT True
      else if xm < x then fw (m + 1, r)
      else fw (l, m))
      }
  ) (l,r)"

prepare_code_thms binarysearch_def
print_theorems
thm binarysearch.code(1,2) 

 
lemma avg_diff1: "(l::nat) \<le> r \<Longrightarrow> r - (avg l r + 1) \<le> (r - l) div 2" by (simp add: avg_def)
lemma avg_diff2: "(l::nat) \<le> r \<Longrightarrow> avg l r - l \<le> (r - l) div 2" by  (simp add: avg_def)

lemma avg_between [backward] :
  "l + 1 < r \<Longrightarrow> r > avg l r"
  "l + 1 < r \<Longrightarrow> avg l r > l" by (auto simp: avg_def)

lemma binarysearch_correct: "sorted xs \<Longrightarrow> l \<le> r \<Longrightarrow> r \<le> length xs \<Longrightarrow>
   binarysearch l r x xs \<le> binarysearch_SPEC l r xs x"
  unfolding binarysearch_SPEC_def 
  apply(rule T_specifies_I)
    apply(subst binarysearch.code(1))
proof(induct "r-l" arbitrary: l r rule: less_induct)
  case less
  from less(2-4) show ?case apply(subst binarysearch.code(2))  unfolding mop_lookup_list_def
     apply (vcg'\<open>simp\<close> rules: less(1)[THEN T_conseq4] )   
    unfolding Some_le_emb'_conv Some_eq_emb'_conv
    subgoal by auto 
    subgoal using le_less_Suc_eq by fastforce
    subgoal apply (simp) by auto2 
    subgoal by(simp add: avg_def)  
    subgoal by(simp add: avg_def)  
    subgoal 
      apply (rule allI conjI) apply auto2
        using binarysearch_mono[OF avg_diff1] 
        by (simp add: le_SucI)
    subgoal by(simp add: avg_def)    
    subgoal by(simp add: avg_def)   
    subgoal by(simp add: avg_def)
    subgoal 
      apply (rule allI conjI) apply auto2  
        using binarysearch_mono[OF avg_diff2] 
        by (simp add: le_SucI) 
    subgoal by auto2
    done
  
qed
 
sepref_definition binarysearch_impl is 
  "uncurry3 binarysearch" :: "nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a id_assn\<^sup>k *\<^sub>a array_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  unfolding binarysearch_def avg_def  listlookup_time_def
  using [[goals_limit = 3]] 
  by sepref

thm binarysearch_impl.refine[to_hnr]
thm hnr_refine[OF binarysearch_correct ] binarysearch_impl.refine[to_hnr, unfolded autoref_tag_defs]
thm  hnr_refine[OF binarysearch_correct, OF _ _ _ binarysearch_impl.refine[to_hnr, unfolded autoref_tag_defs], no_vars] 

lemma binary_search_impl_correct: 
  assumes "sorted xs" "l \<le> r" "r \<le> length xs"
  shows "hn_refine (hn_ctxt array_assn xs bi * hn_val Id x bia * hn_val nat_rel r bib * hn_val nat_rel l ai)
            (binarysearch_impl ai bib bia bi)
            (hn_ctxt array_assn xs bi * hn_val Id x bia * hn_val nat_rel r bib * hn_val nat_rel l ai) 
            bool_assn (binarysearch_SPEC l r xs x)"
  using assms hnr_refine[OF binarysearch_correct, OF _ _ _ binarysearch_impl.refine[to_hnr, unfolded autoref_tag_defs]] by metis

thm extract_cost_ub'[OF binary_search_impl_correct[unfolded  binarysearch_SPEC_def], where Cost_ub="binarysearch_time (r - l)" ]
lemma binary_search_correct': "sorted xs \<Longrightarrow> r \<le> length xs \<Longrightarrow> l \<le> r \<Longrightarrow> 
     <hn_ctxt array_assn xs p * hn_val Id x bia * hn_val nat_rel r bib * hn_val nat_rel l ai * timeCredit_assn (binarysearch_time (r - l))> 
        binarysearch_impl ai bib bia p
       <\<lambda>ra. hn_ctxt array_assn xs p * \<up> (ra \<longleftrightarrow> (\<exists>i\<ge>l. i < r \<and> xs ! i = x))>\<^sub>t"
  apply(rule extract_cost_ub'[OF binary_search_impl_correct[unfolded  binarysearch_SPEC_def], where Cost_ub="binarysearch_time (r - l)" ])
       apply auto
     apply(subst in_ran_emb_special_case) apply (simp_all add: pure_def) apply auto
   by (metis (no_types, lifting) ent_true_drop(1) entails_ex entt_refl') 


subsection \<open>Final Hoare triple and run-time claim.\<close>

lemma binary_search_correct: "sorted xs \<Longrightarrow> r \<le> length xs \<Longrightarrow> l \<le> r \<Longrightarrow> 
     <array_assn xs p * timeCredit_assn (binarysearch_time (r - l))> 
        binarysearch_impl l r x p
       <\<lambda>ra.   array_assn xs p * \<up> (ra \<longleftrightarrow> (\<exists>i\<ge>l. i < r \<and> xs ! i = x))>\<^sub>t"
  apply(rule ht_cons_rule[OF _ _ binary_search_correct'[ unfolded hn_ctxt_def pure_def ]])
  by (sep_auto )+

lemma binary_search_time_ln: "binarysearch_time \<in> \<Theta>(\<lambda>n. ln (real n))"
  using binarysearch_time'_Theta unfolding binarysearch_time'_def by auto

end