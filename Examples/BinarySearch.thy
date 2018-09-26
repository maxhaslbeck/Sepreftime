theory BinarySearch
  imports "../Refine_Imperative_HOL/Sepref" "../RefineMonadicVCG" "SepLogicTime_RBTreeBasic.Asymptotics_1D"
begin



subsubsection "List interface"


definition "listlookup_time = 3"

context
  fixes n::nat
begin
  definition "mop_lookup_list xs i = SPECT [ xs ! i \<mapsto> enat n ]"

  sepref_register "mop_lookup_list" 
  print_theorems 
end

term list_assn
term Array.nth

definition "array_assn xs p = p \<mapsto>\<^sub>a xs"

lemma inst_ex_assn: "A \<Longrightarrow>\<^sub>A B x \<Longrightarrow> A \<Longrightarrow>\<^sub>A (\<exists>\<^sub>Ax. B x)"
  using entails_ex_post by blast 

lemma mop_lookup_list_as_array_rule[sepref_fr_rules]:
  "1 \<le> n \<Longrightarrow> x < length xs \<Longrightarrow>
    hn_refine (hn_ctxt array_assn xs p * hn_val Id x x')
     (Array.nth p (x'::nat))
     (hn_ctxt array_assn xs p * hn_ctxt (pure Id) x x') id_assn ( PR_CONST (mop_lookup_list n) $  xs $ x)"
  unfolding autoref_tag_defs mop_lookup_list_def
  apply (rule extract_cost_otherway[OF _  nth_rule, where F="nat_assn x x'"]) unfolding mult.assoc
  unfolding hn_ctxt_def array_assn_def
      apply(rule match_first) apply rotatel apply(rule match_first) apply (simp add: pure_def)  
   apply(rule match_first) apply (simp add: pure_def)   apply safe 
    apply(rule inst_ex_assn[where x="xs ! x"]) apply simp apply simp  done


thm mop_lookup_list_as_array_rule[to_hfref]

definition avg :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "avg l r = (l + r) div 2"


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


function binarysearch_fun :: "nat \<Rightarrow> nat \<Rightarrow> 'a::linorder \<Rightarrow> 'a list \<Rightarrow> bool nrest" where
  "binarysearch_fun l r x xs =
   do {
    if l \<ge> r then RETURNT False
    else if l + 1 \<ge> r then RETURNT (xs ! l = x)
    else let m = avg l r in
      if xs ! m = x then RETURNT True
      else if xs ! m < x then binarysearch_fun (m + 1) r x xs
      else binarysearch_fun l m x xs }"
by pat_completeness auto
termination by (relation "Wellfounded.measure (\<lambda>(l,r,a,f). r-l)") (auto simp: avg_def)
 
lemma "sorted xs \<Longrightarrow> l \<le> r \<Longrightarrow> r \<le> length xs \<Longrightarrow>
   binarysearch_fun l r x xs \<le> binarysearch_SPEC l r xs x"
  apply(induction rule: binarysearch_fun.induct)
  oops

definition "binarysearch l r x xs =
    RECT (\<lambda>fw (l,r,x,xs).
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
      else if xm < x then fw (m + 1, r, x, xs)
      else fw (l, m, x, xs))
      }
  ) (l,r,x,xs)"

lemma binarysearch_simps: "binarysearch l r x xs = do {
    if l \<ge> r then RETURNT False
    else if l + 1 \<ge> r then
         do {
              ASSERT (l < length xs);
             xsi \<leftarrow> mop_lookup_list listlookup_time xs l;
                                RETURNT (xsi = x) }
    else  do {
        m \<leftarrow> RETURNT (avg l r);
        ASSERT (m < length xs);
        xm \<leftarrow> mop_lookup_list listlookup_time xs m;
      (if xm = x then RETURNT True
      else if xm < x then binarysearch (m + 1) r x xs
      else binarysearch l m x xs)
      } }"
  unfolding binarysearch_def by (subst RECT_unfold, refine_mono, auto)


lemma Some_eq_emb'_conv: "emb' Q tf s = Some t \<longleftrightarrow> (Q s \<and> t = tf s)"
  unfolding emb'_def by(auto split: if_splits)
 
lemma avg_diff1: "(l::nat) \<le> r \<Longrightarrow> r - (avg l r + 1) \<le> (r - l) div 2" by (simp add: avg_def)
lemma avg_diff1': "(l::nat) \<le> r \<Longrightarrow> r - Suc (avg l r) \<le> (r - l) div 2" by (simp add: avg_def)
lemma avg_diff2: "(l::nat) \<le> r \<Longrightarrow> avg l r - l \<le> (r - l) div 2" by  (simp add: avg_def)


lemma avg_between [backward] :
  "l + 1 < r \<Longrightarrow> r > avg l r"
  "l + 1 < r \<Longrightarrow> avg l r > l" by (auto simp: avg_def)

lemma binarysearch_correct: "sorted xs \<Longrightarrow> l \<le> r \<Longrightarrow> r \<le> length xs \<Longrightarrow>
   binarysearch l r x xs \<le> binarysearch_SPEC l r xs x"
  unfolding binarysearch_SPEC_def 
  apply(rule T_specifies_I)
proof(induct "r-l" arbitrary: l r rule: less_induct)
  case less
  from less(2-4) show ?case
    apply(subst binarysearch_simps) unfolding mop_lookup_list_def
    apply (vcg'\<open>simp\<close>)
            apply (metis le_neq_implies_less le_refl not_less_eq) 
    apply(simp add: avg_def)
    apply(rule T_conseq4)  
         apply(rule less(1)) apply (simp add: avg_def;fail)+
    subgoal 
      apply(simp only: Some_le_emb'_conv Some_eq_emb'_conv)
      apply (rule allI conjI)
      subgoal by auto2    (* <<<<<<<<<<<<<<<<<<<<<<<<<<<  :) *)
      subgoal  using binarysearch_mono[OF avg_diff1'] 
        by (simp add: le_SucI)
      done
    subgoal 
      using le_less_Suc_eq by fastforce 
    apply(simp add: avg_def)
    subgoal by auto2    (* <<<<<<<<<<<<<<<<<<<<<<<<<<<  :) *)
    subgoal 
      using le_less_Suc_eq by fastforce 
    apply(simp add: avg_def)
    apply(rule T_conseq4) 
         apply(rule less(1)) apply (simp add: avg_def;fail)+
    subgoal 
      apply(simp only: Some_le_emb'_conv Some_eq_emb'_conv)
      apply (rule allI conjI)
      subgoal by auto2    (* <<<<<<<<<<<<<<<<<<<<<<<<<<<  :) *)
      subgoal  using binarysearch_mono[OF avg_diff2] 
        by (simp add: le_SucI)
      done
    done
qed

   

context 
  fixes l::"nat"
  notes [[sepref_register_adhoc l]]
  notes [sepref_import_param] = IdI[of l] 
  fixes r::"nat"
  notes [[sepref_register_adhoc r]]
  notes [sepref_import_param] = IdI[of r] 
  fixes x::"nat"
  notes [[sepref_register_adhoc x]]
  notes [sepref_import_param] = IdI[of x] 
begin 

declare listlookup_time_def [simp]

sepref_definition binarysearch_impl is "(binarysearch l r x)" :: "array_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  unfolding binarysearch_def avg_def 
  using [[goals_limit = 3]] 

  apply sepref_dbg_preproc
  apply sepref_dbg_cons_init
  apply sepref_dbg_id 
     apply sepref_dbg_monadify

     apply sepref_dbg_opt_init

  thm sepref_fr_rules     
  thm sepref_comb_rules          

  apply sepref_dbg_trans_step+ 


  apply sepref_dbg_opt
  apply sepref_dbg_cons_solve \<comment> \<open>Frame rule, recovering the invalidated list 
    or pure elements, propagating recovery over the list structure\<close>
  apply sepref_dbg_cons_solve \<comment> \<open>Trivial frame rule\<close>
  apply sepref_dbg_constraints 
  sorry
 

thm binarysearch_impl.refine[to_hnr]
thm hnr_refine[OF binarysearch_correct ] binarysearch_impl.refine[to_hnr, unfolded autoref_tag_defs]
thm  hnr_refine[OF binarysearch_correct, OF _ _ _ binarysearch_impl.refine[to_hnr, unfolded autoref_tag_defs]] 

lemma binary_search_impl_correct: "sorted xs \<Longrightarrow> l \<le> r \<Longrightarrow> r \<le> length xs \<Longrightarrow> hn_refine (hn_ctxt array_assn xs p) (binarysearch_impl p) (hn_ctxt array_assn xs p) bool_assn (binarysearch_SPEC l r xs x)"
  using hnr_refine[OF binarysearch_correct, OF _ _ _ binarysearch_impl.refine[to_hnr, unfolded autoref_tag_defs]]  by auto 

thm extract_cost_ub'[OF binary_search_impl_correct[unfolded  binarysearch_SPEC_def], where Cost_ub="binarysearch_time (r - l)" ]
lemma "sorted xs \<Longrightarrow> r \<le> length xs \<Longrightarrow> l \<le> r \<Longrightarrow> 
     <hn_ctxt array_assn xs p * timeCredit_assn (binarysearch_time (r - l))> 
        binarysearch_impl p
       <\<lambda>ra. hn_ctxt array_assn xs p * \<up> (ra \<longleftrightarrow> (\<exists>i\<ge>l. i < r \<and> xs ! i = x))>\<^sub>t"
  apply(rule extract_cost_ub'[OF binary_search_impl_correct[unfolded  binarysearch_SPEC_def], where Cost_ub="binarysearch_time (r - l)" ])
       apply auto
     apply(subst in_ran_emb_special_case) apply (simp_all add: pure_def) apply auto
   by (metis (no_types, lifting) ent_true_drop(1) entails_ex entt_refl') 


lemma "binarysearch_time \<in> \<Theta>(\<lambda>n. ln (real n))"
  using binarysearch_time'_Theta unfolding binarysearch_time'_def by auto





end