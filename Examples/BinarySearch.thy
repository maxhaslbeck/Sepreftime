theory BinarySearch
  imports "../Refine_Imperative_HOL/Sepref" "../RefineMonadicVCG"
begin


definition avg :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "avg l r = (l + r) div 2"


function binarysearch_time :: "nat \<Rightarrow> nat" where
  "n < 2 \<Longrightarrow> binarysearch_time n = 2"
| "n \<ge> 2 \<Longrightarrow> binarysearch_time n = 2 + binarysearch_time (n div 2)"
by force simp_all
termination by (relation "Wellfounded.measure (\<lambda>n. n)") auto


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
    else if l + 1 \<ge> r then RETURNT (xs ! l = x)
    else do {
        m \<leftarrow> RETURNT (avg l r);
      (if xs ! m = x then RETURNT True
      else if xs ! m < x then fw (m + 1, r, x, xs)
      else fw (l, m, x, xs))
      }
  ) (l,r,x,xs)"

lemma binarysearch_simps: "binarysearch l r x xs = do {
    if l \<ge> r then RETURNT False
    else if l + 1 \<ge> r then RETURNT (xs ! l = x)
    else  do {
        m \<leftarrow> RETURNT (avg l r);
      (if xs ! m = x then RETURNT True
      else if xs ! m < x then binarysearch (m + 1) r x xs
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

lemma "sorted xs \<Longrightarrow> l \<le> r \<Longrightarrow> r \<le> length xs \<Longrightarrow>
   binarysearch l r x xs \<le> binarysearch_SPEC l r xs x"
  unfolding binarysearch_SPEC_def
  apply(rule T_specifies_I)
proof(induct "r-l" arbitrary: l r rule: less_induct)
  case less
  from less(2-4) show ?case
    apply(subst binarysearch_simps) 
    apply (vcg'\<open>simp\<close>)
    apply (metis le_neq_implies_less le_refl not_less_eq) 
    apply(rule T_conseq6) 
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
    subgoal by auto2    (* <<<<<<<<<<<<<<<<<<<<<<<<<<<  :) *)
    subgoal 
      using le_less_Suc_eq by fastforce 
    apply(rule T_conseq6) 
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

   






end