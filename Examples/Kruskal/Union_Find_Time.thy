theory Union_Find_Time
imports 
  "../../SepLog_Automatic" 
  "../../Refine_Imperative_HOL/Sepref_Additional" 
  Collections.Partial_Equivalence_Relation
  "HOL-Library.Code_Target_Numeral"
  "SepLogicTime_RBTreeBasic.Asymptotics_1D"
  UnionFind_Impl
begin

notation timeCredit_assn  ("$") 

text {*
  We implement a simple union-find data-structure based on an array.
  It uses path compression and a size-based union heuristics.
*}

subsection {* Abstract Union-Find on Lists *}
text {*
  We first formulate union-find structures on lists, and later implement 
  them using Imperative/HOL. This is a separation of proof concerns
  between proving the algorithmic idea correct and generating the verification
  conditions.
*}

subsubsection {* Representatives *}
text {*
  We define a function that searches for the representative of an element.
  This function is only partially defined, as it does not terminate on all
  lists. We use the domain of this function to characterize valid union-find 
  lists. 
*}
function (domintros) rep_of 
  where "rep_of l i = (if l!i = i then i else rep_of l (l!i))"
  by pat_completeness auto

text {* A valid union-find structure only contains valid indexes, and
  the @{text "rep_of"} function terminates for all indexes. *}
definition 
  "ufa_invar l \<equiv> \<forall>i<length l. rep_of_dom (l,i) \<and> l!i<length l"

lemma ufa_invarD: 
  "\<lbrakk>ufa_invar l; i<length l\<rbrakk> \<Longrightarrow> rep_of_dom (l,i)" 
  "\<lbrakk>ufa_invar l; i<length l\<rbrakk> \<Longrightarrow> l!i<length l" 
  unfolding ufa_invar_def by auto

text {* We derive the following equations for the @{text "rep-of"} function. *}
lemma rep_of_refl: "l!i=i \<Longrightarrow> rep_of l i = i"
  apply (subst rep_of.psimps)
  apply (rule rep_of.domintros)
  apply (auto)
  done

lemma rep_of_step: 
  "\<lbrakk>ufa_invar l; i<length l; l!i\<noteq>i\<rbrakk> \<Longrightarrow> rep_of l i = rep_of l (l!i)"
  apply (subst rep_of.psimps)
  apply (auto dest: ufa_invarD)
  done

lemmas rep_of_simps = rep_of_refl rep_of_step

lemma rep_of_iff: "\<lbrakk>ufa_invar l; i<length l\<rbrakk> 
  \<Longrightarrow> rep_of l i = (if l!i=i then i else rep_of l (l!i))"
  by (simp add: rep_of_simps)

text {* We derive a custom induction rule, that is more suited to
  our purposes. *}
lemma rep_of_induct[case_names base step, consumes 2]:
  assumes I: "ufa_invar l" 
  assumes L: "i<length l"
  assumes BASE: "\<And>i. \<lbrakk> ufa_invar l; i<length l; l!i=i \<rbrakk> \<Longrightarrow> P l i"
  assumes STEP: "\<And>i. \<lbrakk> ufa_invar l; i<length l; l!i\<noteq>i; P l (l!i) \<rbrakk> 
    \<Longrightarrow> P l i"
  shows "P l i"
proof -
  from ufa_invarD[OF I L] have "ufa_invar l \<and> i<length l \<longrightarrow> P l i"
    apply (induct l\<equiv>l i rule: rep_of.pinduct)
    apply (auto intro: STEP BASE dest: ufa_invarD)
    done
  thus ?thesis using I L by simp
qed

text {* In the following, we define various properties of @{text "rep_of"}. *}
lemma rep_of_min: 
  "\<lbrakk> ufa_invar l; i<length l \<rbrakk> \<Longrightarrow> l!(rep_of l i) = rep_of l i"
proof -
  have "\<lbrakk>rep_of_dom (l,i) \<rbrakk> \<Longrightarrow> l!(rep_of l i) = rep_of l i"
    apply (induct arbitrary:  rule: rep_of.pinduct)
    apply (subst rep_of.psimps, assumption)
    apply (subst (2) rep_of.psimps, assumption)
    apply auto
    done 
  thus "\<lbrakk> ufa_invar l; i<length l \<rbrakk> \<Longrightarrow> l!(rep_of l i) = rep_of l i"
    by (metis ufa_invarD(1))
qed

lemma rep_of_bound: 
  "\<lbrakk> ufa_invar l; i<length l \<rbrakk> \<Longrightarrow> rep_of l i < length l"
  apply (induct rule: rep_of_induct)
  apply (auto simp: rep_of_iff)
  done

lemma rep_of_idem: 
  "\<lbrakk> ufa_invar l; i<length l \<rbrakk> \<Longrightarrow> rep_of l (rep_of l i) = rep_of l i"
  by (auto simp: rep_of_min rep_of_refl)

lemma rep_of_min_upd: "\<lbrakk> ufa_invar l; x<length l; i<length l \<rbrakk> \<Longrightarrow> 
  rep_of (l[rep_of l x := rep_of l x]) i = rep_of l i"
  by (metis list_update_id rep_of_min)   

lemma rep_of_idx: 
  "\<lbrakk>ufa_invar l; i<length l\<rbrakk> \<Longrightarrow> rep_of l (l!i) = rep_of l i"
  by (metis rep_of_step)

subsubsection {* Abstraction to Partial Equivalence Relation *}
definition ufa_\<alpha> :: "nat list \<Rightarrow> (nat\<times>nat) set" 
  where "ufa_\<alpha> l 
    \<equiv> {(x,y). x<length l \<and> y<length l \<and> rep_of l x = rep_of l y}"

lemma ufa_\<alpha>_equiv[simp, intro!]: "part_equiv (ufa_\<alpha> l)"
  apply rule
  unfolding ufa_\<alpha>_def
  apply (rule symI)
  apply auto
  apply (rule transI)
  apply auto
  done

lemma ufa_\<alpha>_lenD: 
  "(x,y)\<in>ufa_\<alpha> l \<Longrightarrow> x<length l"
  "(x,y)\<in>ufa_\<alpha> l \<Longrightarrow> y<length l"
  unfolding ufa_\<alpha>_def by auto

lemma ufa_\<alpha>_dom[simp]: "Domain (ufa_\<alpha> l) = {0..<length l}"
  unfolding ufa_\<alpha>_def by auto

lemma ufa_\<alpha>_refl[simp]: "(i,i)\<in>ufa_\<alpha> l \<longleftrightarrow> i<length l"
  unfolding ufa_\<alpha>_def
  by simp

lemma ufa_\<alpha>_len_eq: 
  assumes "ufa_\<alpha> l = ufa_\<alpha> l'"  
  shows "length l = length l'"
  by (metis assms le_antisym less_not_refl linorder_le_less_linear ufa_\<alpha>_refl)

subsubsection {* Operations *}
lemma ufa_init_invar: "ufa_invar [0..<n]"
  unfolding ufa_invar_def
  by (auto intro: rep_of.domintros)

lemma ufa_init_correct: "ufa_\<alpha> [0..<n] = {(x,x) | x. x<n}"
  unfolding ufa_\<alpha>_def
  using ufa_init_invar[of n]
  apply (auto simp: rep_of_refl)
  done

lemma ufa_find_correct: "\<lbrakk>ufa_invar l; x<length l; y<length l\<rbrakk> 
  \<Longrightarrow> rep_of l x = rep_of l y \<longleftrightarrow> (x,y)\<in>ufa_\<alpha> l"
  unfolding ufa_\<alpha>_def
  by auto

abbreviation "ufa_union l x y \<equiv> l[rep_of l x := rep_of l y]"

lemma ufa_union_invar:
  assumes I: "ufa_invar l"
  assumes L: "x<length l" "y<length l"
  shows "ufa_invar (ufa_union l x y)"
  unfolding ufa_invar_def
proof (intro allI impI, simp only: length_list_update)
  fix i
  assume A: "i<length l"
  with I have "rep_of_dom (l,i)" by (auto dest: ufa_invarD)

  have "ufa_union l x y ! i < length l" using I L A
    apply (cases "i=rep_of l x")
    apply (auto simp: rep_of_bound dest: ufa_invarD)
    done
  moreover have "rep_of_dom (ufa_union l x y, i)" using I A L
  proof (induct rule: rep_of_induct)
    case (base i)
    thus ?case
      apply -
      apply (rule rep_of.domintros)
      apply (cases "i=rep_of l x")
      apply auto
      apply (rule rep_of.domintros)
      apply (auto simp: rep_of_min)
      done
  next
    case (step i)

    from step.prems `ufa_invar l` `i<length l` `l!i\<noteq>i` 
    have [simp]: "ufa_union l x y ! i = l!i"
      apply (auto simp: rep_of_min rep_of_bound nth_list_update)
      done

    from step show ?case
      apply -
      apply (rule rep_of.domintros)
      apply simp
      done
  qed
  ultimately show 
    "rep_of_dom (ufa_union l x y, i) \<and> ufa_union l x y ! i < length l"
    by blast

qed

lemma ufa_union_aux:
  assumes I: "ufa_invar l"
  assumes L: "x<length l" "y<length l" 
  assumes IL: "i<length l"
  shows "rep_of (ufa_union l x y) i = 
    (if rep_of l i = rep_of l x then rep_of l y else rep_of l i)"
  using I IL
proof (induct rule: rep_of_induct)
  case (base i)
  have [simp]: "rep_of l i = i" using `l!i=i` by (simp add: rep_of_refl)
  note [simp] = `ufa_invar l` `i<length l`
  show ?case proof (cases)
    assume A[simp]: "rep_of l x = i"
    have [simp]: "l[i := rep_of l y] ! i = rep_of l y" 
      by (auto simp: rep_of_bound)

    show ?thesis proof (cases)
      assume [simp]: "rep_of l y = i" 
      show ?thesis by (simp add: rep_of_refl)
    next
      assume A: "rep_of l y \<noteq> i"
      have [simp]: "rep_of (l[i := rep_of l y]) i = rep_of l y"
        apply (subst rep_of_step[OF ufa_union_invar[OF I L], simplified])
        using A apply simp_all
        apply (subst rep_of_refl[where i="rep_of l y"])
        using I L
        apply (simp_all add: rep_of_min)
        done
      show ?thesis by (simp add: rep_of_refl)
    qed
  next
    assume A: "rep_of l x \<noteq> i"
    hence "ufa_union l x y ! i = l!i" by (auto)
    also note `l!i=i`
    finally have "rep_of (ufa_union l x y) i = i" by (simp add: rep_of_refl)
    thus ?thesis using A by auto
  qed
next    
  case (step i)

  note [simp] = I L `i<length l`

  have "rep_of l x \<noteq> i" by (metis I L(1) rep_of_min `l!i\<noteq>i`)
  hence [simp]: "ufa_union l x y ! i = l!i"
    by (auto simp add: nth_list_update rep_of_bound `l!i\<noteq>i`) []

  have "rep_of (ufa_union l x y) i = rep_of (ufa_union l x y) (l!i)" 
    by (auto simp add: rep_of_iff[OF ufa_union_invar[OF I L]])
  also note step.hyps(4)
  finally show ?case
    by (auto simp: rep_of_idx)
qed
  
lemma ufa_union_correct: "\<lbrakk> ufa_invar l; x<length l; y<length l \<rbrakk> 
  \<Longrightarrow> ufa_\<alpha> (ufa_union l x y) = per_union (ufa_\<alpha> l) x y"
  unfolding ufa_\<alpha>_def per_union_def
  by (auto simp: ufa_union_aux
    split: if_split_asm
  )

lemma ufa_compress_aux:
  assumes I: "ufa_invar l"
  assumes L[simp]: "x<length l"
  shows "ufa_invar (l[x := rep_of l x])" 
  and "\<forall>i<length l. rep_of (l[x := rep_of l x]) i = rep_of l i"
proof -
  {
    fix i
    assume "i<length (l[x := rep_of l x])"
    hence IL: "i<length l" by simp

    have G1: "l[x := rep_of l x] ! i < length (l[x := rep_of l x])"
      using I IL 
      by (auto dest: ufa_invarD[OF I] simp: nth_list_update rep_of_bound)
    from I IL have G2: "rep_of (l[x := rep_of l x]) i = rep_of l i 
      \<and> rep_of_dom (l[x := rep_of l x], i)"
    proof (induct rule: rep_of_induct)
      case (base i)
      thus ?case
        apply (cases "x=i")
        apply (auto intro: rep_of.domintros simp: rep_of_refl)
        done
    next
      case (step i) 
      hence D: "rep_of_dom (l[x := rep_of l x], i)"
        apply -
        apply (rule rep_of.domintros)
        apply (cases "x=i")
        apply (auto intro: rep_of.domintros simp: rep_of_min)
        done
      
      thus ?case apply simp using step
        apply -
        apply (subst rep_of.psimps[OF D])
        apply (cases "x=i")
        apply (auto simp: rep_of_min rep_of_idx)
        apply (subst rep_of.psimps[where i="rep_of l i"])
        apply (auto intro: rep_of.domintros simp: rep_of_min)
        done
    qed
    note G1 G2
  } note G=this

  thus "\<forall>i<length l. rep_of (l[x := rep_of l x]) i = rep_of l i"
    by auto

  from G show "ufa_invar (l[x := rep_of l x])" 
    by (auto simp: ufa_invar_def)
qed

lemma ufa_compress_invar:
  assumes I: "ufa_invar l"
  assumes L[simp]: "x<length l"
  shows "ufa_invar (l[x := rep_of l x])" 
  using assms by (rule ufa_compress_aux)

lemma ufa_compress_correct:
  assumes I: "ufa_invar l"
  assumes L[simp]: "x<length l"
  shows "ufa_\<alpha> (l[x := rep_of l x]) = ufa_\<alpha> l"
  by (auto simp: ufa_\<alpha>_def ufa_compress_aux[OF I])

subsubsection \<open>stuff about the height (by Max Haslbeck)\<close>


function (domintros) height_of 
  where "height_of l i = (if l!i = i then 0::nat else 1 + height_of l (l!i))"
  by pat_completeness auto
print_theorems 

lemma height_of_dom_rep_of_dom[simp]: "height_of_dom (l, i) = rep_of_dom (l, i)"
  apply(rule)
  subgoal 
    apply (induct arbitrary:  rule: height_of.pinduct) 
    apply (rule rep_of.domintros) by simp
  subgoal 
    apply (induct arbitrary:  rule: rep_of.pinduct)
    apply (rule height_of.domintros) by simp
  done

lemma height_of_step: "ufa_invar l \<Longrightarrow>
         i < length l \<Longrightarrow>
         l ! i \<noteq> i \<Longrightarrow>
          height_of l i = Suc (height_of l (l ! i))"  
  by (simp add: height_of.psimps ufa_invarD(1)) 


 

definition "h_of l i = Max {height_of l j|j. j<length l \<and> rep_of l j = i}"

definition invar where
  "invar l sl = (length l = length sl 
              \<and> sum (\<lambda>i. if l!i=i then sl !i else 0) {0..<length l} = length l
              \<and> (\<forall>i<length l. l!i=i \<longrightarrow> (2::nat) ^ h_of l i \<le> sl ! i))"

lemma invar_sli_le_l:
  assumes "invar l sl" "ufa_invar l" "i<length l"
  shows "sl ! (rep_of l i) \<le> length l"
proof -
  from assms(1) have a: "sum (\<lambda>i. if l!i=i then sl !i else 0) {0..<length l} = length l"
      and len: "length sl = length l" by(auto simp: invar_def)

  let ?r = "(rep_of l i)"
  from assms have "?r<length l" by(auto simp: rep_of_bound)    
  then have f: "{0..<length l} = {?r} \<union> ({0..<length l}-{?r})" by auto
  have "sl ! (?r) \<le> sum (\<lambda>i. if l!i=i then sl !i else 0) ({0..<length l}-{?r}) + (if l!?r=?r then sl !?r else 0)"
    using assms by (auto simp: rep_of_min) 
  also have "\<dots> = sum (\<lambda>i. if l!i=i then sl !i else 0) {0..<length l}"
    apply(subst (2) f) apply(subst sum_Un_nat) by simp_all
  also have "\<dots> = length l" using a by simp
  finally show "sl ! (rep_of l i) \<le> length l" .
qed



lemma h_rep: "ufa_invar l \<Longrightarrow> y<length l\<Longrightarrow> height_of l (rep_of l y) = 0"
  apply (subst height_of.psimps) subgoal by (simp add: rep_of_bound ufa_invarD(1) ufa_union_invar )   
  by (simp add: rep_of_min) 




lemma ufa_compress_compresses:
  "\<lbrakk>ufa_invar l; i<length l; j<length l\<rbrakk> \<Longrightarrow>
      height_of (l[j:=rep_of l j]) i \<le> height_of l i"
  proof (induct rule: rep_of_induct)
    case (base i)
    then show ?case
      apply(subst height_of.psimps)  subgoal apply simp apply(rule ufa_invarD(1)) by(auto simp add: ufa_compress_invar)
      apply (auto simp add: rep_of_refl) 
      by (metis nth_list_update' rep_of_iff) 
  next
    case (step i)
    show ?case 
      apply(subst height_of.psimps)  subgoal using step by (simp add: ufa_invarD(1) ufa_compress_invar )
      apply auto 
      apply(subst (2) height_of.psimps)  subgoal using step by (simp add: rep_of_bound ufa_invarD(1) ufa_compress_invar )
      using step(1-3) apply auto
      apply(cases "i=j")
      subgoal apply simp apply(subst height_of.psimps) subgoal by (simp add: rep_of_bound ufa_compress_invar ufa_invarD(1))   
      using rep_of_min by auto  
    subgoal apply simp apply(rule step(4)) using step by auto
    done
  qed                                                                                  

lemma ufa_union_on_path_only_increases_by_one:
  "\<lbrakk>ufa_invar l; i<length l; x<length l; y<length l; rep_of l i = rep_of l x\<rbrakk> \<Longrightarrow> 
      height_of (ufa_union l x y) i \<le> Suc (height_of l i)"
proof (induct rule: rep_of_induct)
  case (base i)
  then show ?case
    apply(cases "i=rep_of l x")
    subgoal
      apply(subst height_of.psimps)  subgoal by (simp add: ufa_invarD(1) ufa_union_invar )  
      apply simp
      apply (auto simp add:   )[]
       apply(subst height_of.psimps) subgoal by (simp add: rep_of_bound ufa_invarD(1) ufa_union_invar)  
      apply (auto simp: h_rep)[] by(simp add: rep_of_min)
    subgoal 
      apply(subst height_of.psimps)  subgoal apply simp  
        by (simp add: ufa_invarD(1) ufa_union_invar)  
      by simp 
    done
next
  case (step i)
  then have not: "i\<noteq>rep_of l x" 
    using rep_of_min by blast 

  show ?case
    apply(subst height_of.psimps)  subgoal using step by (simp add: ufa_invarD(1) ufa_union_invar ) 
    using not apply simp
    apply(subst (2) height_of.psimps)  subgoal using step by (simp add: rep_of_bound ufa_invarD(1) ufa_union_invar ) 
    apply simp apply safe
     apply(rule step(4)) using step 
    by (auto simp add: rep_of_idx) 
qed

lemma ufa_union_not_on_path_stays:
  "\<lbrakk>ufa_invar l; i<length l; x<length l; y<length l; rep_of l i \<noteq> rep_of l x\<rbrakk> \<Longrightarrow> 
      height_of (ufa_union l x y) i = height_of l i"
proof (induct rule: rep_of_induct)
  case (base i)
  then show ?case
    apply(cases "i=rep_of l x")
    subgoal
      by (auto simp add:  h_rep  rep_of_iff)  
    subgoal 
      apply(subst height_of.psimps)  subgoal apply simp  
        by (simp add: ufa_invarD(1) ufa_union_invar) 
      apply auto
      apply(subst height_of.psimps)  subgoal apply simp  
        by (simp add: ufa_invarD(1) ufa_union_invar)  
      by simp 
    done
next
  case (step i)
  then have not: "i\<noteq>rep_of l x" 
    using rep_of_min by blast 

  show ?case
    apply(subst height_of.psimps)  subgoal using step by (simp add: ufa_invarD(1) ufa_union_invar ) 
    using not step(1-3) apply auto
    apply(subst (2) height_of.psimps)  subgoal using step by (simp add: rep_of_bound ufa_invarD(1) ufa_union_invar ) 
    apply simp 
     apply(rule step(4)) using step 
    by (auto simp add: rep_of_idx) 
qed


lemma ufa_union_on_path:
"\<lbrakk>ufa_invar l; i<length l; x<length l; y<length l\<rbrakk> \<Longrightarrow> 
      height_of (ufa_union l x y) i \<le> Suc (height_of l i)"
  proof (induct rule: rep_of_induct)
    case (base i)
    then show ?case
      apply(cases "i=rep_of l x")
      subgoal
      apply(subst height_of.psimps)  subgoal by (simp add: ufa_invarD(1) ufa_union_invar )  
      apply (auto simp add:   )[]
        apply(subst height_of.psimps) subgoal by (simp add: rep_of_bound ufa_invarD(1) ufa_union_invar)  
        apply auto[] by(simp add: rep_of_min)
      subgoal 
        apply(subst height_of.psimps)  subgoal apply simp  
          by (simp add: ufa_invarD(1) ufa_union_invar)  
        by simp 
      done
  next
    case (step i)
    then have not: "i\<noteq>rep_of l x" 
      using rep_of_min by blast 

    show ?case
      apply(subst height_of.psimps)  subgoal using step by (simp add: ufa_invarD(1) ufa_union_invar ) 
      using not apply simp
      apply(subst (2) height_of.psimps)  subgoal using step by (simp add: rep_of_bound ufa_invarD(1) ufa_union_invar ) 
      apply simp apply safe
      apply(rule step(4)) using step by auto
  qed


lemma hel: "(\<And>x. x\<in>A \<Longrightarrow> f x \<le> g x) \<Longrightarrow> finite A  \<Longrightarrow> MAXIMUM A f \<le> MAXIMUM A g"  
  by (smt Max_ge_iff Max_in finite_imageI imageE image_eqI image_is_empty order_refl)  
lemma MAXIMUM_mono: "(\<And>x. x\<in>A \<Longrightarrow> f x \<le> g x) \<Longrightarrow> finite A  \<Longrightarrow> A = B \<Longrightarrow> MAXIMUM A f \<le> MAXIMUM B g"  
  using hel by blast 
lemma MAXIMUM_eq: "(\<And>x. x\<in>A \<Longrightarrow> f x = g x) \<Longrightarrow> finite A  \<Longrightarrow> A = B \<Longrightarrow> MAXIMUM A f = MAXIMUM B g"  
  apply(rule antisym) by  (auto intro: MAXIMUM_mono)





lemma h_of_alt: "h_of l i = MAXIMUM {j|j. j<length l \<and> rep_of l j = i} (height_of l)"
  unfolding h_of_def 
  by (simp add: setcompr_eq_image) 
 

lemma h_of_compress: "ufa_invar l \<Longrightarrow> j < length l \<Longrightarrow> h_of (l[j:=rep_of l j]) i \<le>  h_of l i"
  unfolding h_of_alt 
  apply(rule MAXIMUM_mono)
  subgoal apply(rule ufa_compress_compresses) by auto
  by (auto simp add: ufa_compress_aux(2))   


lemma h_of_uf_union_untouched:
  "ufa_invar l \<Longrightarrow> x < length l \<Longrightarrow> y < length l \<Longrightarrow> i < length l \<Longrightarrow> l!i = i 
    \<Longrightarrow> i \<noteq> rep_of l x \<Longrightarrow> i \<noteq> rep_of l y   \<Longrightarrow> h_of (ufa_union l x y) i = h_of l i"
  unfolding h_of_alt 
  apply(rule MAXIMUM_eq)
  subgoal apply(rule ufa_union_not_on_path_stays)  
    using ufa_union_aux by auto  
  using ufa_union_aux by auto
 

lemma Suc_h_of: assumes
  a:  "i < length l " "rep_of l i = i"
  shows 
  "Suc (h_of l i) = MAXIMUM {j|j. j<length l \<and> rep_of l j = i} (\<lambda>j. Suc (height_of l j))"
  unfolding h_of_alt  
  apply(subst  mono_Max_commute[where f=Suc]) 
  subgoal by (simp add: mono_Suc)
  subgoal by simp
  subgoal using a by auto  
  by (simp add: image_image) 

lemma MAXIMUM_Un: "finite A \<Longrightarrow> finite B \<Longrightarrow> A \<noteq> {} \<Longrightarrow> B \<noteq> {} 
  \<Longrightarrow> MAXIMUM (A \<union> B) f = max (MAXIMUM A f) (MAXIMUM B f)"
  apply(simp add: image_Un)
  apply(subst Max_Un) by auto


lemma fixes A::nat 
  shows "A\<le>A' \<Longrightarrow> B\<le>B' \<Longrightarrow> max A B \<le> max A' B'"    
  by auto  
 


lemma h_of_uf_union_id:
  assumes "ufa_invar l "" x < length l "" y < length l "" i < length l "
    " rep_of l i = i" "i = rep_of l y" and neq: "rep_of l y = rep_of l x"
  shows "h_of (ufa_union l x y) i = h_of l i"
  using neq apply simp using assms  
  by (metis list_update_id rep_of_min)  


lemma h_of_uf_union_touched:
  assumes "ufa_invar l "" x < length l "" y < length l "" i < length l "
    " rep_of l i = i" "i = rep_of l y" and neq: "rep_of l y \<noteq> rep_of l x"
  shows "h_of (ufa_union l x y) i \<le> max (h_of l (rep_of l y)) (Suc (h_of l (rep_of l x)))"
proof -
  have *: "{j|j. j<length (ufa_union l x y) \<and> rep_of (ufa_union l x y) j = i}
      = {j|j. j<length (ufa_union l x y) \<and> rep_of (ufa_union l x y) j = i \<and> rep_of l j = rep_of l y}
          \<union> {j|j. j<length (ufa_union l x y) \<and> rep_of (ufa_union l x y) j = i \<and> rep_of l j = rep_of l x}" (is "_ = ?A \<union> ?B")
    apply auto using assms  
    by (simp add: ufa_union_aux)  

  have A: "?A = {j |j. j < length l \<and> rep_of l j = rep_of l y}"
    using ufa_union_aux assms by auto
  have B: "?B = {j |j. j < length l \<and> rep_of l j = rep_of l x}"
    using ufa_union_aux assms by auto

  have "h_of (ufa_union l x y) i = MAXIMUM {j|j. j<length (ufa_union l x y) \<and> rep_of (ufa_union l x y) j = i} (height_of (ufa_union l x y))"
    unfolding h_of_alt by simp
  also have "\<dots> = MAXIMUM (?A \<union> ?B) (height_of (ufa_union l x y))"
    unfolding * by simp
  also have "\<dots> = max (MAXIMUM ?A (height_of (ufa_union l x y))) (MAXIMUM ?B (height_of (ufa_union l x y)))"
    apply(subst MAXIMUM_Un) apply simp_all
    subgoal  apply(rule exI[where x=y]) using assms by (simp add: ufa_union_aux)  
    subgoal  apply(rule exI[where x=x]) using assms by (simp add: ufa_union_aux)  
    done
  also have "\<dots> \<le> max (MAXIMUM ?A (height_of l)) (MAXIMUM ?B (\<lambda>j. Suc (height_of l j)))"
    apply(rule max.mono)
    subgoal apply(rule MAXIMUM_mono)
      subgoal apply(rule order_eq_refl) apply(rule ufa_union_not_on_path_stays) using assms by auto  
      by simp_all 
    subgoal apply(rule MAXIMUM_mono)
      subgoal apply(rule ufa_union_on_path)  using assms by auto
       apply simp by simp
    done
  also have "\<dots> \<le> max  (h_of l (rep_of l y)) (Suc (h_of l (rep_of l x)))"
    apply(rule max.mono)
    subgoal unfolding h_of_alt A by simp
    subgoal apply(subst Suc_h_of)
      subgoal using assms by (auto simp: rep_of_min rep_of_bound rep_of_refl)
      subgoal using assms by (auto simp: rep_of_min rep_of_bound rep_of_refl)  
      unfolding B by simp
    done
  finally show ?thesis .
qed 

lemma height_of_le_h_of: "i < length l \<Longrightarrow> height_of l i \<le> h_of l (rep_of l i)"
    unfolding h_of_def apply(rule Max.coboundedI) apply simp
    apply(subst setcompr_eq_image) apply(rule imageI)
    by auto




lemma height_of_ub: assumes "invar l sl" "ufa_invar l" "i<length l"
  shows "2 ^ (height_of l i) \<le> length l"
proof -
  from assms(1) have "length l = length sl "
            and 2:  "sum (\<lambda>i. if l!i=i then sl !i else 0) {0..<length l} = length l"
            and 3:  "\<And>i. i<length l \<Longrightarrow>  l!i=i \<Longrightarrow> (2::nat) ^ h_of l i \<le> sl ! i"
    unfolding invar_def  by auto

  have *: "height_of l i \<le> h_of l (rep_of l i)"     
    using assms by (auto intro: height_of_le_h_of)

  have "(2::nat) ^ (height_of l i) \<le> 2 ^ (h_of l (rep_of l i))"
    apply(rule power_increasing) apply(rule *) by simp
  also have "\<dots> \<le> sl ! (rep_of l i)"
   using 3 assms by(auto simp add: rep_of_bound rep_of_min )   
  also have "\<dots> \<le> length l" using assms 
    by (auto simp: rep_of_bound intro: invar_sli_le_l) 
  finally show ?thesis .
qed
    


subsection {* Implementation with Imperative/HOL *}
text {* In this section, we implement the union-find data-structure with
  two arrays, one holding the next-pointers, and another one holding the size
  information. Note that we do not prove that the array for the 
  size information contains any reasonable values, as the correctness of the
  algorithm is not affected by this. We leave it future work to also estimate
  the complexity of the algorithm.
*}

type_synonym uf = "nat array \<times> nat array"

definition is_uf :: "(nat\<times>nat) set \<Rightarrow> uf \<Rightarrow> assn" where 
  "is_uf R u \<equiv> case u of (s,p) \<Rightarrow> 
  \<exists>\<^sub>Al szl. p\<mapsto>\<^sub>al * s\<mapsto>\<^sub>aszl 
    * \<up>(ufa_invar l \<and> ufa_\<alpha> l = R \<and> length szl = length l \<and> invar l szl)"

definition uf_init :: "nat \<Rightarrow> uf Heap" where 
  "uf_init n \<equiv> do {
    l \<leftarrow> Array.of_list [0..<n];
    szl \<leftarrow> Array.new n (1::nat);
    return (szl,l)
  }"

lemma of_list_rule':
    "<$ (1 + n)> Array.of_list [0..<n] <\<lambda>r. r \<mapsto>\<^sub>a [0..<n]>"
  using of_list_rule[of "[0..<n]"] by auto 

lemma height_of_init: "j<n \<Longrightarrow> height_of [0..<n] j = 0"
  by (simp add: height_of.psimps ufa_init_invar ufa_invarD(1))

lemma h_of_init: "i < n \<Longrightarrow> h_of [0..<n] i = 0"
  unfolding h_of_def apply auto
  apply(rule antisym) 
  subgoal apply(rule Max.boundedI)
     apply simp
    using ufa_init_invar apply auto apply(rule exI[where x=i]) apply simp
    subgoal  
      by (simp add: rep_of_refl)  
    apply(rule height_of_init) by simp
  by simp 

lemma ufa_init_invar': "invar [0..<n] (replicate n (Suc 0))"
  unfolding invar_def apply auto using h_of_init by auto

definition uf_init_time :: "nat \<Rightarrow> nat" where "uf_init_time n == (2*n+3)"

lemma uf_init_bound[asym_bound]: "uf_init_time \<in> \<Theta>(\<lambda>n. n)" 
  unfolding uf_init_time_def by auto2

lemma uf_init_rule: 
  "<$(uf_init_time n)> uf_init n <is_uf {(i,i) |i. i<n}>\<^sub>t"
  unfolding uf_init_time_def uf_init_def is_uf_def[abs_def]
  by (sep_auto simp: ufa_init_correct ufa_init_invar ufa_init_invar' zero_time heap: of_list_rule')
 


partial_function (heap) uf_rep_of :: "nat array \<Rightarrow> nat \<Rightarrow> nat Heap" 
  where [code]: 
  "uf_rep_of p i = do {
    n \<leftarrow> Array.nth p i;
    if n=i then return i else uf_rep_of p n
  }"


lemma uf_rep_of_rule: "\<lbrakk>ufa_invar l; i<length l\<rbrakk> \<Longrightarrow>
  <p\<mapsto>\<^sub>al * $(height_of l i + 2)> uf_rep_of p i <\<lambda>r. p\<mapsto>\<^sub>al * \<up>(r=rep_of l i)>\<^sub>t"
  apply (induct rule: rep_of_induct)
  apply (subst uf_rep_of.simps)
  apply (sep_auto simp: rep_of_refl)

  apply (subst uf_rep_of.simps)
  apply (sep_auto simp: rep_of_step height_of_step)
  done

text {* We chose a non tail-recursive version here, as it is easier to prove. *}
partial_function (heap) uf_compress :: "nat \<Rightarrow> nat \<Rightarrow> nat array \<Rightarrow> unit Heap" 
  where [code]: 
  "uf_compress i ci p = (
    if i=ci then return ()
    else do {
      ni\<leftarrow>Array.nth p i;
      uf_compress ni ci p;
      Array.upd i ci p;
      return ()
    })"

lemma compress_invar:
  assumes "invar l szl"
    "ufa_invar l" "i<length l"
  shows "invar (l[i := rep_of l i]) szl"
  using assms unfolding invar_def
  apply safe
  subgoal by simp
  subgoal apply simp  
    by (smt nth_list_update_eq nth_list_update_neq rep_of_iff rep_of_min sum.ivl_cong)  
  subgoal for i
    apply(rule order.trans)
    apply(rule power_increasing[where N="h_of l i"])
    subgoal apply(rule h_of_compress) by auto
     apply simp
    apply simp  
    by (metis nth_list_update_eq nth_list_update_neq rep_of_min)
  done





lemma uf_compress_rule: "\<lbrakk> ufa_invar l; i<length l; ci=rep_of l i; invar l szl \<rbrakk> \<Longrightarrow>
  <p\<mapsto>\<^sub>al *  $(1+height_of l i*3)> uf_compress i ci p 
  <\<lambda>_. (\<exists>\<^sub>Al'. p\<mapsto>\<^sub>al' * \<up>(invar l' szl \<and> ufa_invar l' \<and> length l' = length l 
     \<and> (\<forall>i<length l. rep_of l' i = rep_of l i)))>\<^sub>t"
proof (induction rule: rep_of_induct)
  case (base i) thus ?case
    apply (subst uf_compress.simps)
    apply (sep_auto simp: rep_of_refl)
    done
next
  case (step i)
  note SS = `ufa_invar l` `i<length l` `l!i\<noteq>i` `ci = rep_of l i` `invar l szl`

   
  have IH': 
    "<p \<mapsto>\<^sub>a l * $ (1 + height_of l (l ! i) *3)> 
       uf_compress (l ! i) (rep_of l i) p
     <\<lambda>_.  (\<exists>\<^sub>Al'. p \<mapsto>\<^sub>a l' * 
        \<up> (invar l' szl \<and>ufa_invar l' \<and> length l' = length l 
           \<and> (\<forall>i<length l'. rep_of l i = rep_of l' i)))
     >\<^sub>t"   
    apply(rule pre_rule[OF _ post_rule[OF step.IH[simplified SS rep_of_idx] ]] ) 
    by (sep_auto simp add: rep_of_idx SS)+  

  show ?case
    apply (subst uf_compress.simps)
    apply (sep_auto simp: SS height_of_step heap: )
    apply(sep_auto heap: IH') 
 
    using SS apply (sep_auto  ) 
    subgoal using compress_invar by simp
    subgoal using ufa_compress_invar by fastforce
    subgoal by simp
    subgoal using ufa_compress_aux(2) by fastforce
    done
qed

definition uf_rep_of_c :: "nat array \<Rightarrow> nat \<Rightarrow> nat Heap"
  where "uf_rep_of_c p i \<equiv> do {
    ci\<leftarrow>uf_rep_of p i;
    uf_compress i ci p;
    return ci
  }"

lemma uf_rep_of_c_rule: "\<lbrakk>ufa_invar l; i<length l; invar l szl\<rbrakk> \<Longrightarrow>
  <p\<mapsto>\<^sub>al * $(4+height_of l i*4)> uf_rep_of_c p i <\<lambda>r.  (\<exists>\<^sub>Al'. p\<mapsto>\<^sub>al' 
    * \<up>(r=rep_of l i \<and> ufa_invar l' \<and> invar l' szl
       \<and> length l' = length l 
       \<and> (\<forall>i<length l. rep_of l' i = rep_of l i)))>\<^sub>t"
  unfolding uf_rep_of_c_def
  by (sep_auto heap: uf_compress_rule uf_rep_of_rule) 

thm height_of_ub

definition height_ub :: "nat \<Rightarrow> nat" where "height_ub n = nat (ceiling (log 2 n))"


lemma height_ub_bound[asym_bound]: "height_ub \<in> \<Theta>(\<lambda>n. ln n)"
  unfolding height_ub_def using abcd_lnx[of 0 1 1 0] by auto

lemma height_ub:
  assumes "invar l sl" "ufa_invar l" "i<length l"
  shows "height_of l i \<le> height_ub (length l)"
proof -
  from height_of_ub[OF assms] have "2 ^ height_of l i \<le> length l" .
  from le_log2_of_power[OF this]
    show ?thesis unfolding height_ub_def by linarith
  qed



lemma uf_rep_of_c_rule_ub: 
  assumes "ufa_invar l"  "i<length l" "invar l szl"
  shows "<p\<mapsto>\<^sub>al * $(4+ height_ub (length l)*4)> uf_rep_of_c p i <\<lambda>r. (\<exists>\<^sub>Al'. p\<mapsto>\<^sub>al' 
    * \<up>(r=rep_of l i \<and> ufa_invar l' \<and> invar l' szl
       \<and> length l' = length l 
       \<and> (\<forall>i<length l. rep_of l' i = rep_of l i))) >\<^sub>t"
proof -
  from assms height_ub have "height_of l i \<le> height_ub (length l)" by auto
  then obtain x where p: "height_ub (length l) = height_of l i + x"  
    using le_Suc_ex by blast  
  show ?thesis unfolding p
    using assms by(sep_auto heap: uf_rep_of_c_rule)
qed





definition uf_cmp :: "uf \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool Heap" where 
  "uf_cmp u i j \<equiv> do {
    let (s,p)=u;
    n\<leftarrow>Array.len p;
    if (i\<ge>n \<or> j\<ge>n) then return False
    else do {
      ci\<leftarrow>uf_rep_of_c p i;
      cj\<leftarrow>uf_rep_of_c p j;
      return (ci=cj)
    }
  }"

lemma cnv_to_ufa_\<alpha>_eq: 
  "\<lbrakk>(\<forall>i<length l. rep_of l' i = rep_of l i); length l = length l'\<rbrakk> 
  \<Longrightarrow> (ufa_\<alpha> l = ufa_\<alpha> l')"
  unfolding ufa_\<alpha>_def by auto

lemma "  card (Domain (ufa_\<alpha> l)) = length l"
  by simp

definition uf_cmp_time :: "nat \<Rightarrow> nat" where "uf_cmp_time n = 10+ height_ub n*8"

lemma uf_cmp_time_bound[asym_bound]: 
  "uf_cmp_time \<in> \<Theta>(\<lambda>n. ln n)" unfolding uf_cmp_time_def by auto2 

lemma uf_cmp_rule:
  "<is_uf R u * $(uf_cmp_time (card (Domain R)))> uf_cmp u i j <\<lambda>r. is_uf R u * \<up>(r\<longleftrightarrow>(i,j)\<in>R)>\<^sub>t" 
  unfolding uf_cmp_def is_uf_def uf_cmp_time_def
  apply (sep_auto heap: uf_rep_of_c_rule_ub length_rule dest: ufa_\<alpha>_lenD simp: not_le split: prod.split)
   apply(rule fi_rule[OF uf_rep_of_c_rule_ub]) defer defer defer
      apply(simp only: mult.assoc)
  apply(rule match_first) apply sep_auto
      apply(timeframeinf)
     defer apply simp apply simp apply simp
  apply(sep_auto) 
  apply (drule cnv_to_ufa_\<alpha>_eq, simp_all)
  apply (drule cnv_to_ufa_\<alpha>_eq, simp_all)
  apply (drule cnv_to_ufa_\<alpha>_eq, simp_all)
  apply (drule cnv_to_ufa_\<alpha>_eq, simp_all)
  apply (drule cnv_to_ufa_\<alpha>_eq, simp_all)
  apply (drule cnv_to_ufa_\<alpha>_eq, simp_all)
  apply (subst ufa_find_correct)
  apply (auto simp add: )
  done 
  

definition uf_union :: "uf \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> uf Heap" where 
  "uf_union u i j \<equiv> do {
    let (s,p)=u;
    ci \<leftarrow> uf_rep_of p i;
    cj \<leftarrow> uf_rep_of p j;
    if (ci=cj) then return (s,p) 
    else do {
      si \<leftarrow> Array.nth s ci;
      sj \<leftarrow> Array.nth s cj;
      if si<sj then do {
        Array.upd ci cj p;
        Array.upd cj (si+sj) s;
        return (s,p)
      } else do { 
        Array.upd cj ci p;
        Array.upd ci (si+sj) s;
        return (s,p)
      }
    }
  }"



lemma uf_rep_of_rule_ub: assumes "ufa_invar l" "i<length l"  "invar l szl"
  shows "<p\<mapsto>\<^sub>al * $(height_ub (length l) + 2)> uf_rep_of p i <\<lambda>r. p\<mapsto>\<^sub>al * \<up>(r=rep_of l i)>\<^sub>t"
proof -
  from assms height_ub have "height_of l i \<le> height_ub (length l)" by auto
  then obtain x where p: "height_ub (length l) = height_of l i + x"  
    using le_Suc_ex by blast  
  show ?thesis unfolding p
    using assms by(sep_auto heap: uf_rep_of_rule)
qed




lemma 12:
  assumes "i < length l " "j < length l" 
       "ufa_invar l " "(i, j) \<notin> ufa_\<alpha> l "
     and size:  "szl ! rep_of l i < szl ! rep_of l j  "
  and i:  "invar l szl "
      shows "invar (ufa_union l i j) (szl[rep_of l j := szl ! rep_of l i + szl ! rep_of l j])"
proof - 
  let ?upd = "ufa_union l i j"

  from i have [simp]: "length szl = length l" unfolding invar_def by auto

  { fix a b and f :: "'a\<Rightarrow>nat" have r: "a\<noteq>b \<Longrightarrow> sum f {a,b}   = f a + f b" by simp     }
  note ff=this

  have *: "{0..<length l} = ({0..<length l}-{rep_of l j}) \<union> {rep_of l j}" 
    using assms rep_of_bound by auto  
  have **:"{0..<length l} = ({0..<length l}-{rep_of l i,rep_of l j}) \<union> {rep_of l i,rep_of l j}" 
    using assms rep_of_bound by auto  

  have ss: "(({0..<length l} - {rep_of l j}) \<inter> {ia. ?upd ! ia = ia})
        = ({0..<length l}-{rep_of l i,rep_of l j}) \<inter> {ia. l ! ia = ia}" using assms by (auto simp: nth_list_update') 


  have "(\<Sum>ia = 0..<length l. if ?upd ! ia = ia then szl[rep_of l j := szl ! rep_of l i + szl ! rep_of l j] ! ia else 0)
     = sum (\<lambda>ia. if ?upd ! ia = ia then szl[rep_of l j := szl ! rep_of l i + szl ! rep_of l j] ! ia else 0) ({0..<length l}-{rep_of l j})
            + (szl ! rep_of l i + szl ! rep_of l j)" (is "?A = _")
    apply(subst *)  apply(subst sum_Un_nat) apply simp apply simp apply simp
    apply safe 
    subgoal using assms rep_of_bound  
      using invar_def by fastforce  
    subgoal using assms  
      by (simp add: rep_of_min ufa_find_correct)  
    subgoal using assms  
      by (simp add: rep_of_min ufa_find_correct) 
    done 
  also have "\<dots> = sum (\<lambda>i. if l ! i = i then szl ! i else 0)
                         ({0..<length l}-{rep_of l i,rep_of l j})
               + (szl ! rep_of l i + szl ! rep_of l j)" (is "?L + _ = ?R + _")
  proof -
    have "?L = sum (\<lambda>ia. szl[rep_of l j := szl ! rep_of l i + szl ! rep_of l j] ! ia)
                 (({0..<length l}-{rep_of l j})\<inter>{ia. ?upd ! ia = ia})"
      apply(subst sum.inter_restrict) by simp_all
    also have "\<dots> = sum (\<lambda>ia. szl[rep_of l j := szl ! rep_of l i + szl ! rep_of l j] ! ia)
                 (({0..<length l}-{rep_of l i,rep_of l j}) \<inter> {ia. l ! ia = ia})"
      unfolding ss by simp
    also have "\<dots> = ?R"
      apply(subst sum.inter_restrict) apply simp apply auto apply(rule sum.cong) apply simp using assms by auto  
    finally have "?L = ?R" .
    then show ?thesis by simp
  qed  
  also have "\<dots> = (\<Sum>i = 0..<length l. if l ! i = i then szl ! i else 0)"
    apply(subst (2) **) apply(subst sum_Un_nat) apply simp apply simp apply simp
    apply(subst ff) using assms apply (auto simp: rep_of_min) 
    done
  also from i have "\<dots> = length l" unfolding invar_def by auto
  finally have A: "?A = length l" .
    
  have max_distrib: "\<And>a b :: nat. (2::nat) ^ max a b = max (2 ^ a) (2 ^ b)" 
    by (simp add: max_def)  
  { 
    assume a: "rep_of l j < length szl" "?upd ! rep_of l j = rep_of l j"  
    
    from i have g: "\<And>i. i<length l \<Longrightarrow> l ! i = i \<Longrightarrow> 2 ^ h_of l i \<le> szl ! i" unfolding invar_def by metis
    
    have "(2::nat) ^ (max (h_of l (rep_of l j)) (Suc (h_of l (rep_of l i))))
          \<le> max ( (szl ! (rep_of l j))) (2 * (szl ! (rep_of l i)))"
      apply(subst max_distrib) 
      apply(rule max.mono)
      subgoal apply(rule g) using assms a by (auto simp: rep_of_min)    
      subgoal apply(simp only: power.power_Suc) apply(rule mult_left_mono)
        apply(rule g) using assms a by (auto simp: rep_of_refl rep_of_min rep_of_bound)    
      done
    also have "\<dots> \<le> szl ! rep_of l i + szl ! rep_of l j"
      using size by auto
    finally
    have "2 ^ max (h_of l (rep_of l j)) (Suc (h_of l (rep_of l i))) \<le> szl ! rep_of l i + szl ! rep_of l j"
      .
  } note absch = this

  show ?thesis unfolding invar_def
    apply safe
    subgoal using i[unfolded invar_def] by simp
    subgoal apply simp using A by simp
    subgoal for i apply(cases "i=rep_of l j")
      subgoal apply simp
        apply(rule order.trans)
         apply(rule power_increasing[OF h_of_uf_union_touched])
                prefer 9
        subgoal using absch by simp
        using assms by (auto simp: rep_of_idem) 
      subgoal 
        apply simp apply(subst h_of_uf_union_untouched) 
               prefer 8 subgoal
          using i unfolding invar_def 
          by (metis nth_list_update')            
        using assms apply (auto simp: rep_of_idem )  
        by (metis nth_list_update')  
      done
    done
qed

lemma 21:
  assumes "i < length l "" j < length l ""
       ufa_invar l "
       "(i, j) \<notin> ufa_\<alpha> l "
   and size: "\<not> szl ! rep_of l i < szl ! rep_of l j  "
  and i: "invar l szl "
      shows "invar (ufa_union l j i) (szl[rep_of l i := szl ! rep_of l i + szl ! rep_of l j])"
proof - 
  let ?upd = "ufa_union l j i"

  from i have [simp]: "length szl = length l" unfolding invar_def by auto

  { fix a b and f :: "'a\<Rightarrow>nat" have r: "a\<noteq>b \<Longrightarrow> sum f {a,b}   = f a + f b" by simp     }
  note ff=this

  have *: "{0..<length l} = ({0..<length l}-{rep_of l i}) \<union> {rep_of l i}" 
    using assms rep_of_bound by auto  
  have **:"{0..<length l} = ({0..<length l}-{rep_of l i,rep_of l j}) \<union> {rep_of l i,rep_of l j}" 
    using assms rep_of_bound by auto  

  have ss: "(({0..<length l} - {rep_of l i}) \<inter> {ia. ?upd ! ia = ia})
        = ({0..<length l}-{rep_of l i,rep_of l j}) \<inter> {ia. l ! ia = ia}" using assms by (auto simp: nth_list_update') 


  have "(\<Sum>ia = 0..<length l. if ?upd ! ia = ia then szl[rep_of l i := szl ! rep_of l i + szl ! rep_of l j] ! ia else 0)
     = sum (\<lambda>ia. if ?upd ! ia = ia then szl[rep_of l i := szl ! rep_of l i + szl ! rep_of l j] ! ia else 0) ({0..<length l}-{rep_of l i})
            + (szl ! rep_of l i + szl ! rep_of l j)" (is "?A = _")
    apply(subst *)  apply(subst sum_Un_nat) apply simp apply simp apply simp
    apply safe 
    subgoal using assms rep_of_bound  
      using invar_def by fastforce  
    subgoal using assms   
      using rep_of_min ufa_find_correct by fastforce  
    subgoal using assms  
      using rep_of_min ufa_find_correct by fastforce   
    done 
  also have "\<dots> = sum (\<lambda>i. if l ! i = i then szl ! i else 0)
                         ({0..<length l}-{rep_of l i,rep_of l j})
               + (szl ! rep_of l i + szl ! rep_of l j)" (is "?L + _ = ?R + _")
  proof -
    have "?L = sum (\<lambda>ia. szl[rep_of l i := szl ! rep_of l i + szl ! rep_of l j] ! ia)
                 (({0..<length l}-{rep_of l i})\<inter>{ia. ?upd ! ia = ia})"
      apply(subst sum.inter_restrict) by simp_all
    also have "\<dots> = sum (\<lambda>ia. szl[rep_of l i := szl ! rep_of l i + szl ! rep_of l j] ! ia)
                 (({0..<length l}-{rep_of l i,rep_of l j}) \<inter> {ia. l ! ia = ia})"
      unfolding ss by simp
    also have "\<dots> = ?R"
      apply(subst sum.inter_restrict) apply simp apply auto apply(rule sum.cong) apply simp using assms by auto  
    finally have "?L = ?R" .
    then show ?thesis by simp
  qed  
  also have "\<dots> = (\<Sum>i = 0..<length l. if l ! i = i then szl ! i else 0)"
    apply(subst (2) **) apply(subst sum_Un_nat) apply simp apply simp apply simp
    apply(subst ff) using assms apply (auto simp: rep_of_min) 
    using ufa_find_correct by blast
  also from i have "\<dots> = length l" unfolding invar_def by auto
  finally have A: "?A = length l" .
    
  have max_distrib: "\<And>a b :: nat. (2::nat) ^ max a b = max (2 ^ a) (2 ^ b)" 
    by (simp add: max_def)  
  { 
    assume a: "rep_of l i < length szl" "?upd ! rep_of l i = rep_of l i"  
    
    from i have g: "\<And>i. i<length l \<Longrightarrow> l ! i = i \<Longrightarrow> 2 ^ h_of l i \<le> szl ! i" unfolding invar_def by metis
    
    have "(2::nat) ^ (max (h_of l (rep_of l i)) (Suc (h_of l (rep_of l j))))
          \<le> max ( (szl ! (rep_of l i))) (2 * (szl ! (rep_of l j)))"
      apply(subst max_distrib) 
      apply(rule max.mono)
      subgoal apply(rule g) using assms a by (auto simp: rep_of_min)    
      subgoal apply(simp only: power.power_Suc) apply(rule mult_left_mono)
        apply(rule g) using assms a by (auto simp: rep_of_refl rep_of_min rep_of_bound)    
      done
    also have "\<dots> \<le> szl ! rep_of l i + szl ! rep_of l j"
      using size by auto
    finally
    have "2 ^ max (h_of l (rep_of l i)) (Suc (h_of l (rep_of l j))) \<le> szl ! rep_of l i + szl ! rep_of l j"
      .
  } note absch = this

  show ?thesis unfolding invar_def
    apply safe
    subgoal using i[unfolded invar_def] by simp
    subgoal apply simp using A by simp
    subgoal for e apply(cases "e=rep_of l i")
      subgoal apply simp
        apply(rule order.trans)
         apply(rule power_increasing[OF h_of_uf_union_touched])
                prefer 9
        subgoal using absch by simp
        using assms by (auto simp: rep_of_idem ufa_find_correct)   
      subgoal 
        apply simp apply(subst h_of_uf_union_untouched) 
               prefer 8 subgoal
          using i unfolding invar_def 
          by (metis nth_list_update')            
        using assms apply (auto simp: rep_of_idem )  
        by (metis nth_list_update')  
      done
    done
qed

 

lemma uf_union_rule': "\<lbrakk>i\<in>Domain R; j\<in> Domain R\<rbrakk> 
  \<Longrightarrow> <is_uf R u * $(11+ height_ub (card (Domain R))*2)> uf_union u i j <is_uf (per_union R i j)>\<^sub>t"
  unfolding uf_union_def
  apply (cases u)
  apply (simp add: is_uf_def[abs_def])
  apply(sep_auto heap: uf_rep_of_rule_ub)
    apply(simp add: ufa_\<alpha>_lenD)
  apply simp
  apply(sep_auto heap: uf_rep_of_rule_ub)
    apply(simp add: ufa_\<alpha>_lenD)
   apply simp
  apply (sep_auto
    simp: per_union_cmp ufa_\<alpha>_lenD ufa_find_correct
    rep_of_bound
    ufa_union_invar
    ufa_union_correct
  )
  subgoal apply(drule ufa_\<alpha>_lenD) apply(drule ufa_\<alpha>_lenD) using 12 by blast
  apply (sep_auto
    simp: per_union_cmp ufa_\<alpha>_lenD ufa_find_correct
    rep_of_bound
    ufa_union_invar
    ufa_union_correct
  )
  subgoal apply(drule ufa_\<alpha>_lenD) apply(drule ufa_\<alpha>_lenD) using 21 by blast  
  done


definition "uf_union_time n = 11+ height_ub n*2"

lemma uf_union_time_bound[asym_bound]: "uf_union_time \<in> \<Theta>(\<lambda>n. ln n)"
  unfolding uf_union_time_def by auto2

lemma uf_union_rule: "\<lbrakk>i\<in>Domain R; j\<in> Domain R\<rbrakk> 
  \<Longrightarrow> <is_uf R u * $(uf_union_time (card (Domain R)))> uf_union u i j <is_uf (per_union R i j)>\<^sub>t"
  unfolding uf_union_time_def using uf_union_rule' by auto


interpretation UnionFind_Impl is_uf uf_init uf_init_time uf_cmp uf_cmp_time uf_union uf_union_time
proof (unfold_locales, goal_cases)
case (1 t x' x)
  show ?case
    unfolding PR_CONST_def mop_per_init_def apply simp
    apply(rule extract_cost_otherway'[OF _ uf_init_rule, where Cost_lb="uf_init_time x"])
      apply (sep_auto simp: per_init'_def hn_ctxt_def pure_def)+
    using 1 by simp
next
  case (2 t R' R a' a b' b)
   show ?case 
    unfolding PR_CONST_def mop_per_compare_def apply simp
    apply(rule extract_cost_otherway'[OF _ uf_cmp_rule, where Cost_lb="(uf_cmp_time (card (Domain R')))"])
      apply (sep_auto simp: per_init'_def hn_ctxt_def pure_def)+
    using 2 by simp
next
  case (3  t R' R a' a b' b)
   show ?case 
    unfolding PR_CONST_def mop_per_union_def apply simp
    apply(rule extract_cost_otherway'[OF _ uf_union_rule, where Cost_lb="(uf_union_time (card (Domain R')))"])
        apply (sep_auto simp: per_init'_def hn_ctxt_def pure_def)+
    subgoal using 3 by simp
      apply (sep_auto simp: per_init'_def hn_ctxt_def pure_def)+
    subgoal using 3 by simp
      apply (sep_auto simp: per_init'_def hn_ctxt_def pure_def invalid_assn_def)+
    using 3 by simp
qed

end