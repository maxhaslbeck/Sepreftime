theory Refine_Foreach
imports Sepreftime RefineMonadicVCG
begin


text {*
  A common pattern for loop usage is iteration over the elements of a set.
  This theory provides the @{text "FOREACH"}-combinator, that iterates over 
  each element of a set.
*}

subsection {* Auxilliary Lemmas *}
text {* The following lemma is commonly used when reasoning about iterator
  invariants.
  It helps converting the set of elements that remain to be iterated over to
  the set of elements already iterated over. *}
lemma it_step_insert_iff: 
  "it \<subseteq> S \<Longrightarrow> x\<in>it \<Longrightarrow> S-(it-{x}) = insert x (S-it)" by auto

subsection {* Definition *}

text {*
  Foreach-loops come in different versions, depending on whether they have an 
  annotated invariant (I), a termination condition (C), and an order (O).

  Note that asserting that the set is finite is not necessary to guarantee
  termination. However, we currently provide only iteration over finite sets,
  as this also matches the ICF concept of iterators.
*}
   
definition "FOREACH_body f \<equiv> \<lambda>(xs, \<sigma>). do {
  let x = hd xs; \<sigma>'\<leftarrow>f x \<sigma>; RETURNT (tl xs,\<sigma>')
  }"

definition FOREACH_cond where "FOREACH_cond c \<equiv> (\<lambda>(xs,\<sigma>). xs\<noteq>[] \<and> c \<sigma>)"

text {* Foreach with continuation condition, order and annotated invariant: *}

definition FOREACHoci ("FOREACH\<^sub>O\<^sub>C\<^bsup>_,_\<^esup>") where "FOREACHoci R \<Phi> S c f \<sigma>0 inittime body_time \<equiv> do {
  ASSERT (finite S);
  xs \<leftarrow> SPECT (emb (\<lambda>xs. distinct xs \<and> S = set xs \<and> sorted_wrt R xs) inittime);
  (_,\<sigma>) \<leftarrow> whileIET 
    (\<lambda>(it,\<sigma>). \<exists>xs'. xs = xs' @ it \<and> \<Phi> (set it) \<sigma>) (\<lambda>(it,_). length it * body_time)  (FOREACH_cond c) (FOREACH_body f) (xs,\<sigma>0); 
  RETURNT \<sigma> }"

text {* Foreach with continuation condition and annotated invariant: *}
definition FOREACHci ("FOREACH\<^sub>C\<^bsup>_\<^esup>") where "FOREACHci \<equiv> FOREACHoci (\<lambda>_ _. True)"


subsection {* Proof Rules *}
thm vcg_rules
lemma FOREACHoci_rule:
  assumes IP: 
    "\<And>x it \<sigma>. \<lbrakk> c \<sigma>; x\<in>it; it\<subseteq>S; I it \<sigma>; \<forall>y\<in>it - {x}. R x y;
                \<forall>y\<in>S - it. R y x \<rbrakk> \<Longrightarrow> f x \<sigma> \<le> SPECT (emb (I (it-{x})) (enat body_time))"
  assumes FIN: "finite S"
  assumes I0: "I S \<sigma>0"
  assumes II1: "\<And>\<sigma>. \<lbrakk>I {} \<sigma>\<rbrakk> \<Longrightarrow> P \<sigma>"
  assumes II2: "\<And>it \<sigma>. \<lbrakk> it\<noteq>{}; it\<subseteq>S; I it \<sigma>; \<not>c \<sigma>;
                         \<forall>x\<in>it. \<forall>y\<in>S - it. R y x \<rbrakk> \<Longrightarrow> P \<sigma>"
  assumes time_ub: "inittime + enat ((card S) * body_time) \<le> enat overall_time" 
  assumes progress_f[progress_rules]: "\<And>a b. progress (f a b)"
  shows "FOREACHoci R I S c f \<sigma>0 inittime body_time \<le> SPECT (emb P (enat overall_time))"
  unfolding FOREACHoci_def
  apply(rule T_specifies_I) 
  apply(vcg'\<open>-\<close> rules: T_RESTemb whileIET_rule[THEN T_conseq4]  ) 
  
  unfolding FOREACH_body_def FOREACH_cond_def
      apply(vcg'\<open>-\<close> rules: )
  subgoal for a b xs'
      apply (rule IP[THEN T_specifies_rev,THEN T_conseq4])
          defer defer defer apply auto []
    subgoal  
      by (metis DiffE UnE list.sel(1) set_simps2 sorted_wrt.elims(2) sorted_wrt_append)  
    subgoal  
      by (simp add: Un_Diff sorted_wrt_append)  
    subgoal apply(vcg'\<open>-\<close> rules: ) 
          subgoal apply(rule exI[where x="xs' @ [hd a]"]) by simp   
          subgoal            by (metis remove1_tl set_remove1_eq) 
          subgoal 
            by (simp add: left_diff_distrib') 
          done

          apply simp_all
    done
  subgoal (* progress *) apply(auto split: prod.splits)
    apply(rule progress_rules) using progress_rules by simp
   using I0 apply simp
apply(vcg'\<open>-\<close> rules: ) 
  apply (auto simp: FIN mm3_Some_conv left_diff_distrib'[symmetric] split: option.splits if_splits)
  using II1 apply simp
  subgoal for a x xs' apply(cases "set a = {}") apply(rule II1) apply simp
        apply(rule II2) by (auto simp add: sorted_wrt_append) 
  subgoal using time_ub  by (auto simp: distinct_card)
proof (goal_cases)
  case (1 a b xs')
  have "length xs' \<le> length (xs' @ a)" by simp
  also have "\<dots> = card (set xs') + card (set a)"
    using 1 by (auto simp: distinct_card)
  also have "\<dots> = card S" using 1 by (simp add: card_Un_disjoint)
  finally have "length xs' \<le> card S" .
  then have "inittime + enat (length xs' * body_time) \<le> inittime + enat (card S * body_time)" by simp
  then show ?case using time_ub  
    using order_trans by blast  
qed 

(* ... *)


  
text \<open>We define a relation between distinct lists and sets.\<close>  
definition [to_relAPP]: "list_set_rel R \<equiv> \<langle>R\<rangle>list_rel O br set distinct"


(* ... *)



subsection {* Nres-Fold with Interruption (nfoldli) *}
text {*
  A foreach-loop can be conveniently expressed as an operation that converts
  the set to a list, followed by folding over the list.
  
  This representation is handy for automatic refinement, as the complex 
  foreach-operation is expressed by two relatively simple operations.
*}

text {* We first define a fold-function in the nrest-monad *}
fun nfoldli where
  "nfoldli l c f s = (case l of 
    [] \<Rightarrow> RETURNT s 
    | x#ls \<Rightarrow> if c s then do { s\<leftarrow>f x s; nfoldli ls c f s} else RETURNT s
  )"




end