theory Refine_Foreach
imports Sepreftime
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

definition FOREACHoci ("FOREACH\<^sub>O\<^sub>C\<^bsup>_,_\<^esup>") where "FOREACHoci R \<Phi> S c f \<sigma>0 inittime \<equiv> do {
  ASSERT (finite S);
  xs \<leftarrow> SPECT (emb (\<lambda>xs. distinct xs \<and> S = set xs \<and> sorted_wrt R xs) inittime);
  (_,\<sigma>) \<leftarrow> whileT (*
    (\<lambda>(it,\<sigma>). \<exists>xs'. xs = xs' @ it \<and> \<Phi> (set it) \<sigma>) *) (FOREACH_cond c) (FOREACH_body f) (xs,\<sigma>0); 
  RETURNT \<sigma> }"

text {* Foreach with continuation condition and annotated invariant: *}
definition FOREACHci ("FOREACH\<^sub>C\<^bsup>_\<^esup>") where "FOREACHci \<equiv> FOREACHoci (\<lambda>_ _. True)"



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