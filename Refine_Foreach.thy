theory Refine_Foreach
imports Sepreftime RefineMonadicVCG SepLogic_Misc
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
  x \<leftarrow> RETURNT( hd xs); \<sigma>'\<leftarrow>f x \<sigma>; RETURNT (tl xs,\<sigma>')
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
  unfolding FOREACH_body_def FOREACH_cond_def  
  apply(vcg'\<open>-\<close> rules:  IP[THEN T_specifies_rev,THEN T_conseq4]  )  

  prefer 5 apply auto []
  subgoal using I0 by blast  
  subgoal by blast  
  subgoal by simp  
  subgoal by auto  
  subgoal by (metis distinct_append hd_Cons_tl remove1_tl set_remove1_eq sorted_wrt.simps(2) sorted_wrt_append)  
  subgoal by (metis DiffD1 DiffD2 UnE list.set_sel(1) set_append sorted_wrt_append)  
  subgoal apply (auto simp: Some_le_mm3_Some_conv Some_le_emb'_conv Some_eq_emb'_conv)
      subgoal by (metis append.assoc append.simps(2) append_Nil hd_Cons_tl)
      subgoal by (metis remove1_tl set_remove1_eq) 
      subgoal by (simp add: diff_mult_distrib)
      done
  subgoal using time_ub II1 apply (auto simp: Some_le_mm3_Some_conv Some_le_emb'_conv Some_eq_emb'_conv
               ) 
    subgoal by (simp add: distinct_card) 
    subgoal by (metis DiffD1 DiffD2 II2 Un_iff Un_upper2 sorted_wrt_append) 
    subgoal by (metis DiffD1 DiffD2 II2 Un_iff sorted_wrt_append sup_ge2) 
    subgoal by (metis add_mono diff_le_self distinct_append distinct_card dual_order.trans enat_ord_simps(1) length_append order_mono_setup.refl set_append)  
    done
  subgoal by (fact FIN)
  done


lemma FOREACHci_rule :
  assumes IP: 
    "\<And>x it \<sigma>. \<lbrakk> x\<in>it; it\<subseteq>S; I it \<sigma>; c \<sigma> \<rbrakk> \<Longrightarrow> f x \<sigma> \<le> SPECT (emb (I (it-{x})) (enat body_time))"
  assumes II1: "\<And>\<sigma>. \<lbrakk>I {} \<sigma>\<rbrakk> \<Longrightarrow> P \<sigma>"
  assumes II2: "\<And>it \<sigma>. \<lbrakk> it\<noteq>{}; it\<subseteq>S; I it \<sigma>; \<not>c \<sigma> \<rbrakk> \<Longrightarrow> P \<sigma>"
  assumes FIN: "finite S"
  assumes I0: "I S \<sigma>0"
  assumes progress_f: "\<And>a b. progress (f a b)"
  assumes "inittime + enat (card S * body_time) \<le> enat overall_time"
  shows "FOREACHci I S c f \<sigma>0 inittime body_time  \<le> SPECT (emb P (enat overall_time))"
  unfolding FOREACHci_def
  by (rule FOREACHoci_rule) (simp_all add: assms)


(* ... *)


  
text \<open>We define a relation between distinct lists and sets.\<close>  
definition [to_relAPP]: "list_set_rel R \<equiv> \<langle>R\<rangle>list_rel O br set distinct"


(*lemma list_set_rel_finite: "(succl, succ) \<in> \<langle>Id\<rangle>list_set_rel \<Longrightarrow> finite succ"
  sorry *)

(* ... *)



subsection {* Nres-Fold with Interruption (nfoldli) *}
text {*
  A foreach-loop can be conveniently expressed as an operation that converts
  the set to a list, followed by folding over the list.
  
  This representation is handy for automatic refinement, as the complex 
  foreach-operation is expressed by two relatively simple operations.
*}

text {* We first define a fold-function in the nrest-monad *}
definition nfoldli where
  "nfoldli l c f s = RECT (\<lambda>D (l,s). (case l of 
    [] \<Rightarrow> RETURNT s 
    | x#ls \<Rightarrow> if c s then do { s\<leftarrow>f x s; D (ls, s)} else RETURNT s
  )) (l, s)"


lemma nfoldli_simps[simp]:
  "nfoldli [] c f s = RETURNT s"
  "nfoldli (x#ls) c f s = 
    (if c s then do { s\<leftarrow>f x s; nfoldli ls c f s} else RETURNT s)"
  unfolding nfoldli_def by (subst RECT_unfold, refine_mono, auto split: nat.split)+

lemma param_nfoldli[param]:
  shows "(nfoldli,nfoldli) \<in> 
    \<langle>Ra\<rangle>list_rel \<rightarrow> (Rb\<rightarrow>Id) \<rightarrow> (Ra\<rightarrow>Rb\<rightarrow>\<langle>Rb\<rangle>nrest_rel) \<rightarrow> Rb \<rightarrow> \<langle>Rb\<rangle>nrest_rel"
  apply (intro fun_relI)
proof goal_cases
  case (1 l l' c c' f f' s s')
  thus ?case
    apply (induct arbitrary: s s')
    apply (simp only: nfoldli_simps True_implies_equals)
    apply parametricity
    apply (simp only: nfoldli_simps True_implies_equals)
    apply (parametricity)
    done
qed

lemma nfoldli_no_ctd[simp]: "\<not>ctd s \<Longrightarrow> nfoldli l ctd f s = RETURNT s"
  by (cases l) auto

lemma nfoldli_append: "nfoldli (l1@l2) ctd f s = nfoldli l1 ctd f s \<bind> nfoldli l2 ctd f"
  by (induction l1 arbitrary: s) simp_all

lemma nfoldli_assert:
  assumes "set l \<subseteq> S"
  shows "nfoldli l c (\<lambda> x s. ASSERT (x \<in> S) \<then> f x s) s = nfoldli l c f s"
  using assms by (induction l arbitrary: s) (auto simp: pw_eq_iff refine_pw_simps)

lemmas nfoldli_assert' = nfoldli_assert[OF order.refl]

definition nfoldliIE :: "('d list \<Rightarrow> 'd list \<Rightarrow> 'a \<Rightarrow>  bool) \<Rightarrow> nat \<Rightarrow> 'd list \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('d \<Rightarrow> 'a \<Rightarrow> 'a nrest) \<Rightarrow> 'a \<Rightarrow> 'a nrest" where
  "nfoldliIE I E l c f s = nfoldli l c f s"
 


lemma nfoldliIE_rule':
  assumes IS: "\<And>x l1 l2 \<sigma>. \<lbrakk> l0=l1@x#l2; I l1 (x#l2) \<sigma>; c \<sigma> \<rbrakk> \<Longrightarrow> f x \<sigma> \<le> SPECT (emb (I (l1@[x]) l2) (enat body_time))"
  assumes FNC: "\<And>l1 l2 \<sigma>. \<lbrakk> l0=l1@l2; I l1 l2 \<sigma>; \<not>c \<sigma> \<rbrakk> \<Longrightarrow> P \<sigma>"  
  assumes FC: "\<And>\<sigma>. \<lbrakk> I l0 [] \<sigma> \<rbrakk> \<Longrightarrow> P \<sigma>"  
  shows "lr@l = l0 \<Longrightarrow> I lr l \<sigma> \<Longrightarrow> nfoldliIE I body_time l c f \<sigma> \<le> SPECT (emb P (body_time * length l))"
proof (induct l arbitrary: lr \<sigma>)
  case Nil
  then show ?case by (auto simp: nfoldliIE_def RETURNT_def le_fun_def  Some_le_emb'_conv dest!: FC)
next
  case (Cons a l)
  show ?case
    apply (auto simp add: nfoldliIE_def)
    subgoal 
      apply(rule T_specifies_I)
      apply (vcg'\<open>-\<close> rules: IS[THEN T_specifies_rev  , THEN T_conseq4] 
                            Cons(1)[unfolded nfoldliIE_def, THEN T_specifies_rev  , THEN T_conseq4])
      unfolding Some_eq_emb'_conv Some_le_emb'_conv
      using Cons(2,3) by auto
    subgoal 
      apply(simp add: RETURNT_def le_fun_def Some_le_emb'_conv)
      apply(rule FNC) using Cons(2,3) by auto
    done      
qed

lemma nfoldliIE_rule:
  assumes I0: "I [] l0 \<sigma>0"
  assumes IS: "\<And>x l1 l2 \<sigma>. \<lbrakk> l0=l1@x#l2; I l1 (x#l2) \<sigma>; c \<sigma> \<rbrakk> \<Longrightarrow> f x \<sigma> \<le> SPECT (emb (I (l1@[x]) l2) (enat body_time))"
  assumes FNC: "\<And>l1 l2 \<sigma>. \<lbrakk> l0=l1@l2; I l1 l2 \<sigma>; \<not>c \<sigma> \<rbrakk> \<Longrightarrow> P \<sigma>"  
  assumes FC: "\<And>\<sigma>. \<lbrakk> I l0 [] \<sigma> \<rbrakk> \<Longrightarrow> P \<sigma>"  
  assumes T: "(body_time * length l0) \<le> t"
  shows "nfoldliIE I body_time l0 c f \<sigma>0 \<le> SPECT (emb P t)"
proof -
  have "nfoldliIE I body_time l0 c f \<sigma>0 \<le> SPECT (emb P (body_time * length l0))" 
     apply(rule nfoldliIE_rule'[where lr="[]"]) using assms by auto
  also have "\<dots> \<le> SPECT (emb P t)"
    apply(rule SPECT_ub) using T by (auto simp: le_fun_def)
  finally show ?thesis .
qed


lemma nfoldli_refine[refine]:
  assumes "(li, l) \<in> \<langle>S\<rangle>list_rel"
    and "(si, s) \<in> R"
    and CR: "(ci, c) \<in> R \<rightarrow> bool_rel"
    and [refine]: "\<And>xi x si s. \<lbrakk> (xi,x)\<in>S; (si,s)\<in>R; c s \<rbrakk> \<Longrightarrow> fi xi si \<le> \<Down>R (f x s)"
  shows "nfoldli li ci fi si \<le> \<Down> R (nfoldli l c f s)"
  using assms(1,2)
proof (induction arbitrary: si s rule: list_rel_induct)
  case Nil thus ?case by (simp add: RETURNT_refine)
next
  case (Cons xi x li l) 
  note [refine] = Cons

  show ?case
    apply (simp add: RETURNT_refine  split del: if_split)
    apply refine_rcg
    using CR Cons.prems by (auto simp: RETURNT_refine  dest: fun_relD)
qed    


thm nfoldliIE_rule[THEN T_specifies_rev, THEN T_conseq4,no_vars]


definition "nfoldliIE' I bt l0 f s0 = nfoldliIE I bt l0 (\<lambda>_. True) f s0"

lemma nfoldliIE'_rule:
  assumes 
"\<And>x l1 l2 \<sigma>.
    l0 = l1 @ x # l2 \<Longrightarrow>
    I l1 (x # l2) \<sigma> \<Longrightarrow> Some 0 \<le> lst (f x \<sigma>) (emb (I (l1 @ [x]) l2) (enat body_time))"
"I [] l0 \<sigma>0"
"(\<And>\<sigma>. I l0 [] \<sigma> \<Longrightarrow> Some (t + enat (body_time * length l0)) \<le> Q \<sigma>)"
shows "Some t \<le> lst (nfoldliIE' I body_time l0 f \<sigma>0) Q"
  unfolding nfoldliIE'_def
  apply(rule nfoldliIE_rule[where P="I l0 []" and c="\<lambda>_. True" and t="body_time * length l0", THEN T_specifies_rev, THEN T_conseq4])
       apply fact
  subgoal 
    apply(rule T_specifies_I) using  assms(1) by auto 
  subgoal by auto
    apply simp
   apply simp
  subgoal  
    unfolding Some_eq_emb'_conv 
    using assms(3) by auto
  done




text {* We relate our fold-function to the while-loop that we used in
  the original definition of the foreach-loop *}
lemma nfoldli_while: "nfoldli l c f \<sigma>
          \<le>
         (whileIET I E 
           (FOREACH_cond c) (FOREACH_body f) (l, \<sigma>) \<bind>
          (\<lambda>(_, \<sigma>). RETURNT \<sigma>))"
proof (induct l arbitrary: \<sigma>)
  case Nil thus ?case 
    unfolding whileIET_def 
     apply (subst whileT_unfold) by (auto simp: FOREACH_cond_def)
next
  case (Cons x ls)
  show ?case 
  proof (cases "c \<sigma>")
    case False thus ?thesis
    unfolding whileIET_def 
     apply (subst whileT_unfold)
      unfolding FOREACH_cond_def
      by simp
  next
    case [simp]: True
    from Cons show ?thesis
    unfolding whileIET_def 
     apply (subst whileT_unfold)
      unfolding FOREACH_cond_def FOREACH_body_def
      apply clarsimp
      apply (rule  bindT_mono)
      apply simp_all
      done
  qed    
qed

lemma rr: "l0 = l1 @ a \<Longrightarrow> a \<noteq> [] \<Longrightarrow> l0 = l1 @ hd a # tl a" by auto 

lemma nfoldli_rule:
  assumes I0: "I [] l0 \<sigma>0"
  assumes IS: "\<And>x l1 l2 \<sigma>. \<lbrakk> l0=l1@x#l2; I l1 (x#l2) \<sigma>; c \<sigma> \<rbrakk> \<Longrightarrow> f x \<sigma> \<le> SPECT (emb (I (l1@[x]) l2) (enat body_time))"
  assumes FNC: "\<And>l1 l2 \<sigma>. \<lbrakk> l0=l1@l2; I l1 l2 \<sigma>; \<not>c \<sigma> \<rbrakk> \<Longrightarrow> P \<sigma>"
  assumes FC: "\<And>\<sigma>. \<lbrakk> I l0 [] \<sigma>; c \<sigma> \<rbrakk> \<Longrightarrow> P \<sigma>"
  assumes progressf: "\<And>x y. progress (f x y)"
  shows "nfoldli l0 c f \<sigma>0 \<le> SPECT (emb P (body_time * length l0))"
  apply (rule order_trans[OF nfoldli_while[
          where I="\<lambda>(l2,\<sigma>). \<exists>l1. l0=l1@l2 \<and> I l1 l2 \<sigma>" and E="\<lambda>(l2,\<sigma>). (length l2) * body_time"]])  
  unfolding FOREACH_cond_def FOREACH_body_def 
  apply(rule T_specifies_I) 
  apply(vcg'_step \<open>clarsimp\<close>)
  subgoal  using I0 by auto
  subgoal 
    apply(vcg'_step \<open>clarsimp\<close>) 
    apply (elim exE conjE)
    subgoal for a b l1      
      apply(vcg'_step \<open>clarsimp\<close> rules: IS[THEN T_specifies_rev , THEN T_conseq4 ])
         apply(rule rr) apply simp_all    
      apply(auto simp add: Some_le_mm3_Some_conv emb_eq_Some_conv left_diff_distrib')
      apply(rule exI[where x="l1@[hd a]"]) by simp        
    done
  subgoal (* progress *)
    supply progressf [progress_rules] by (progress \<open>clarsimp\<close>)  
  subgoal 
    apply(vcg' \<open>clarsimp\<close>) 
    subgoal for a \<sigma>
      apply(cases "c \<sigma>")       
      using FC  FNC  by(auto simp add: Some_le_emb'_conv  mult.commute)         
    done
  done



definition "LIST_FOREACH' tsl c f \<sigma> \<equiv> do {xs \<leftarrow> tsl; nfoldli xs c f \<sigma>}"

text {* This constant is a placeholder to be converted to
  custom operations by pattern rules *} 
definition "it_to_sorted_list R s to_sorted_list_time
  \<equiv> SPECT (emb (\<lambda>l. distinct l \<and> s = set l \<and> sorted_wrt R l) to_sorted_list_time)"

definition "LIST_FOREACH \<Phi> tsl c f \<sigma>0 bodytime \<equiv> do {
  xs \<leftarrow> tsl;
  (_,\<sigma>) \<leftarrow> whileIET (\<lambda>(it, \<sigma>). \<exists>xs'. xs = xs' @ it \<and> \<Phi> (set it) \<sigma>) (\<lambda>(it, \<sigma>). length it * bodytime)
    (FOREACH_cond c) (FOREACH_body f) (xs, \<sigma>0);
    RETURNT \<sigma>}"

lemma FOREACHoci_by_LIST_FOREACH:
  "FOREACHoci R \<Phi> S c f \<sigma>0 to_sorted_list_time bodytime = do {
    ASSERT (finite S);
    LIST_FOREACH \<Phi> (it_to_sorted_list R S to_sorted_list_time) c f \<sigma>0 bodytime
  }"
  unfolding OP_def FOREACHoci_def LIST_FOREACH_def it_to_sorted_list_def 
  by simp
(*
 
lemma LFO_pre_refine: (* TODO: Generalize! *)
  assumes "(li,l)\<in>\<langle>A\<rangle>list_set_rel"
  assumes "(ci,c)\<in>R \<rightarrow> bool_rel"
  assumes "(fi,f)\<in>A\<rightarrow>R\<rightarrow>\<langle>R\<rangle>nrest_rel"
  assumes "(s0i,s0)\<in>R"
  shows "LIST_FOREACH' (RETURNT li) ci fi s0i \<le> \<Down>R (FOREACHci I l c f s0 0 body_time)"
proof -
  from assms(1) have [simp]: "finite l" by (auto simp: list_set_rel_def br_def)
  show ?thesis
    unfolding   FOREACHci_def unfolding FOREACHoci_by_LIST_FOREACH 
    apply simp
    apply (rule LIST_FOREACH_autoref[param_fo, THEN nres_relD])
    using assms
    apply auto
    apply (auto simp: it_to_sorted_list_def nres_rel_def pw_le_iff refine_pw_simps
      list_set_rel_def br_def)
    done
qed    
    *)

(*
lemma LFOci_refine: (* TODO: Generalize! *)
  assumes "(li,l)\<in>\<langle>A\<rangle>list_set_rel"
  assumes "\<And>s si. (si,s)\<in>R \<Longrightarrow> ci si \<longleftrightarrow> c s"
  assumes "\<And>x xi s si. \<lbrakk>(xi,x)\<in>A; (si,s)\<in>R\<rbrakk> \<Longrightarrow> fi xi si \<le> \<Down>R (f x s)"
  assumes "(s0i,s0)\<in>R"
  shows "nfoldli li ci fi s0i \<le> \<Down>R (FOREACHci I l c f s0 init_time body_time)"
(*
proof -
  from assms LFO_pre_refine[of li l A ci c R fi f s0i s0] show ?thesis
    unfolding fun_rel_def nres_rel_def LIST_FOREACH'_def
    apply (simp add: pw_le_iff refine_pw_simps)
    apply blast+
    done
qed    
*)sorry
*)



end