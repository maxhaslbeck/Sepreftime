theory HNR                    
imports Sepreftime "../Imperative_HOL_Time/SepLogicTime/SepAuto"
begin       

term "execute c h = Some (r, h', n)"

lemma " (\<forall>\<sigma>. run c (Some h) \<sigma> r t \<longrightarrow> (\<sigma> = Some h')) = (\<forall>g. execute c h = g \<longrightarrow> g = Some (r, h', n) )"
  apply (rule)
  subgoal apply auto oops
    

definition "\<And>T. hn_refine \<Gamma> c \<Gamma>' R m \<equiv> nofailT m \<longrightarrow> 
    (\<forall>h as \<sigma> r n t M. pHeap h as n \<Turnstile> \<Gamma> \<longrightarrow> run c (Some h) \<sigma> r t \<longrightarrow> m = REST M \<longrightarrow>
    (\<sigma> \<noteq> None \<and> (\<exists>ra Ca. M ra = Some Ca \<and> pHeap (the \<sigma>) (new_addrs h as (the \<sigma>)) ((n+Ca)-t) \<Turnstile> \<Gamma>' * R ra r \<and> n+Ca\<ge>t)
       \<and> relH {a . a < lim h \<and> a \<notin> as} h (the \<sigma>) \<and> lim h \<le> lim (the \<sigma>)))"    
(*

  <\<Gamma> * $T> c <\<lambda>r. \<Gamma>' * (\<exists>\<^sub>Ax. R x r * \<up>(REST [x\<mapsto>T] \<le> m)) >\<^sub>t)" 
(* maybe T should be hidden/existentially quantified *)

*)
 
definition hn_ctxt :: "('a\<Rightarrow>'c\<Rightarrow>assn) \<Rightarrow> 'a \<Rightarrow> 'c \<Rightarrow> assn" 
  -- {* Tag for refinement assertion *}
  where
  "\<And>P. hn_ctxt P a c \<equiv> P a c"


lemma hnr_bind:
  assumes D1: "hn_refine \<Gamma> m' \<Gamma>1 Rh m"
  assumes D2: 
    "\<And>x x'. RETURNT x \<le> m \<Longrightarrow> hn_refine (\<Gamma>1 * hn_ctxt Rh x x') (f' x') (\<Gamma>2 x x') R (f x)"
  assumes IMP: "\<And>x x'. \<Gamma>2 x x' \<Longrightarrow>\<^sub>A \<Gamma>' * hn_ctxt Rx x x' * true"
  shows "hn_refine \<Gamma> (m'\<bind>f') \<Gamma>' R (m\<bind>f)"
    unfolding hn_refine_def apply clarify
proof (goal_cases)
  case (1 h as \<sigma> r n t M)
  from 1(1) have nfm: "nofailT m" and nff: "(\<forall>x t. inresT m x t \<longrightarrow> nofailT (f x))" by (auto simp: pw_bindT_nofailT)

  
  thm execute_bind effect_bindE
  from 1(3) have "run (m' \<bind> f') (Some h) \<sigma> r t" .
 

  from D1 have "G" unfolding hn_refine_def using nfm 1(2) apply auto

  then show ?case sorry
qed 



lemma extraction: "hn_refine \<Gamma> c \<Gamma>' (\<lambda>ra r. \<up>(ra = r)) (REST [length xs\<mapsto> enat (f (length xs))]) \<Longrightarrow>
           <\<Gamma> * $(f (length xs))> c <\<lambda>r. \<Gamma>' * \<up>(r = length xs) >\<^sub>t"
  unfolding hn_refine_def
  unfolding hoare_triple_def 
  apply clarify
proof (goal_cases)
  case (1 h as \<sigma> r n t)
  from 1(2) have 2: "pHeap h as (n-f (length xs)) \<Turnstile> \<Gamma>" and  nf: "n\<ge>f (length xs)"
    using mod_timeCredit_dest by auto

  from 1(1) have 3: "\<And>h as \<sigma> r n t M.
       pHeap h as n \<Turnstile> \<Gamma> \<Longrightarrow>
       run c (Some h) \<sigma> r t \<Longrightarrow>
      SPECT [length xs \<mapsto> enat (f (length xs))] = SPECT M \<Longrightarrow>
       \<sigma> \<noteq> None \<and>
       (\<exists>ra Ca. M ra = Some (enat Ca) \<and> pHeap (the \<sigma>) (new_addrs h as (the \<sigma>)) ((n + Ca) - t) \<Turnstile> \<Gamma>' * \<up> (ra = r) \<and> t \<le> n + Ca) \<and>
      relH {a. a < heap.lim h \<and> a \<notin> as} h (the \<sigma>) \<and> heap.lim h \<le> heap.lim (the \<sigma>)" 
      by auto
  
   have  A: "(\<exists>y. \<sigma> = Some y)"
  and B: "(\<exists>ra  Ca. [length xs \<mapsto> enat (f (length xs))] ra = Some (enat Ca) \<and>
     pHeap (the \<sigma>) (new_addrs h as (the \<sigma>)) (n - f (length xs) + Ca - t) \<Turnstile> \<Gamma>' * (\<lambda>ra r. \<up>(ra = r)) ra r \<and>
        t \<le> n - f (length xs) + Ca )" and C:
  "relH {a. a < heap.lim h \<and> a \<notin> as} h (the \<sigma>)" "heap.lim h \<le> heap.lim (the \<sigma>) " 
     using   3[OF 2 1(3)] apply blast
     using   3[OF 2 1(3)] apply blast
     using   3[OF 2 1(3)] apply blast
     using   3[OF 2 1(3)] apply blast done

   have p2: "\<And>ra Ca. ([length xs \<mapsto> enat (f (length xs))] ra = Some (enat Ca)) =
                (ra = length xs \<and> Ca = f (length xs))" by auto

  have p: "\<And>ra. [ra \<mapsto> enat t] \<le> [length xs \<mapsto> enat (f (length xs))] = ( (ra = length xs \<and>  t \<le>  (f (length xs))))"
    by (auto simp: le_fun_def)

  from B have "pHeap (the \<sigma>) (new_addrs h as (the \<sigma>)) (n -  t) \<Turnstile> \<Gamma>' * (\<lambda>ra r. \<up>(ra = r)) (length xs) r \<and>
        t \<le> n "
    unfolding p2 using nf by auto

  then have H: "pHeap (the \<sigma>) (new_addrs h as (the \<sigma>)) (n  - t) \<Turnstile> \<Gamma>' * (\<lambda>ra r. \<up>(ra = r)) (length xs) r" and
        T: "t \<le> n " by auto

  show ?case
    apply safe apply fact
    subgoal using H  
      by (smt assn_times_comm entailsD' entails_pure_post entails_triv entails_true mod_false')  
    subgoal by fact
    apply fact apply fact done
    
qed
  


end