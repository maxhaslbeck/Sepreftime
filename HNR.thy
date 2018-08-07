theory HNR                    
imports Sepreftime "../Imperative_HOL_Time/SepLogicTime/SepAuto"
begin       

term "execute c h = Some (r, h', n)"

lemma " (\<forall>\<sigma>. run c (Some h) \<sigma> r t \<longrightarrow> (\<sigma> = Some h')) = (\<forall>g. execute c h = g \<longrightarrow> g = Some (r, h', n) )"
  apply (rule)
  subgoal apply auto oops
    

definition "\<And>T. hn_refine \<Gamma> c \<Gamma>' R m \<equiv> nofailT m \<longrightarrow> 
    (\<forall>h as  n   M. pHeap h as n \<Turnstile> \<Gamma>  \<longrightarrow> m = REST M \<longrightarrow>
    (\<exists>h' t r. execute c h = Some (r, h', t) \<and>
       (\<exists>ra Ca. M ra \<ge> Some Ca \<and> pHeap h' (new_addrs h as h') ((n+Ca)-t) \<Turnstile> \<Gamma>' * R ra r \<and> n+Ca\<ge>t)
       \<and> relH {a . a < lim h \<and> a \<notin> as} h h' \<and> lim h \<le> lim h'))"    
(*

  <\<Gamma> * $T> c <\<lambda>r. \<Gamma>' * (\<exists>\<^sub>Ax. R x r * \<up>(REST [x\<mapsto>T] \<le> m)) >\<^sub>t)" 
(* maybe T should be hidden/existentially quantified *)

*)
 
definition hn_ctxt :: "('a\<Rightarrow>'c\<Rightarrow>assn) \<Rightarrow> 'a \<Rightarrow> 'c \<Rightarrow> assn" 
  -- {* Tag for refinement assertion *}
  where
  "\<And>P. hn_ctxt P a c \<equiv> P a c"


text "Transitivity"
lemma relH_trans[trans]: "\<lbrakk>relH as h1 h2; relH as h2 h3\<rbrakk> \<Longrightarrow> relH as h1 h3"
  unfolding relH_def
  by auto

lemma in_range_subset: 
  "\<lbrakk>as \<subseteq> as'; in_range (h,as')\<rbrakk> \<Longrightarrow> in_range (h,as)"
  by (auto simp: in_range.simps)


lemma relH_subset:
  assumes "relH bs h h'"
  assumes "as \<subseteq> bs"
  shows "relH as h h'"
  using assms unfolding relH_def by (auto intro: in_range_subset)




lemma hnr_bind:
  assumes D1: "hn_refine \<Gamma> m' \<Gamma>1 Rh m"
  assumes D2: 
    "\<And>x x'. RETURNT x \<le> m \<Longrightarrow> hn_refine (\<Gamma>1 * hn_ctxt Rh x x') (f' x') (\<Gamma>2 x x') R (f x)"
  assumes IMP: "\<And>x x'. \<Gamma>2 x x' \<Longrightarrow>\<^sub>A \<Gamma>' * hn_ctxt Rx x x' * true"
  shows "hn_refine \<Gamma> (m'\<bind>f') \<Gamma>' R (m\<bind>f)"
    unfolding hn_refine_def apply clarify
proof (goal_cases)
  case (1 h as n Mf)
  from 1(1) have nfm: "nofailT m" and nff: "\<And>x t. inresT m x t \<Longrightarrow> nofailT (f x)" by (auto simp: pw_bindT_nofailT)

  from nfm obtain M where M: "m = SPECT M" by fastforce 

  from D1 nfm 1(2) M 
    obtain r h' t ra Ca where execm: "execute m' h = Some (r, h', t)"
                and Mra: "M ra \<ge> Some (enat Ca)" and pH1: "pHeap h' (new_addrs h as h') (n + Ca - t) \<Turnstile> \<Gamma>1 * Rh ra r" and t: "t \<le> n + Ca"
                and relH1:  "relH {a. a < heap.lim h \<and> a \<notin> as} h h'" and hl1: "heap.lim h \<le> heap.lim h'"
      unfolding hn_refine_def by blast

    from M Mra have ram: "RETURNT ra \<le> m" apply (auto simp: le_fun_def RETURNT_def) 
      using dual_order.trans by fastforce
    have noff: "nofailT (f ra)" apply(rule nff[where t=0]) using Mra M unfolding inresT_def
      by (smt le_some_optE nrest.simps(5) zero_enat_def zero_le) 
    then obtain fM where fMra: "f ra = SPECT fM" by fastforce
  
    from D2[OF ram, of r] have "\<And>h as n M.
       pHeap h as n \<Turnstile> \<Gamma>1 * Rh ra r \<Longrightarrow>
       f ra = SPECT M \<Longrightarrow>
       \<exists>h' t rb. execute (f' r) h = Some (rb, h', t) \<and>
                 (\<exists>raa Ca. M raa \<ge> Some (enat Ca) \<and> pHeap h' (new_addrs h as h') (n + Ca - t) \<Turnstile> \<Gamma>2 ra r * R raa rb \<and> t \<le> n + Ca) \<and>
                 relH {a. a < heap.lim h \<and> a \<notin> as} h h' \<and> heap.lim h \<le> heap.lim h'"   unfolding hn_refine_def hn_ctxt_def by auto

    from this[OF pH1 fMra] obtain h'' t' r' ra' Ca' where execf: "execute (f' r) h' = Some (r', h'', t')" and
          fMra': " fM ra' \<ge> Some (enat Ca')"
           and M'':    " pHeap h'' (new_addrs h' (new_addrs h as h') h'') (n + Ca - t + Ca' - t') \<Turnstile> \<Gamma>2 ra r * R ra' r'"
           and t':" t' \<le> n + Ca - t + Ca'" 
     and relH2: "relH {a. a < heap.lim h' \<and> a \<notin> new_addrs h as h'} h' h''" and hl2: "heap.lim h' \<le> heap.lim h'' "
      by blast

    from Mra fMra' obtain Car Car' where PF: "M ra = Some Car" "fM ra' = Some Car'" by fastforce+


    thm execute_bind
    have t'': "n + Ca - t + Ca' - t' = n + (Ca + Ca') - (t + t')" using t t' by simp 
    have  
      "new_addrs h' (new_addrs h as h') h'' = new_addrs h as h''" 
      using hl1 hl2 
      by (auto simp add: new_addrs_def)
    with M'' have  
      ende: "pHeap h'' (new_addrs h as h'') (n + (Ca + Ca') - (t + t')) \<Turnstile>  \<Gamma>2 ra r * R ra' r'" 
      by (simp add: t'') 
    thm Sup_upper 
    have "Some (enat (Ca+Ca')) \<le> Some (Car+Car')" 
      using PF Mra fMra' add_mono by fastforce 
    also 
    from  1(3) fMra M have 
      "Some ((Car+Car')) \<le> Mf ra' "
      unfolding bindT_def  apply simp apply(drule nrest_Sup_SPECT_D[where x=ra'])
      apply simp apply(rule Sup_upper) apply auto
      apply(rule exI[where x="(map_option (op + (Car)) \<circ> fM)"]) 
       using PF  
       apply simp apply(rule exI[where x=ra]) apply(rule exI[where x="Car"]) by simp  
     finally have "Some (enat (Ca+Ca')) \<le> Mf ra' " .

    show ?case
      apply(rule exI[where x=h''])
      apply(rule exI[where x="t+t'"])
      apply(rule exI[where x="r'"])
    proof (safe)
      show "execute (m' \<bind> f') h = Some (r', h'', t + t')"
        by (simp add: execute_bind(1)[OF execm] execf) 
      show "\<exists>ra Ca. Mf ra \<ge> Some (enat Ca) \<and> pHeap h'' (new_addrs h as h'') (n + Ca - (t + t')) \<Turnstile> \<Gamma>' * R ra r' \<and> t + t' \<le> n + Ca"
        apply(rule exI[where x=ra'])
        apply(rule exI[where x="Ca+Ca'"])
      proof (safe)
        show "Mf ra' \<ge> Some (enat (Ca+Ca'))" apply fact done
 
        from ende IMP show "pHeap h'' (new_addrs h as h'') (n + (Ca + Ca') - (t + t')) \<Turnstile> \<Gamma>' * R ra' r'" sorry
        show "t + t' \<le> n + (Ca + Ca')" using t t' by simp
      qed 
      note relH1
      also have "relH {a. a < lim h \<and> a \<notin> as} h' h''"
        apply (rule relH_subset[OF relH2])
        using hl1 hl2
        by (auto simp: new_addrs_def) 
      finally show "relH {a. a < lim h \<and> a \<notin> as} h h''" . 
      show "heap.lim h \<le> heap.lim h'' "
        using hl1 hl2 by simp
    qed
  qed 


lemma extraction: "hn_refine \<Gamma> c \<Gamma>' (\<lambda>ra r. \<up>(ra = r)) (REST [length xs\<mapsto> enat (Costs)]) \<Longrightarrow>
           <\<Gamma> * $Costs> c <\<lambda>r. \<Gamma>' * \<up>(r = length xs) >\<^sub>t"
  unfolding hn_refine_def
  unfolding hoare_triple_def 
  apply clarify
proof (goal_cases)
  case (1 h as \<sigma> r n t)
  from 1(2) have 2: "pHeap h as (n-Costs) \<Turnstile> \<Gamma>" and  nf: "n\<ge>Costs"
    using mod_timeCredit_dest by auto

  from 1(1) have 3: "\<And>h as n M.
       pHeap h as n \<Turnstile> \<Gamma> \<Longrightarrow> 
      SPECT [length xs \<mapsto> enat (Costs)] = SPECT M \<Longrightarrow> (\<exists>h' t r. execute c h = Some (r, h', t) \<and>      
       (\<exists>ra Ca. M ra \<ge> Some (enat Ca) \<and> pHeap h' (new_addrs h as h') ((n + Ca) - t) \<Turnstile> \<Gamma>' * \<up> (ra = r) \<and> t \<le> n + Ca) \<and>
      relH {a. a < heap.lim h \<and> a \<notin> as} h h' \<and> heap.lim h \<le> heap.lim h')" 
      by auto

    thm effect_deterministic
  
    from 3[OF 2 ] obtain h' t' r' where E: "execute c h = Some (r', h', t') " and
          R:  "(\<exists>ra Ca. [length xs \<mapsto> enat (Costs)] ra \<ge> Some (enat Ca) \<and>
                    pHeap h' (new_addrs h as h') (n - Costs + Ca - t') \<Turnstile> \<Gamma>' * \<up> (ra = r') \<and> t' \<le> n - Costs + Ca) \<and>
           relH {a. a < heap.lim h \<and> a \<notin> as} h h' \<and> heap.lim h \<le> heap.lim h'" by blast

    have F: "\<sigma> = Some h'" and prime: "r' = r" "t' = t"  
      using E 1(3) run.cases apply force
      using E 1(3) run.cases apply force
      using E 1(3) run.cases by force 
    then have sig: "the \<sigma> = h'" by auto
    from R  have
    B: "(\<exists>ra  Ca. [length xs \<mapsto> enat (Costs)] ra \<ge> Some (enat Ca) \<and>
     pHeap (the \<sigma>) (new_addrs h as (the \<sigma>)) (n - Costs + Ca - t) \<Turnstile> \<Gamma>' * (\<lambda>ra r. \<up>(ra = r)) ra r \<and>
        t \<le> n - Costs + Ca )" and C:
  "relH {a. a < heap.lim h \<and> a \<notin> as} h (the \<sigma>)" "heap.lim h \<le> heap.lim (the \<sigma>) " 
      unfolding prime sig by auto
 

   have p2: "\<And>ra Ca. ([length xs \<mapsto> enat (Costs)] ra \<ge> Some (enat Ca)) =
                (ra = length xs \<and> Ca \<le> Costs)" by auto
 

  from B obtain Ca where i: "pHeap (the \<sigma>) (new_addrs h as (the \<sigma>)) (n - Costs + Ca - t) \<Turnstile> \<Gamma>' * (\<lambda>ra r. \<up>(ra = r)) (length xs) r"
      and ii:  "t \<le> n - Costs + Ca"  and ineq: "Ca \<le> Costs"
         
    using B unfolding p2 using nf by auto

  have pr: "(n - Costs + Ca - t) = (n - t) - (Costs - Ca)" using ineq ii nf by auto
  have pl: "(n - (t + (Costs - Ca)) + (Costs - Ca)) = n-t" using ineq ii nf by auto

  have "pHeap (the \<sigma>) (new_addrs h as (the \<sigma>) \<union> {}) ((n - t) - (Costs - Ca) + (Costs - Ca)) \<Turnstile> \<Gamma>' * (\<lambda>ra r. \<up>(ra = r)) (length xs) r * true"
    apply(rule mod_star_convI)  apply simp
    apply(rule i[unfolded pr])  by (simp add: top_assn_rule)
 
  then have H: "pHeap (the \<sigma>) (new_addrs h as (the \<sigma>)) (n - t) \<Turnstile> \<Gamma>' * \<up> (r = length xs) * true"
    apply (simp add: pl) by argo  
  
  from ii ineq nf have T: "t \<le> n " by auto

  show ?case
    apply safe
    subgoal using F by auto
    subgoal using H by simp  
    subgoal by fact
    apply fact apply fact done
    
qed
  


end