theory Sepref_Additional
imports Sepref_Basic
begin


subsection "Rotate method"

definition gr where "gr A B = A * B"

lemma right_swap: "(A \<Longrightarrow>\<^sub>A B * (C * D)) \<Longrightarrow> (A \<Longrightarrow>\<^sub>A B * (D * C))"
  by (simp add: assn_times_comm)
lemma right_take: "(A \<Longrightarrow>\<^sub>A gr B C * D) \<Longrightarrow> (A \<Longrightarrow>\<^sub>A B * (C * D))"
  by (simp add: gr_def assn_times_assoc) 
lemma left_swap: "(B * (C * D) \<Longrightarrow>\<^sub>A A) \<Longrightarrow> (B * (D * C) \<Longrightarrow>\<^sub>A A)"
  by (simp add: assn_times_comm)
lemma left_take: "(gr B C * D \<Longrightarrow>\<^sub>A A) \<Longrightarrow> (B * (C * D) \<Longrightarrow>\<^sub>A A)"
  by (simp add: gr_def assn_times_assoc) 

lemma right_move_back: "(A \<Longrightarrow>\<^sub>A B * C) \<Longrightarrow> (A \<Longrightarrow>\<^sub>A C * B)"
  by (simp add: assn_times_comm)
lemma left_move_back: "(B * C \<Longrightarrow>\<^sub>A A) \<Longrightarrow> (C * B \<Longrightarrow>\<^sub>A A)"
  by (simp add: assn_times_comm)

thm mult.assoc
method rotater = ( (simp only: mult.assoc)? , rule right_move_back , (simp only: mult.assoc)?  )
method rotatel = ( (simp only: mult.assoc)? , rule left_move_back , (simp only: mult.assoc)?  )

method swapl = ( (simp only: mult.assoc)? ,rule left_swap, (simp only: mult.assoc)?   )
method takel = ( (simp only: mult.assoc)? , rule left_take, (simp only: mult.assoc)?  )

method swapr = ( (simp only: mult.assoc)? , rule right_swap , (simp only: mult.assoc)?  )
method taker = ( (simp only: mult.assoc)? , rule right_take, (simp only: mult.assoc)?  )


lemma match_first: "A \<Longrightarrow>\<^sub>A B \<Longrightarrow> \<Gamma> * A \<Longrightarrow>\<^sub>A \<Gamma> * B"  
  by (simp add: assn_times_comm entails_frame)  

lemma match_rest: "emp \<Longrightarrow>\<^sub>A B \<Longrightarrow> \<Gamma> \<Longrightarrow>\<^sub>A \<Gamma> * B"  
  using match_first by fastforce 

lemma run_and_execute: "(\<forall>\<sigma> t r. run c (Some h) \<sigma> r t \<longrightarrow> \<sigma> \<noteq> None \<and> P (the \<sigma>) r t)
        \<longleftrightarrow> (\<exists>h' t r. execute c h = Some (r, h', t) \<and> P h' r t)"  
  apply rule
  subgoal by (metis option.sel run.intros(2) run.intros(3) timeFrame.elims) 
  subgoal by (metis (mono_tags) not_None_eq option.sel prod.sel(1) prod.sel(2) run_to_execute) 
  done

lemma hoare_alt: 
  "<P> c <\<lambda>r. Q r > = (\<forall>h as n.
        pHeap h as n \<Turnstile> P \<longrightarrow> (\<exists>h' t r. execute c h = Some (r, h', t) \<and>
        (pHeap h' (new_addrs h as h') (n - t) \<Turnstile> Q r \<and>
        t \<le> n \<and> relH {a. a < heap.lim h \<and> a \<notin> as} h h' \<and> heap.lim h \<le> heap.lim h')))" (is "?L = (\<forall>h as n. ?H h as n \<longrightarrow> (\<exists>h' t r. _ \<and> ?P h as h' n t r))")
proof -
  have "?L = (\<forall>h as n. pHeap h as n \<Turnstile> P \<longrightarrow> 
                  (\<forall> \<sigma> t r. run c (Some h) \<sigma> r t \<longrightarrow> \<sigma> \<noteq> None \<and> (?P h as (the \<sigma>) n t r)))"
    unfolding hoare_triple_def by auto  
  also have "\<dots> =  (\<forall>h as n. pHeap h as n \<Turnstile> P \<longrightarrow>
              (\<exists>h' t r. execute c h = Some (r, h', t) \<and>
                         ?P h as h' n t r))" apply(subst run_and_execute) by simp
  finally show ?thesis .
qed

lemma extract_cost_otherway:
  assumes 
    "\<Gamma> * timeCredit_assn Cost_lb \<Longrightarrow>\<^sub>A G * F"
    "<G> c <\<lambda>r. Q r >"
    "\<And>r. Q r * F \<Longrightarrow>\<^sub>A \<Gamma>' * (\<exists>\<^sub>Ara. R ra r * \<up>(ra \<in> dom M)) * true"
    "(\<And>c. c\<in>ran M \<Longrightarrow> Cost_lb \<le> c)"
  shows "hn_refine \<Gamma> c \<Gamma>' R (REST M)" 
proof - 
  note pre_rule[OF assms(1) frame_rule[OF assms(2)]]
  then have TR: "\<And>h as n. pHeap h as n \<Turnstile> \<Gamma> * timeCredit_assn Cost_lb \<Longrightarrow>
           (\<exists>h' t r. execute c h = Some (r, h', t) \<and>
                     pHeap h' (new_addrs h as h') (n - t) \<Turnstile> Q r * F \<and> t \<le> n \<and> relH {a. a < heap.lim h \<and> a \<notin> as} h h' \<and> heap.lim h \<le> heap.lim h')" 
    unfolding hoare_alt by simp

  show ?thesis
    unfolding hn_refine_def apply auto
  proof -
    fix h as n
    assume "pHeap h as n \<Turnstile> \<Gamma>"
    then have "pHeap h as (n+Cost_lb) \<Turnstile> \<Gamma> * timeCredit_assn Cost_lb"  
      by (simp add: mod_timeCredit_dest)
    from TR[OF this] obtain h' t r where "execute c h = Some (r, h', t)"
           and h: "pHeap h' (new_addrs h as h') (n + Cost_lb - t) \<Turnstile> Q r * F" 
           and 3: "t \<le> n + Cost_lb" "relH {a. a < heap.lim h \<and> a \<notin> as} h h'" "heap.lim h \<le> heap.lim h'"
      by blast

    from h assms(3) have h': "pHeap h' (new_addrs h as h') (n + Cost_lb - t) \<Turnstile>   \<Gamma>' * (\<exists>\<^sub>Ara. R ra r * \<up> (ra \<in> dom M)) * true"
      by (simp add: entails_def)
    then have "\<exists>ra. pHeap h' (new_addrs h as h') (n + Cost_lb - t) \<Turnstile>   \<Gamma>' *  R ra r * \<up> (ra \<in> dom M) * true"
      by(simp add: ex_distrib_star' ex_distrib_star[symmetric] mod_ex_dist assn_times_assoc)
    then obtain ra where h'': "pHeap h' (new_addrs h as h') (n + Cost_lb - t) \<Turnstile>   \<Gamma>' *  R ra r * \<up> (ra \<in> dom M) * true"
        by blast
    have "pHeap h' (new_addrs h as h') (n + Cost_lb - t) \<Turnstile>   (\<Gamma>' *  R ra r * true) * \<up> (ra \<in> dom M)"
      apply(rule entailsD[OF _ h''])  by (simp add: entails_triv move_back_pure') 
    then have h'': "pHeap h' (new_addrs h as h') (n + Cost_lb - t) \<Turnstile>   \<Gamma>' *  R ra r * true" and radom: "ra \<in> dom M"
      using mod_pure_star_dist  by auto   

    show "\<exists>h' t r. execute c h = Some (r, h', t) \<and>
                       (\<exists>ra Ca. Some (enat Ca) \<le> M ra \<and> t \<le> n + Ca \<and> pHeap h' (new_addrs h as h') (n + Ca - t) \<Turnstile> \<Gamma>' * R ra r * true) \<and>
                       relH {a. a < heap.lim h \<and> a \<notin> as} h h' \<and> heap.lim h \<le> heap.lim h'"
      apply(rule exI[where x=h']) apply(rule exI[where x=t]) apply(rule exI[where x=r])
      apply safe apply fact
          apply(rule exI[where x=ra])
        apply(rule exI[where x=Cost_lb])
        apply safe 
      subgoal using assms(4) radom using ranI by force
      subgoal by fact
      subgoal using h'' mod_star_trueI by blast 
       apply fact apply fact done
  qed
qed



subsection "how to extract a hoare triple from hn_refine"

lemma extract_cost_ub:
  assumes "hn_refine \<Gamma> c \<Gamma>' R (REST M)" "(\<And>c. c\<in>ran M \<Longrightarrow> c \<le> Cost_ub)"
  shows "<\<Gamma> * timeCredit_assn Cost_ub> c <\<lambda>r. \<Gamma>' * (\<exists>\<^sub>Ara. R ra r * \<up>(ra \<in> dom M)) >\<^sub>t"
  using assms(1)  unfolding hn_refine_def
  unfolding hoare_triple_def 
  apply clarify
proof (goal_cases)
  case (1 h as \<sigma> r n t)
  from 1(2) have 2: "pHeap h as (n-Cost_ub) \<Turnstile> \<Gamma>" and  nf: "n\<ge>Cost_ub"
    using mod_timeCredit_dest by auto

  from 1(1) have 3: "\<And>h as n Ma.
       pHeap h as n \<Turnstile> \<Gamma> \<Longrightarrow> 
      SPECT M = SPECT Ma \<Longrightarrow> (\<exists>h' t r. execute c h = Some (r, h', t) \<and>      
       (\<exists>ra Ca. Ma ra \<ge> Some (enat Ca) \<and> t \<le> n + Ca \<and> pHeap h' (new_addrs h as h') ((n + Ca) - t) \<Turnstile> \<Gamma>' * R ra r * true) \<and>
      relH {a. a < heap.lim h \<and> a \<notin> as} h h' \<and> heap.lim h \<le> heap.lim h')" 
    by auto

  thm effect_deterministic

  from 3[OF 2 ] obtain h' t' r' where E: "execute c h = Some (r', h', t') " and
    R:  "(\<exists>ra Ca. M ra \<ge> Some (enat Ca) \<and>
                    pHeap h' (new_addrs h as h') (n - Cost_ub + Ca - t') \<Turnstile> \<Gamma>' * R ra r' * true \<and> t' \<le> n - Cost_ub + Ca) \<and>
           relH {a. a < heap.lim h \<and> a \<notin> as} h h' \<and> heap.lim h \<le> heap.lim h'" by blast

  have F: "\<sigma> = Some h'" and prime: "r' = r" "t' = t"  
    using E 1(3) run.cases apply force
    using E 1(3) run.cases apply force
    using E 1(3) run.cases by force 
  then have sig: "the \<sigma> = h'" by auto
  from R  have
    B: "(\<exists>ra Ca. M ra \<ge> Some (enat Ca) \<and>
     pHeap (the \<sigma>) (new_addrs h as (the \<sigma>)) (n - Cost_ub + Ca - t) \<Turnstile> \<Gamma>' * R ra r * true \<and>
        t \<le> n - Cost_ub + Ca )" and C:
    "relH {a. a < heap.lim h \<and> a \<notin> as} h (the \<sigma>)" "heap.lim h \<le> heap.lim (the \<sigma>) " 
    unfolding prime sig by auto



  from B obtain ra Ca where i: "pHeap (the \<sigma>) (new_addrs h as (the \<sigma>)) (n - Cost_ub + Ca - t) \<Turnstile> \<Gamma>' * R ra r * true"
    and ii:  "t \<le> n - Cost_ub + Ca"  and ineq: "M ra \<ge> Some (enat Ca)"
    using B by auto

  from ineq have radom: "ra \<in> dom M" using domIff by fastforce  
  then obtain Mra where Mra: "M ra = Some Mra" by blast
  with assms(2) have "Mra \<le> enat Cost_ub" by (meson ranI)
  with Mra ineq have "Some (enat Ca) \<le> Some (enat Cost_ub)" 
    using dual_order.trans by fastforce 
  then have ie: "Ca \<le> Cost_ub" by auto

  have pr: "(n - Cost_ub + Ca - t) = (n - t) - (Cost_ub - Ca)" using ie ii nf by auto
  have pl: "(n - (t + (Cost_ub - Ca)) + (Cost_ub - Ca)) = n-t" using ii nf by auto

  have "pHeap (the \<sigma>) (new_addrs h as (the \<sigma>) \<union> {}) ((n - t) - (Cost_ub - Ca) + (Cost_ub - Ca)) \<Turnstile> \<Gamma>' * R ra r * true * true"
    apply(rule mod_star_convI)  apply simp
     apply(rule i[unfolded pr])  by (simp add: top_assn_rule)

  then have H: "pHeap (the \<sigma>) (new_addrs h as (the \<sigma>)) (n - t) \<Turnstile> \<Gamma>' * R ra r * true * true"
    by (simp add: pl)   

  have "pHeap (the \<sigma>) (new_addrs h as (the \<sigma>)) (n - t) \<Turnstile> \<Gamma>' * R ra r * \<up> (ra \<in> dom M) * true"
    apply(rule entailsD[OF _ H]) using radom by auto2  
  then have "\<exists>ra. pHeap (the \<sigma>) (new_addrs h as (the \<sigma>)) (n - t) \<Turnstile> \<Gamma>' * R ra r * \<up> (ra \<in> dom M) * true"
    by blast
  then have H': "pHeap (the \<sigma>) (new_addrs h as (the \<sigma>)) (n - t) \<Turnstile> (\<exists>\<^sub>Ara. \<Gamma>' *  R ra r * \<up> (ra \<in> dom M) * true)"
    using mod_ex_dist by blast
  have H: "pHeap (the \<sigma>) (new_addrs h as (the \<sigma>)) (n - t) \<Turnstile> \<Gamma>' * (\<exists>\<^sub>Ara. R ra r * \<up> (ra \<in> dom M)) * true" 
    apply(rule entailsD[OF _ H']) by auto2

  from ii ie nf have T: "t \<le> n " by auto

  show ?case
    apply safe
    subgoal using F by auto
    subgoal using H by simp  
    subgoal by fact
     apply fact apply fact done
qed



end