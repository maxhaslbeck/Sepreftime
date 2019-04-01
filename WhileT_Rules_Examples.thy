theory
  WhileT_Rules_Examples
imports
  Sepreftime
begin




lemma
  assumes "whileT b c s = r"
  assumes IS: "\<And>s t'. I s = Some t' \<Longrightarrow> b s  \<Longrightarrow> c s \<noteq> FAILi \<and>  lst (c s) I \<ge> Some t'"
    (*  "T (\<lambda>x. T I (c x)) (SPECT (\<lambda>x. if b x then I x else None)) \<ge> Some 0" *) 
  assumes "I s = Some t'"
  assumes wf: "wf {(y, x)|x M y. I x \<noteq> None \<and> b x \<and> c x = SPECT M \<and> M y \<noteq> None}"
  shows whileT_rule: "lst r (\<lambda>x. if b x then None else I x) \<ge> Some t'"
  using assms(1,3)
  unfolding whileT_def
proof (induction arbitrary: t' rule: RECT_wf_induct[where R="{(y, x)|x M y. I x \<noteq> None \<and> b x \<and> c x = SPECT M \<and> M y \<noteq> None}"])
  case 1
  show ?case by fact
next
  case 2
  then show ?case by refine_mono 
next
  case step: (3 x D r t')

  { assume b:"b x"
    with  IS step(3) have pff: "Some t' \<le> lst (c x) I" and cnofail: "c x \<noteq> FAILi" by auto
    from b step(2) have r: "r = bindT (c x) D" by auto
    from cnofail obtain M where cM: "c x = SPECT M" by force

    from step(3) pff have inf: "I x \<le> lst (c x) I" by auto

    have k: "\<And>y. M y \<noteq> None \<Longrightarrow> I y \<noteq> None"
      using inf[unfolded T_pw cM mii_alt] by (auto simp: mm2_def step(3) split: option.splits) 

    { fix y t''
      have " None \<noteq> M y \<Longrightarrow> I y = Some t'' \<Longrightarrow> Some t'' \<le> lst (D y) (\<lambda>x. if b x then None else I x)"
        apply(rule step(1)[where y=y])
        subgoal apply auto subgoal using step(3) by auto subgoal using b by simp apply(rule exI[where x=M]) using cM  
          using leI by fastforce          
         apply simp   by metis
    } note pf=this

    { fix y

      from step(3) inf have pot_pays: "\<And>y. I x \<le> mm2 (I y) (M y)" unfolding T_pw mii_alt using cM by (auto split: nrest.splits)
      from pot_pays have ineq: "I x \<le> mm2 (I y) (M y)" by auto 

      have " Some t' \<le> mii (\<lambda>y. lst (D y) (\<lambda>x. if b x then None else I x)) (c x) y" 
        unfolding mii_alt using cM apply(auto split: nrest.splits) 
        unfolding mm2_def apply (auto split: option.splits)
        subgoal using pf  
          by (metis (no_types, lifting) Inf_option_def RETURNT_alt T_RETURNT lst_def k less_eq_option_Some_None option.distinct(1))
      proof - 
        fix th tn  (* time that we have, time that we need *)
        assume  My: "M y = Some tn" and T: "lst (D y) (\<lambda>x. if b x then None else I x) = Some th" 

        from ineq obtain tiy where Iy: "I y = Some tiy" using My step(3) by(auto simp: mm2_def split: if_splits option.splits)
        with ineq My step(3) have 2: "tiy \<ge> tn" and a2: "t' \<le> tiy - tn" by (auto simp: mm2_def split: if_splits) 
        from cM My pf have "Some tiy \<le> lst (D y) (\<lambda>x. if b x then None else I x)" by (simp add: \<open>I y = Some tiy\<close>)
        with T have 3: "tiy \<le> th" by simp

        { assume less: "th < tn"
          from 3 2 less show False by simp
        } 
        {
          assume notless: "~ th < tn"
          from notless have "tn \<le> th" by auto
          from enat_minus_mono[OF this 3]   have "tiy - tn \<le> th - tn" by auto
          with a2 show "t' \<le> th - tn" by auto 
        } 
      qed 
    }
    then have "Some t' \<le> lst (bindT (c x) D) (\<lambda>x. if b x then None else I x)"
      apply(simp add: T_bindT) unfolding T_pw by auto
    then have ?case unfolding r by auto
  }
  moreover
  {
    assume nb: "\<not> b x"
    with  step(2) have "r = RETURNT x" by auto
    then have ?case using nb step(3) by (simp add: T_RETURNT)
  }
  ultimately have i: ?case by auto

  thm step.IH
  note IH = step.IH[OF _ refl]
  note IS' = IS[THEN conjunct2]
  note step.hyps[symmetric, simp]   

  from step.prems
  have ?case 
    apply clarsimp apply safe
    subgoal 
      apply vcg           
      apply (rule T_conseq6)  
        apply (rule IS')
      apply simp_all
      apply (rule T_conseq6)
        apply (rule IH)
      subgoal for y  by simp 
      apply simp
      by (auto split: if_splits) 
    subgoal by vcg
    done 
  from i show ?case .
qed


lemma
  assumes "whileT b c s = r"
  assumes IS[vcg_rules]: "\<And>s t'. I s = Some t' \<Longrightarrow> b s 
           \<Longrightarrow>    lst (c s) (\<lambda>s'. if (s',s)\<in>R then I s' else None) \<ge> Some t'"
    (*  "T (\<lambda>x. T I (c x)) (SPECT (\<lambda>x. if b x then I x else None)) \<ge> Some 0" *) 
  assumes "I s = Some t"
  assumes wf: "wf R"
  assumes exit: "\<And>s t'. I s = Some t' \<Longrightarrow> \<not>b s \<Longrightarrow> Q s \<ge> Some t'"
  shows whileT_rule''a_: "lst r Q \<ge> Some t"
  using assms(1,3)
  unfolding whileT_def
proof (induction arbitrary: t rule: RECT_wf_induct[where R="R"])
  case 1  
  show ?case by fact
next
  case 2
  then show ?case by refine_mono
next
  case step: (3 x D r t') 
  note IH[vcg_rules] = step.IH[OF _ refl] 
  note step.hyps[symmetric, simp]   

  from step.prems
  show ?case 
    apply clarsimp
    apply safe 
    apply vcg'   using exit by simp
qed



lemma waux1: "(\<forall>s t'. I s = Some t' \<longrightarrow> b s  \<longrightarrow> c s \<noteq> FAILi \<and>  lst (c s) (Q s) \<ge> Some t')
    = (lst (SPECT (\<lambda>x. if b x then I x else None)) (\<lambda>s. lst (c s) (Q s)) \<ge> Some 0)"
  apply(subst (2)T_pw) unfolding mii_alt apply simp
  by (force simp: mm2_def split: option.splits) 


lemma waux2: "(\<forall>s t'. I s = Some t' \<longrightarrow> lst (whileT b c s) (\<lambda>x. if b x then None else I x) \<ge> Some t')
      = (lst (SPECT I) (\<lambda>s. lst (whileT b c s) (\<lambda>x. if b x then None else I x)) \<ge> Some 0)"  
  apply(subst (2) T_pw) unfolding mii_alt apply simp
  by (force simp: mm2_def split: option.splits)  

lemma 
  assumes IS: "lst (SPECT (\<lambda>x. if b x then I x else None)) (\<lambda>s. lst (c s) (\<lambda>s'. if (s',s)\<in>R then I s' else None)) \<ge> Some 0" 
  assumes wf: "wf R"
  shows whileT_rule''_: "lst (SPECT I) (\<lambda>s. lst (whileT b c s) (\<lambda>x. if b x then None else I x)) \<ge> Some 0"
  using IS   unfolding  waux1[symmetric] unfolding  waux2[symmetric]  using whileT_rule''[OF _ _ _ wf]
  by blast



 

lemma
  assumes "whileT b c s = r"
  assumes IS[vcg_rules]: "\<And>s t'. I s = Some t' \<Longrightarrow> b s  \<Longrightarrow> lst (c s) I \<ge> Some t'"
    (*  "T (\<lambda>x. T I (c x)) (SPECT (\<lambda>x. if b x then I x else None)) \<ge> Some 0" *) 
  assumes "I s = Some t'"
  assumes wf: "wf {(y, x)|x M y. I x \<noteq> None \<and> b x \<and> c x = SPECT M \<and> M y \<noteq> None}"
  shows whileT_rule': "lst r (\<lambda>x. if b x then None else I x) \<ge> Some t'"
  using assms(1,3)
  unfolding whileT_def
proof (induction arbitrary: t' rule: RECT_wf_induct[where R="{(y, x)|x M y. I x \<noteq> None \<and> b x \<and> c x = SPECT M \<and> M y \<noteq> None}"])
  case 1
  show ?case by fact
next
  case 2
  then show ?case by refine_mono
next
  case step: (3 x D r t')

  note IH[vcg_rules] = step.IH[OF _ refl]
  note step.hyps[symmetric, simp]   

  from step.prems
  show ?case 
    apply clarsimp
    apply safe
     apply vcg'  
    done 
qed

 




subsection "Examples"


experiment
begin

lemma 
  assumes c: "c = (\<lambda>s. SPECT [s-1\<mapsto>1])" 
      and n: "S\<le>n"
  shows ex4: "lst (whileT (\<lambda>s. s>0) c (S::nat)) (\<lambda>s. if s = 0 then Some (enat n) else None) \<ge> Some 0"
  apply(rule T_conseq4)
   apply(rule whileT_rule'''[where I="\<lambda>s. if s\<le>n then Some (s) else None" ])
      apply simp
  subgoal unfolding c unfolding progress_def by (auto split: if_splits simp add:  )
  subgoal unfolding c apply(auto simp: T_REST split: if_splits) 
    by(auto simp: mm2_def mm3_def one_enat_def)
  using n by (auto simp: mm3_Some_conv split: if_splits) 


lemma assumes "c = (\<lambda>s. SPECT [s-1\<mapsto>1])" 
      and n: "S\<le>n"
      shows ex4': "(whileT (\<lambda>s. s>0) c (S::nat)) \<le> SPECT (\<lambda>s. if s = 0 then Some (enat n) else None)"
  apply(rule T_specifies_I) 
  apply(rule ex4) using assms by auto

lemma 
  assumes c: "c = (\<lambda>s. SPECT [s-1\<mapsto>1])" 
      and n: "S\<le>n"
  shows "lst (whileT (\<lambda>s. s>0) c (S::nat)) (\<lambda>s. if s = 0 then Some (enat n) else None) \<ge> Some 0"
  apply(rule T_conseq4)
   apply(rule whileT_rule''[where I="\<lambda>s. if s\<le>n then Some (enat (n - s)) else None"
            and R="measure nat"])
      apply simp
  subgoal unfolding c apply (simp add: T_REST mm2_def) apply (auto split: if_splits)
     apply (simp add: one_eSuc zero_enat_def) 
    by (simp add: one_enat_def)
    using n apply simp 
  subgoal  by blast
  by (auto split: if_splits)

term emb'
lemma 
  assumes c: "c = (\<lambda>s. SPECT [s-1\<mapsto>1])" 
      and n: "S\<le>n"
  shows "lst (whileT (\<lambda>s. s>0) c (S::nat)) (\<lambda>s. if s = 0 then Some (enat n) else None) \<ge> Some 0"
  apply(rule T_conseq4)
   apply(rule whileT_rule[where I="\<lambda>s. if s\<le>n then Some (enat (n - s)) else None"])
      apply simp
  subgoal unfolding c apply (simp add: T_REST mm2_def) apply (auto split: if_splits)
     apply (simp add: one_eSuc zero_enat_def) 
    by (simp add: one_enat_def)
    using n apply simp 
  subgoal using c apply auto 
    apply(rule wf_bounded_measure[where ub="\<lambda>_. n" and f="\<lambda>s. n - s"])
    by auto 
  by (auto split: if_splits)

lemma                                       (* hmmm *)
  assumes c: "c = (\<lambda>s. SPECT (\<lambda>s'. if s'<s \<and> even s then Some C else None))"  
  shows "lst (whileT (\<lambda>s. s>0) c (S::nat)) (\<lambda>s. if s = 0 then Some \<infinity> else None) \<ge> Some 0"
  apply(rule T_conseq4)
   apply(rule whileT_rule[where I="\<lambda>s. Some \<infinity>"])
      apply simp
  subgoal for s unfolding c by (simp add: T_pw mii_alt mm2_def)
    apply simp 
  subgoal using c apply auto  
    by (smt case_prodI le_less_linear mem_Collect_eq nz_le_conv_less prod.sel(2) wf wf_def)
  by (auto split: if_splits)




lemma                                       
  assumes c[vcg_rules]: "\<And>s. c s \<le> SPECT (\<lambda>s'. if s'<s \<and> even s then Some C else None)"  
  shows "lst (whileT (\<lambda>s. s>0) c (S::nat)) (\<lambda>s. if s \<le> 0 then Some \<infinity> else None) \<ge> Some 0"
  apply(rule  whileT_rule''[where I="\<lambda>s. Some \<infinity>" and R="{(x, y). x < y}", THEN T_conseq4])
      apply simp 
     apply(rule T_conseq4)
      apply(rule T_specifies_rev[OF c])  
     apply (auto split: if_splits)[1]
  apply simp apply(fact wf) by (auto split: if_splits)  




print_statement whileT_rule''

lemma  whileTI_rule[vcg_rules]:
  assumes 
      "\<And>s t'. I s = Some t' \<Longrightarrow> b s \<Longrightarrow> Some t' \<le> lst (c s) (\<lambda>s'. if (s', s) \<in> R then I s' else None)"
    and "I s = Some t'"
    and "wf R"
  shows "Some t' \<le> lst (whileTI I R b c s) (\<lambda>x. if b x then None else I x)"
  unfolding   whileTI_def
  apply(rule whileT_rule''[where I=I and R=R])
  apply simp apply fact+ done
 
lemma                                       (* hmmm *)
  assumes c[vcg_rules]: "\<And>s. Some 0 \<le> lst (c s) (\<lambda>s'. if s' < s \<and> even s then Some C else None)"  
  shows "lst (whileTI (\<lambda>s. Some \<infinity>) {(x, y). x < y} (\<lambda>s. s>0) c (S::nat)) (\<lambda>s. if s \<le> 0 then Some \<infinity> else None) \<ge> Some 0"
  apply vcg  
     apply (auto split: if_splits)   by(fact wf) 



lemma   fixes n :: nat
  assumes [vcg_rules]: "lst f (\<lambda>s. if s \<le> n then Some 1 else None) \<ge> Some 0"
   and  c[vcg_rules]: "\<And>s. Some 0 \<le> lst (c s) (\<lambda>s'. if s' < s then Some (enat C) else None)"
   and C: "C>0"
  shows "lst (
        do { n \<leftarrow> f;
             whileT (\<lambda>s. s>0) c n })  (\<lambda>s. if s \<le> 0 then Some (1+C*n) else None) \<ge> Some 0"
    (* note that n is bound from the outside ! *)
  apply(subst whileTI_def[symmetric, where I="(\<lambda>s. if s\<le>n then Some (1+C*(enat (n-s))) else None)"
                                    and R="  {(x, y). x < y}"])
  apply vcg 
  apply(auto simp: wf one_enat_def split: if_splits) 
  proof -
    fix x s xa   
    assume "x \<le> n " " s \<le> n " " xa < s"
    then have i: "((n - s) + 1) \<le> (n - xa)" by linarith  
    have "C * (n - s) + C = C * ((n - s) + 1)" by simp
    also have "\<dots> \<le> C * (n - xa)"  apply(rule mult_left_mono) apply fact by simp
    finally  
    show "C * (n - s) + C \<le> C * (n - xa)" .
  qed 


lemma   fixes n :: nat
  assumes [vcg_rules]: "lst f (\<lambda>s. if s \<le> n then Some 1 else None) \<ge> Some 0"
   and  c[vcg_rules]: "\<And>s. Some 0 \<le> lst (c s) (\<lambda>s'. if s' < s then Some (enat C) else None)"
   and C: "C>0"
  shows "lst (
        do { n \<leftarrow> f;
             whileTI (\<lambda>s. if s\<le>n then Some (1+C*(enat (n-s))) else None)  {(x, y). x < y}  (\<lambda>s. s>0) c n })
         (\<lambda>s. if s \<le> 0 then Some (1+C*n) else None)  \<ge> Some 0" 
    (* note that n in the Invariant is bound from the inside, very much in contrast to the example above! ! *)
  apply vcg 
  apply(auto simp: wf one_enat_def split: if_splits) 
  proof -
    fix x s xa   
    assume "x \<le> n " " s \<le> x " " xa < s"
    then have i: "((x - s) + 1) \<le> (x - xa)" by linarith  
    have "C * (x - s) + C = C * ((x - s) + 1)" by simp
    also have "\<dots> \<le> C * (x - xa)"  apply(rule mult_left_mono) apply fact by simp
    finally  
    show "C * (x - s) + C \<le> C * (x - xa)" .
  qed
  


lemma dont_care_about_runtime_as_long_as_it_terminates: 
    (* here:
        * the cost C of of the loop body (decrementing s) may even be \<infinity>
        * the starting state S is also arbitrary *)
  assumes c: "c = (\<lambda>s. SPECT [s-1\<mapsto>C])"
  shows "lst (whileT (\<lambda>s. s>0) c (S::nat)) (\<lambda>s. if s = 0 then Some \<infinity> else None) \<ge> Some 0"
  apply(rule T_conseq4)
   apply(rule whileT_rule[where I="\<lambda>s. Some \<infinity>"])
      apply simp
  subgoal for s unfolding c by (simp add: T_REST mm2_def)  
    apply simp 
  subgoal using c apply auto  
    by (smt case_prodI le_less_linear mem_Collect_eq nz_le_conv_less prod.sel(2) wf wf_def) 
  by (auto split: if_splits)

end

 


end