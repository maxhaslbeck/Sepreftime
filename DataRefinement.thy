theory DataRefinement
imports Sepreftime
begin

subsection {* Data Refinement *}


lemma "{(1,2),(2,4)}``{1,2}={2,4}" by auto


definition conc_fun ("\<Down>") where
  "conc_fun R m \<equiv> case m of FAILi \<Rightarrow> FAILT | REST X \<Rightarrow> REST (\<lambda>c. Sup {X a| a. (c,a)\<in>R})"
                                                                  (* ^- not so sure here *)
definition abs_fun ("\<Up>") where
  "abs_fun R m \<equiv> case m of FAILi \<Rightarrow> FAILT 
    | REST X \<Rightarrow> if dom X\<subseteq>Domain R then REST (\<lambda>a. Sup {X c| c. (c,a)\<in>R}) else FAILT"
                                                (* ^- not so sure here *)
lemma 
  conc_fun_FAIL[simp]: "\<Down>R FAILT = FAILT" and
  conc_fun_RES: "\<Down>R (REST X) = REST (\<lambda>c. Sup {X a| a. (c,a)\<in>R})"
  unfolding conc_fun_def by (auto split: nrest.split)

(* 
lemma conc_fun_RES_sv: "single_valued R \<Longrightarrow> 
  \<Down>R (REST X) = REST (\<lambda>c. if c\<in>Dom R then Some (X Sup {X a| a. (c,a)\<in>R})"
*)

 
subsubsection \<open>Examples\<close>

definition Rset where "Rset = { (c,a)| c a. set c = a}"
                                     
lemma "RETURNT [1,2,3] \<le> \<Down>Rset (RETURNT {1,2,3})"
  unfolding conc_fun_def RETURNT_def Rset_def
  apply simp unfolding le_fun_def by auto

lemma "RETURNT [1,2,3] \<le> \<Down>Rset (RETURNT {1,2,3})"
  unfolding conc_fun_def RETURNT_def Rset_def
  apply simp unfolding le_fun_def by auto


definition Reven where "Reven = { (c,a)| c a. even c = a}"

lemma "RETURNT 3 \<le> \<Down>Reven (RETURNT False)"
  unfolding conc_fun_def RETURNT_def Reven_def
  apply simp unfolding le_fun_def by auto

lemma "m \<le> \<Down>Id m"
  unfolding conc_fun_def RETURNT_def 
  apply (cases m) by auto


lemma "m \<le> \<Down>{} m \<longleftrightarrow> (m=FAILT \<or> m = SPECT bot)"
  unfolding conc_fun_def RETURNT_def 
  apply (cases m) apply auto by (metis bot.extremum dual_order.antisym le_funI)


lemma abs_fun_simps[simp]: 
  "\<Up>R FAILT = FAILT"
  "dom X\<subseteq>Domain R \<Longrightarrow> \<Up>R (REST X) = REST (\<lambda>a. Sup {X c| c. (c,a)\<in>R})"
  "\<not>(dom X\<subseteq>Domain R) \<Longrightarrow> \<Up>R (REST X) = FAILT"
  unfolding abs_fun_def by (auto  split: nrest.split)

term single_valued
 
context fixes R assumes SV: "single_valued R" begin


lemma 
  fixes m :: "'b \<Rightarrow> enat option"
  shows
  Sup_sv: "(c, a') \<in> R \<Longrightarrow>  Sup {m a| a. (c,a) \<in> R} = m a'"
proof -
  assume "(c,a') \<in> R"
  with SV have singleton: "{m a| a. (c,a) \<in> R} = {m a'}" by(auto dest: single_valuedD) 
  show ?thesis unfolding singleton by simp
qed 

lemma indomD: " M c = Some y \<Longrightarrow> dom M \<subseteq> Domain R \<Longrightarrow> (\<exists>a. (c,a)\<in>R)"
  by auto

lemma conc_abs_swap: "m' \<le> \<Down>R m \<longleftrightarrow> \<Up>R m' \<le> m"
  apply rule
  subgoal (* <-- *)
  unfolding conc_fun_def abs_fun_def using SV
  apply (auto split: nrest.splits) 
  subgoal for M M'
    apply (auto simp add: le_fun_def)  
    by (smt Sup_least antisym le_cases mem_Collect_eq single_valuedD)  
  subgoal 
    by (smt Collect_cong Domain.DomainI domI domIff empty_Sup empty_def le_map_dom_mono set_rev_mp)    
  done

  subgoal (* \<longrightarrow> *)
    unfolding conc_fun_def abs_fun_def using SV
    apply(auto split: nrest.splits if_splits)
    apply (auto simp add: le_fun_def)
    subgoal for M M' c
      apply(cases "M c = None")
       apply auto apply(frule indomD) apply simp
      apply(auto)
      apply(simp only: Sup_sv)
       
      by (metis (mono_tags, lifting) Sup_le_iff mem_Collect_eq)
    done
  done

lemma 
  fixes m :: "'b \<Rightarrow> enat option"
  shows
  Inf_sv: "(c, a') \<in> R \<Longrightarrow>  Inf {m a| a. (c,a) \<in> R} = m a'"
proof -
  assume "(c,a') \<in> R"
  with SV have singleton: "{m a| a. (c,a) \<in> R} = {m a'}" by(auto dest: single_valuedD) 
  show ?thesis unfolding singleton by simp
qed 

lemma ac_galois: "galois_connection (\<Up>R) (\<Down>R)"
  apply (unfold_locales)
  by (rule conc_abs_swap)


lemma 
  fixes m :: "'b \<Rightarrow> enat option"
  shows 
  Sup_some_svD: "Sup {m a |a. (c, a) \<in> R} = Some t' \<Longrightarrow> (\<exists>a. (c,a)\<in>R \<and> m a = Some t')"
  using SV by (smt Sup_le_iff dual_order.antisym less_eq_option_Some_None mem_Collect_eq order_refl single_valued_def)
 

end 


lemma pw_abs_nofail[refine_pw_simps]: 
  "nofailT (\<Up>R M) \<longleftrightarrow> (nofailT M \<and> (\<forall>x. (\<exists>t. inresT M x t) \<longrightarrow> x\<in>Domain R))"
  apply (cases M)
  apply simp
  apply (auto simp: abs_fun_simps abs_fun_def)
  by (metis zero_enat_def zero_le)

(*
lemma pw_abs_inres[refine_pw_simps]: 
  "(\<exists>t. inresT (\<Up>R M) a t) \<longleftrightarrow> (nofailT (\<Up>R M) \<longrightarrow> (\<exists>c. (\<exists>t. inresT M c t) \<and> (c,a)\<in>R))"
  apply (cases M)
   apply simp
  apply rule
  subgoal for m
    apply (auto simp: abs_fun_def) (*    *)
    sorry
  subgoal for m
    sorry
  done
*)

lemma pw_conc_nofail[refine_pw_simps]: 
  "nofailT (\<Down>R S) = nofailT S"
  by (cases S) (auto simp: conc_fun_RES)

lemma "single_valued A \<Longrightarrow> single_valued B \<Longrightarrow> single_valued (A O B)"
  by (simp add: single_valued_relcomp)
  

lemma pw_conc_inres_sv[refine_pw_simps]:
  "single_valued R \<Longrightarrow> inresT (\<Down>R S') s t = (nofailT S' 
  \<longrightarrow> (\<exists>s'. (s,s')\<in>R \<and> inresT S' s' t))"
  apply (cases S')
  subgoal by simp
  subgoal  for m'
    apply rule
    subgoal 
      by (auto simp: conc_fun_RES dest!: Sup_some_svD)        
    subgoal 
      by (auto simp: conc_fun_RES Sup_sv )  
    done
  done

lemma 
  fixes m :: "'a \<Rightarrow> enat option"
  shows
  "single_valued R \<Longrightarrow> Sup {m a| a. (c,a) \<in> R} = None \<longleftrightarrow> c \<notin> Domain R"
  apply rule
  subgoal oops


lemma pw_conc_inres:
  "inresT (\<Down>R S') s t = (nofailT S' 
  \<longrightarrow> (\<exists>s'. (s,s')\<in>R \<and> inresT S' s' t))"
  apply (cases S')
  subgoal by simp
  subgoal  for m'
    apply rule
    subgoal 
      apply (auto simp: conc_fun_RES) sorry
    subgoal 
      apply (auto simp: conc_fun_RES) sorry
    done
  oops

lemma sv_the: "single_valued R \<Longrightarrow> (c,a) \<in> R \<Longrightarrow> (THE a. (c, a) \<in> R) = a"
  by (simp add: single_valued_def the_equality)

lemma
  conc_fun_RES_sv:
  assumes SV: "single_valued R"
  shows "\<Down>R (REST X) = REST (\<lambda>c. if c\<in>Domain R then X (THE a. (c,a)\<in>R) else None )"
  unfolding conc_fun_def
  apply(auto split: nrest.split)
  apply(rule ext)
  apply auto
  subgoal using  SV  by (auto simp: Sup_sv sv_the)
  subgoal by (smt Collect_cong Domain.DomainI empty_Sup empty_def)
  done


lemma conc_fun_mono[simp, intro!]: 
  assumes SV: "single_valued R"
  shows "mono (\<Down>R)"
  apply rule 
  apply (simp add: pw_le_iff)
  using SV by (auto simp: refine_pw_simps pw_conc_inres_sv) 


lemma conc_fun_R_mono:
  assumes "R \<subseteq> R'" and SV: "single_valued R'"
  shows "\<Down>R M \<le> \<Down>R' M"
  using assms
  by (auto simp: pw_le_iff refine_pw_simps single_valued_subset)


lemma conc_fun_chain:
  assumes SVR: "single_valued R" and SVS: "single_valued S"
  shows "\<Down>R (\<Down>S M) = \<Down>(R O S) M"
  apply(cases M)
  subgoal by simp
  apply simp
  using SVS apply(simp only: conc_fun_RES_sv)
  using SVR apply(simp only: conc_fun_RES_sv)
  using single_valued_relcomp[OF SVR SVS] apply(simp only: conc_fun_RES_sv)
  apply (auto split: nrest.split)
  apply (rule ext) apply auto
    apply(auto simp add: sv_the)  
  apply(subst sv_the) by auto


lemma conc_Id[simp]: "\<Down>Id = id"
  unfolding conc_fun_def [abs_def] by (auto split: nrest.split)

                                 
lemma conc_fun_fail_iff[simp]: 
  "\<Down>R S = FAILT \<longleftrightarrow> S=FAILT"
  "FAILT = \<Down>R S \<longleftrightarrow> S=FAILT"
  by (auto simp add: pw_eq_iff refine_pw_simps)


lemma conc_trans[trans]:
  assumes SV: "single_valued R" "single_valued R'"
    and A: "C \<le> \<Down>R B" and B: "B \<le> \<Down>R' A" 
  shows "C \<le> \<Down>R (\<Down>R' A)"
  using assms by (fastforce simp: pw_le_iff refine_pw_simps)

text {* WARNING: The order of the single statements is important here! *}
lemma conc_trans_additional[trans]:
  assumes "single_valued R"
  shows
  "\<And>A B C. A\<le>\<Down>R  B \<Longrightarrow> B\<le>    C \<Longrightarrow> A\<le>\<Down>R  C"
  "\<And>A B C. A\<le>\<Down>Id B \<Longrightarrow> B\<le>\<Down>R  C \<Longrightarrow> A\<le>\<Down>R  C"
  "\<And>A B C. A\<le>\<Down>R  B \<Longrightarrow> B\<le>\<Down>Id C \<Longrightarrow> A\<le>\<Down>R  C"

  "\<And>A B C. A\<le>\<Down>Id B \<Longrightarrow> B\<le>\<Down>Id C \<Longrightarrow> A\<le>    C"
  "\<And>A B C. A\<le>\<Down>Id B \<Longrightarrow> B\<le>    C \<Longrightarrow> A\<le>    C"
  "\<And>A B C. A\<le>    B \<Longrightarrow> B\<le>\<Down>Id C \<Longrightarrow> A\<le>    C"
  using assms conc_trans[where R=R and R'=Id]
  by (auto intro: order_trans)



end