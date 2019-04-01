theory 
  Sepreftime_Auxiliaries
imports
  "HOL-Library.Extended_Nat" "Automatic_Refinement.Automatic_Refinement"  
begin




section "Auxiliaries"

subsection "Auxiliaries for option"

lemma less_eq_option_None_is_None': "x \<le> None \<longleftrightarrow> x = None" by(auto simp: less_eq_option_None_is_None)

lemma everywhereNone: "(\<forall>x\<in>X. x = None) \<longleftrightarrow> X = {} \<or> X = {None}"
  by auto

subsection "Auxiliaries for enat"



lemma enat_minus_mono: "a' \<ge> b \<Longrightarrow> a' \<ge> a \<Longrightarrow> a' - b \<ge> (a::enat) - b"
  apply(cases a; cases b; cases a') by auto

lemma enat_plus_minus_aux1: "a + b \<le> a' \<Longrightarrow> \<not> a' < a \<Longrightarrow> b \<le> a' - (a::enat)"
  apply(cases a; cases b; cases a') by auto

lemma enat_plus_minus_aux2: "\<not> a < a' \<Longrightarrow> b \<le> a - a' \<Longrightarrow> a' + b \<le> (a::enat)"
  apply(cases a; cases b; cases a') by auto

lemma enat_minus_inf_conv[simp]: "a - enat n = \<infinity> \<longleftrightarrow> a=\<infinity>" by (cases a) auto
lemma enat_minus_fin_conv[simp]: "a - enat n = enat m \<longleftrightarrow> (\<exists>k. a=enat k \<and> m = k - n)" by (cases a) auto

lemma helper: "x2 \<le> x2a \<Longrightarrow> \<not> x2 < a \<Longrightarrow> \<not> x2a < a \<Longrightarrow>  x2 - (a::enat) \<le> x2a - a"
  apply(cases x2; cases x2a) apply auto apply(cases a) by auto

lemma helper2: "x2b \<le> x2 \<Longrightarrow> \<not> x2a < x2  \<Longrightarrow> \<not> x2a < x2b \<Longrightarrow> x2a - (x2::enat) \<le> x2a - x2b"
  apply(cases x2; cases x2a) apply auto apply(cases x2b) by auto

lemma Sup_finite_enat: "Sup X = Some (enat a) \<Longrightarrow> Some (enat a) \<in> X"
  by (auto simp: Sup_option_def Sup_enat_def these_empty_eq Max_eq_iff in_these_eq split: if_splits)

lemma Sup_enat_less2: " Sup X = \<infinity> \<Longrightarrow> (\<exists>x\<in>X. enat t < x)"
  unfolding  Sup_enat_def using    finite_enat_bounded linear 
  apply(auto split: if_splits)  
   apply (smt Max_in empty_iff enat_ord_code(4))
  by (smt not_less)  


lemma [simp]: "t \<le> Some (\<infinity>::enat)"
  by (cases t, auto)

subsection "Auxiliary (for Sup and Inf)"



lemma aux11: "f`X={y} \<longleftrightarrow> (X\<noteq>{} \<and> (\<forall>x\<in>X. f x = y))" by auto
 
lemma aux2: "(\<lambda>f. f x) ` {[x \<mapsto> t1] |x t1. M x = Some t1} = {None} \<longleftrightarrow> (M x = None \<and> M\<noteq>Map.empty)"
  apply (cases "M x"; auto simp: aux11)
  by force

lemma aux3: "(\<lambda>f. f x) ` {[x \<mapsto> t1] |x t1. M x = Some t1} = {Some t1 | t1. M x = Some t1} \<union> ({None | y. y\<noteq>x \<and> M y \<noteq> None })"
  by (fastforce split: if_splits simp: image_iff) 

lemma Sup_pointwise_eq_fun: "(SUP f:{[x \<mapsto> t1] |x t1. M x = Some t1}. f x) = M x"
  unfolding Sup_option_def  
  apply (simp add: aux2) 
  apply (auto simp: aux3)
  by (metis (mono_tags, lifting) Some_image_these_eq Sup_least in_these_eq mem_Collect_eq sup_absorb1 these_image_Some_eq)


lemma SUP_eq_None_iff: "(SUP f:X. f x) = None \<longleftrightarrow> X={} \<or> (\<forall>f\<in>X. f x = None)"
  by (smt SUP_bot_conv(2) SUP_empty Sup_empty empty_Sup)

lemma SUP_eq_Some_iff: "(SUP f:X. f x) = Some t \<longleftrightarrow> (\<exists>f\<in>X. f x \<noteq> None) \<and> (t=Sup {t' | f t'. f\<in>X \<and> f x = Some t' })"
  apply auto
  subgoal 
    by (smt Sup_bot_conv(1) Sup_empty Sup_option_def Sup_pointwise_eq_fun imageE option.distinct(1))
  subgoal 
    unfolding Sup_option_def
    apply (clarsimp split: if_splits)
    apply (fo_rule arg_cong)
    apply (auto simp: Option.these_def)
    apply (metis (mono_tags, lifting) image_iff mem_Collect_eq option.sel)
    apply (metis (mono_tags, lifting) image_iff mem_Collect_eq option.sel)
    done
  subgoal 
    unfolding Sup_option_def
    apply (clarsimp split: if_splits; safe)
    subgoal by (force simp: image_iff)
    apply (fo_rule arg_cong)
    apply (auto simp: Option.these_def)
    apply (metis (mono_tags, lifting) image_iff mem_Collect_eq option.sel)
    done
  done  



lemma Sup_enat_less: "X \<noteq> {} \<Longrightarrow> enat t \<le> Sup X \<longleftrightarrow> (\<exists>x\<in>X. enat t \<le> x)"
  apply rule
  subgoal 
  by (metis Max_in Sup_enat_def finite_enat_bounded linear) 
  subgoal apply auto
    by (simp add: Sup_upper2)
  done


(* 
  This is how implication can be phrased with an Inf operation.
  Generalization from boolean to enat can be explained this way.
 *)

lemma fixes Q P  shows
    "Inf { P x \<le> Q x |x. True}  \<longleftrightarrow> P \<le> Q" unfolding le_fun_def by simp

end