theory RefineMonadicVCG
imports "Refine_Imperative_HOL/Sepref"
begin


lemma REST_single_rule[vcg_simp_rules]: "Some t \<le> TTT Q (REST [x\<mapsto>t']) \<longleftrightarrow> Some (t+t') \<le> (Q x)"
  by (simp add: T_REST aux1')

thm T_pw refine_pw_simps

thm pw_le_iff

lemma [vcg_simp_rules]: "Some t \<le> TTT Q (ASSERT \<Phi>) \<longleftrightarrow> \<Phi> \<and> Some t \<le> Q ()"
  apply (cases \<Phi>)
   apply vcg'
  done

named_theorems progress_rules

method progress methods solver = 
  (rule asm_rl[of "progress _"] , (simp split: prod.splits | intro allI impI conjI | determ \<open>rule progress_rules\<close> | rule disjI1; progress \<open>solver\<close>; fail | rule disjI2; progress \<open>solver\<close>; fail | solver)+) []
method progress' methods solver = 
  (rule asm_rl[of "progress _"] , (simp split: prod.splits | intro allI impI conjI | determ \<open>rule progress_rules\<close> | rule disjI1 disjI2; progress'\<open>solver\<close> | solver)+) []


method vcg' methods solver uses rules = ((rule rules vcg_rules[THEN T_conseq6] | progress\<open>auto\<close> | clarsimp split: if_splits simp: vcg_simp_rules | intro allI impI conjI | (solver; fail) )+)


thm vcg_rules

thm RETURNT_def

lemma Some_le_mm3_Some_conv[vcg_simp_rules]: "Some t \<le> mm3 t' (Some t'') \<longleftrightarrow> (t'' \<le> t' \<and> t \<le> enat (t' - t''))"
  by (simp add: mm3_def)


lemma Some_le_emb'_conv[vcg_simp_rules]: "Some t \<le> emb' Q ft x \<longleftrightarrow> Q x \<and> t \<le> ft x"
  by (auto simp: emb'_def)


lemma not_cons_is_Nil_conv[simp]: "(\<forall>y ys. l \<noteq> y # ys) \<longleftrightarrow> l=[]" by (cases l) auto

lemma mm3_Some0_eq[simp]: "mm3 t (Some 0) = Some t"
  by (auto simp: mm3_def)


lemma progress_REST_iff: "progress (REST [x \<mapsto> t]) \<longleftrightarrow> t\<noteq>0"
  by (auto simp: progress_def)

lemmas [progress_rules] = progress_REST_iff[THEN iffD2]




lemma progress_ASSERT_bind[progress_rules]: "\<lbrakk>\<Phi> \<Longrightarrow> progress (f ()) \<rbrakk> \<Longrightarrow> progress (ASSERT \<Phi>\<bind>f)"
  apply (cases \<Phi>)
  apply (auto simp: progress_def)
  done

lemma progress_bind[progress_rules]: "progress m \<or> (\<forall>x. progress (f x)) \<Longrightarrow> progress (m\<bind>f)"
  apply (auto simp: progress_def)
  sorry



end