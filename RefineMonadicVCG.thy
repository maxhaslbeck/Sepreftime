theory RefineMonadicVCG
imports "Refine_Imperative_HOL/Sepref"
begin

(* TODO: move *)

lemma RETURN_le_RETURN_iff[simp]: "RETURNT x \<le> RETURNT y \<longleftrightarrow> x=y"
  apply auto
  by (simp add: pw_le_iff)

lemma [sepref_import_param]: 
  "((=),(=))\<in>Id\<rightarrow>Id\<rightarrow>Id" 
  "((<),(<))\<in>Id\<rightarrow>Id\<rightarrow>Id" 
  by simp_all






lemma REST_single_rule[vcg_simp_rules]: "Some t \<le> TTT Q (REST [x\<mapsto>t']) \<longleftrightarrow> Some (t+t') \<le> (Q x)"
  by (simp add: T_REST aux1')

thm T_pw refine_pw_simps

thm pw_le_iff

lemma T_ASSERT[vcg_simp_rules]: "Some t \<le> TTT Q (ASSERT \<Phi>) \<longleftrightarrow> Some t \<le> Q () \<and> \<Phi>"
  apply (cases \<Phi>)
   apply vcg'
  done

subsection \<open>Progress rules and solver\<close>

named_theorems progress_rules

lemma progress_SELECT_iff: "progress (SELECT P T) \<longleftrightarrow> T > 0"
  unfolding progress_def SELECT_def emb'_def by (auto split: option.splits)

lemmas [progress_rules] = progress_SELECT_iff[THEN iffD2]

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



method progress methods solver = 
  (rule asm_rl[of "progress _"] , (simp split: prod.splits | intro allI impI conjI | determ \<open>rule progress_rules\<close> | rule disjI1; progress \<open>solver\<close>; fail | rule disjI2; progress \<open>solver\<close>; fail | solver)+) []
method progress' methods solver = 
  (rule asm_rl[of "progress _"] , (simp split: prod.splits | intro allI impI conjI | determ \<open>rule progress_rules\<close> | rule disjI1 disjI2; progress'\<open>solver\<close> | solver)+) []





subsection \<open>VCG for monadic programs\<close>

method vcg' methods solver uses rules = ((rule rules vcg_rules[THEN T_conseq6] | progress\<open>auto\<close> | clarsimp split: option.splits if_splits simp: vcg_simp_rules | intro allI impI conjI | (solver; fail) )+)


thm vcg_rules

subsection \<open>Stuff involcing mm3 and emb\<close>

lemma Some_le_mm3_Some_conv[vcg_simp_rules]: "Some t \<le> mm3 t' (Some t'') \<longleftrightarrow> (t'' \<le> t' \<and> t \<le> enat (t' - t''))"
  by (simp add: mm3_def)


lemma Some_le_emb'_conv[vcg_simp_rules]: "Some t \<le> emb' Q ft x \<longleftrightarrow> Q x \<and> t \<le> ft x"
  by (auto simp: emb'_def)

lemma Some_eq_emb'_conv[vcg_simp_rules]: "emb' Q tf s = Some t \<longleftrightarrow> (Q s \<and> t = tf s)"
  unfolding emb'_def by(auto split: if_splits)



lemma embtimeI: "T \<le> T' \<Longrightarrow> emb P T \<le> emb P T'" unfolding emb'_def by (auto simp: le_fun_def split:  if_splits)

lemma not_cons_is_Nil_conv[simp]: "(\<forall>y ys. l \<noteq> y # ys) \<longleftrightarrow> l=[]" by (cases l) auto

lemma mm3_Some0_eq[simp]: "mm3 t (Some 0) = Some t"
  by (auto simp: mm3_def)


lemma ran_emb': "c \<in> ran (emb' Q t) \<longleftrightarrow> (\<exists>s'. Q s' \<and> t s' = c)"
  by(auto simp: emb'_def ran_def)

lemma ran_emb_conv: "Ex Q \<Longrightarrow>  ran (emb Q t) = {t}"
  by (auto simp: ran_emb')

lemma in_ran_emb_special_case: "c\<in>ran (emb Q t) \<Longrightarrow> c\<le>t"
  apply (cases "Ex Q")
   apply (auto simp: ran_emb_conv)
  apply (auto simp: emb'_def)
  done

lemma dom_emb'_eq[simp]: "dom (emb' Q f) = Collect Q"
  by(auto simp: emb'_def split: if_splits)


lemma emb_le_emb: "emb' P T \<le> emb' P' T' \<longleftrightarrow> (\<forall>x. P x \<longrightarrow> P' x \<and>  T x \<le> T' x)"
  unfolding emb'_def by (auto simp: le_fun_def split: if_splits)



  thm vcg_rules


lemma T_RESTemb_iff: "Some t'
       \<le> TTT Q (REST (emb' P t)) \<longleftrightarrow> (\<forall>x. P x \<longrightarrow> Some (t' + t x) \<le> Q x ) "
  by(auto simp: emb'_def T_pw mii_alt aux1)  


lemma T_RESTemb: "(\<And>x. P x \<Longrightarrow> Some (t' + t x) \<le> Q x)
    \<Longrightarrow>  Some t' \<le> TTT Q (REST (emb' P t))  "
  by (auto simp: T_RESTemb_iff)

(* lemmas [vcg_rules] = T_RESTemb_iff[THEN iffD2] *)

end