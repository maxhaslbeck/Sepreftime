theory SepLogic_Misc
imports "../Imperative_HOL_Time/SepLogicTime/SepAuto"
begin


lemma mod_star_trueI: "h\<Turnstile>P \<Longrightarrow> h\<Turnstile>P*true"  
  by (metis assn_times_comm entailsD' entails_true mult.left_neutral) 


lemma merge_true_star[simp]: "true*true = true"
  using top_assn_reduce by auto

lemma mod_false[simp]: "\<not> h\<Turnstile>false"  
  by (simp add: pure_assn_rule)
lemma mod_pure_star_dist[simp]: "h\<Turnstile>P*\<up>b \<longleftrightarrow> h\<Turnstile>P \<and> b"
  by (simp add: mod_pure_star_dist)


lemma pure_assn_eq_conv[simp]: "\<up>P = \<up>Q \<longleftrightarrow> P=Q" 
  by (metis (full_types) assn_times_comm empty_iff in_range.simps mod_false' mod_pure_star_dist top_assn_rule)

thm entailsD

lemma ent_true[simp]: "P \<Longrightarrow>\<^sub>A true" 
  by (simp add: entails_true) 



lemma ent_star_mono: "\<lbrakk> P \<Longrightarrow>\<^sub>A P'; Q \<Longrightarrow>\<^sub>A Q'\<rbrakk> \<Longrightarrow> P*Q \<Longrightarrow>\<^sub>A P'*Q'" 
  using entail_trans2 entails_frame by blast


lemma merge_true_star_ctx: "true * (true * P) = true * P"
  by (metis assn_times_assoc top_assn_reduce)

lemma pf: "(a::assn) * b = b * a" 
  using assn_times_comm by auto 

lemma ent_true_drop: 
  "P\<Longrightarrow>\<^sub>AQ*true \<Longrightarrow> P*R\<Longrightarrow>\<^sub>AQ*true"
  "P\<Longrightarrow>\<^sub>AQ \<Longrightarrow> P\<Longrightarrow>\<^sub>AQ*true"
  apply (metis assn_times_comm ent_star_mono ent_true merge_true_star_ctx)
  apply (metis assn_one_left ent_star_mono ent_true pf)
  done


lemma ent_true_drop_fst: 
  "R\<Longrightarrow>\<^sub>AQ*true \<Longrightarrow> P*R\<Longrightarrow>\<^sub>AQ*true" 
  apply (metis assn_times_comm ent_star_mono ent_true merge_true_star_ctx) 
  done


lemma entailsI: 
  assumes "\<And>h. h\<Turnstile>P \<Longrightarrow> h\<Turnstile>Q"
  shows "P \<Longrightarrow>\<^sub>A Q" 
  using assms unfolding entails_def by auto

lemma entt_refl': "P\<Longrightarrow>\<^sub>A P * true" 
  by (simp add: entailsI mod_star_trueI) 

subsection "for relH"

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

subsection "new_addrs"

lemma new_addrs_id[simp]: "(new_addrs h as h) = as" unfolding new_addrs_def by auto

subsection "entailst"

definition entailst :: "assn \<Rightarrow> assn \<Rightarrow> bool" (infix "\<Longrightarrow>\<^sub>t" 10)
  where "entailst A B \<equiv> A \<Longrightarrow>\<^sub>A B * true"
lemma enttI: "A\<Longrightarrow>\<^sub>AB*true \<Longrightarrow> A\<Longrightarrow>\<^sub>tB" unfolding entailst_def .
lemma enttD: "A\<Longrightarrow>\<^sub>tB \<Longrightarrow> A\<Longrightarrow>\<^sub>AB*true" unfolding entailst_def .
                                   
lemma ent_trans[trans]: "\<lbrakk> P \<Longrightarrow>\<^sub>A Q; Q \<Longrightarrow>\<^sub>AR \<rbrakk> \<Longrightarrow> P \<Longrightarrow>\<^sub>A R"
  by (auto intro: entailsI dest: entailsD)


lemma entt_trans:
  "entailst A B \<Longrightarrow> entailst B C \<Longrightarrow> entailst A C"
  unfolding entailst_def
  apply (erule ent_trans)
  by (metis assn_times_assoc ent_star_mono ent_true merge_true_star)  

lemma ent_imp_entt: "P\<Longrightarrow>\<^sub>AQ \<Longrightarrow> P\<Longrightarrow>\<^sub>tQ" 
  apply (rule enttI)
  apply (erule ent_trans)
  by (simp add: entailsI mod_star_trueI)  


lemma entt_refl: "P\<Longrightarrow>\<^sub>t P " 
  by (simp add: entailst_def entailsI mod_star_trueI) 

subsection "Heap Or"
 
 
 

lemma ent_disjI1_direct[simp]: "A \<Longrightarrow>\<^sub>A A \<or>\<^sub>A B"
  by (simp add: entailsI or_assn_conv)  

lemma ent_disjI2_direct[simp]: "B \<Longrightarrow>\<^sub>A A \<or>\<^sub>A B"     
  by (simp add: entailsI or_assn_conv)  

lemma entt_disjI1_direct[simp]: "A \<Longrightarrow>\<^sub>t A \<or>\<^sub>A B"
  by (rule ent_imp_entt[OF ent_disjI1_direct])

lemma entt_disjI2_direct[simp]: "B \<Longrightarrow>\<^sub>t A \<or>\<^sub>A B"
  by (rule ent_imp_entt[OF ent_disjI2_direct])

lemma ent_disjE: "\<lbrakk> A\<Longrightarrow>\<^sub>AC; B\<Longrightarrow>\<^sub>AC \<rbrakk> \<Longrightarrow> A\<or>\<^sub>AB \<Longrightarrow>\<^sub>AC"
  by (simp add: entails_def or_assn_conv)  



subsection \<open>New command ureturn\<close>

definition ureturn :: "'a \<Rightarrow> 'a Heap" where
  [code del]: "ureturn x = Heap_Monad.heap (\<lambda>h. (x,h,0))"

lemma execute_ureturn [execute_simps]:
  "execute (ureturn x) = Some \<circ> (\<lambda>h. (x,h,0))"
  by (simp add: ureturn_def execute_simps)

lemma success_ureturnI [success_intros]:
  "success (ureturn x) h"
  by (rule successI) (simp add: execute_simps)

lemma effect_ureturnI [effect_intros]:
  "h = h' \<Longrightarrow> effect (ureturn x) h h' x 0"
  by (rule effectI) (simp add: execute_simps)

lemma effect_ureturnE [effect_elims]:
  assumes "effect (ureturn x) h h' r n"
  obtains "r = x" "h' = h" "n=0"
  using assms by (rule effectE) (simp add: execute_simps)
thm execute_return' 

lemma timeFrame0[simp]: "timeFrame 0 f = f" apply(cases f) by auto

lemma ureturn_bind [simp]: "ureturn x \<bind> f =   f x"
  apply (rule Heap_eqI)
  by (auto simp add: execute_simps )


lemma bind_ureturn [simp]: "f \<bind> ureturn =   f"
  by (rule Heap_eqI) (simp add: bind_def execute_simps split: option.splits)



lemma execute_ureturn' [rewrite]: "execute (ureturn x) h = Some (x, h, 0)" by (metis comp_eq_dest_lhs execute_ureturn)

lemma run_ureturnD: "run (ureturn x) (Some h) \<sigma> r t \<Longrightarrow> \<sigma> = Some h \<and> r = x \<and> t = 0"
  by (auto simp add: execute_ureturn' run.simps)

lemma return_rule:
  "<$0> ureturn x <\<lambda>r. \<up>(r = x)>" 
  unfolding hoare_triple_def apply (auto dest!: run_ureturnD simp: timeCredit_assn_rule)
  subgoal by (metis (mono_tags, hide_lams) pheap.sel(2) pheap.sel(3) pure_assn_rule)
  subgoal using relH_def by fastforce 
  done


subsection "Heap And"
 


lemma mod_and_dist: "h\<Turnstile>P\<and>\<^sub>AQ \<longleftrightarrow> h\<Turnstile>P \<and> h\<Turnstile>Q"
  by (rule and_assn_conv) 

subsection {* Precision *}
text {*
  Precision rules describe that parts of an assertion may depend only on the
  underlying heap. For example, the data where a pointer points to is the same
  for the same heap.
*}
text {* Precision rules should have the form: 
  @{text [display] "\<forall>x y. (h\<Turnstile>(P x * F1) \<and>\<^sub>A (P y * F2)) \<longrightarrow> x=y"}*}
definition "precise R \<equiv> \<forall>a a' h p F F'. 
  h \<Turnstile> R a p * F \<and>\<^sub>A R a' p * F' \<longrightarrow> a = a'"

lemma preciseI[intro?]: 
  assumes "\<And>a a' h p F F'. h \<Turnstile> R a p * F \<and>\<^sub>A R a' p * F' \<Longrightarrow> a = a'"
  shows "precise R"
  using assms unfolding precise_def by blast

lemma preciseD:
  assumes "precise R"
  assumes "h \<Turnstile> R a p * F \<and>\<^sub>A R a' p * F'"
  shows "a=a'"
  using assms unfolding precise_def by blast

lemma preciseD':
  assumes "precise R"
  assumes "h \<Turnstile> R a p * F" 
  assumes "h \<Turnstile> R a' p * F'"
  shows "a=a'"
  apply (rule preciseD)
  apply (rule assms)
  apply (simp only: mod_and_dist)
  apply (blast intro: assms)
  done

lemma precise_extr_pure[simp]: 
  "precise (\<lambda>x y. \<up>P * R x y) \<longleftrightarrow> (P \<longrightarrow> precise R)"
  "precise (\<lambda>x y. R x y * \<up>P) \<longleftrightarrow> (P \<longrightarrow> precise R)"
  (* apply (cases P, (auto intro!: preciseI) [2])+
  done *) sorry

lemma sngr_prec: "precise (\<lambda>x p. p\<mapsto>\<^sub>rx)" (*
  apply rule
  apply (clarsimp simp: mod_and_dist)
  unfolding sngr_assn_def times_assn_def
  apply (simp add: Abs_assn_inverse)
  apply auto
  done *) sorry

lemma snga_prec: "precise (\<lambda>x p. p\<mapsto>\<^sub>ax)" (*
  apply rule
  apply (clarsimp simp: mod_and_dist)
  unfolding snga_assn_def times_assn_def
  apply (simp add: Abs_assn_inverse)
  apply auto
  done *) sorry






end