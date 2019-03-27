theory Join
  imports Sepreftime "Refine_Monadic.Refine_Monadic"
begin


typ "'a nres"
typ "'a nrest"

fun einb :: "'a nres \<Rightarrow> 'a nrest" where
 "einb FAILi = FAILT"
| "einb (RES M) = REST (\<lambda>e. if e\<in>M then Some \<infinity> else None) "

lemma einb_FAIL[simp]: "einb FAIL = FAILT"
  unfolding top_nres_def by(simp only: einb.simps)

lemma grr: "A \<le> SPECT M \<Longrightarrow> A \<le> SPECT M' \<Longrightarrow> A \<le> SPECT (inf M M')"
  apply(cases A) apply simp by simp  

lemma join: assumes  "A \<le> Sepreftime.SPEC Q t" "A \<le> Sepreftime.SPEC Q' t'" 
  shows "A \<le> Sepreftime.SPEC (\<lambda>p. Q p \<and> Q' p) (inf t t')"
proof - 
  have t: "SPECT (\<lambda>v. if Q v \<and> Q' v then Some (inf t t' v) else None)
        \<ge> SPECT (inf (\<lambda>v. if Q v then Some (t v) else None) (\<lambda>v. if Q' v then Some (t' v) else None))"
    by(auto intro!: ext simp add:  le_fun_def) 

  from assms show ?thesis
    unfolding  Sepreftime.SPEC_def apply -
    apply(rule order.trans[OF _ t])
    apply(rule grr) apply simp apply simp done
qed

lemma einb_SPEC: "A \<le> SPEC \<Phi> \<Longrightarrow> einb A \<le> Sepreftime.SPEC \<Phi> (\<lambda>_. \<infinity>)"
  apply(cases A) apply simp
  unfolding Sepreftime.SPEC_def by (auto simp: le_fun_def )

lemma einb_SPEC': "einb A  \<le> Sepreftime.SPEC \<Phi> t
        \<Longrightarrow> A \<le> SPEC \<Phi>"
  unfolding Sepreftime.SPEC_def 
  apply(cases A) apply simp  by (auto simp: le_fun_def split: if_splits )

lemma "einb A  \<le> Sepreftime.SPEC \<Phi> (\<lambda>_. \<infinity>)
        \<longleftrightarrow> A \<le> SPEC \<Phi>"
  using einb_SPEC einb_SPEC' by auto


lemma inf_infinity: "(inf (\<lambda>_. \<infinity>::enat) t) = t" by(auto simp: inf_enat_def )

lemma assumes A: "A \<le> SPEC \<Phi>" 
  and T: "einb A \<le> Sepreftime.SPEC (\<lambda>_. True) t"
shows 
          "einb A \<le> Sepreftime.SPEC \<Phi> t"
  using  join[OF A[THEN einb_SPEC] T] by (simp add: inf_infinity)




end