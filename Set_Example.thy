theory Set_Example
  imports Sepreftime   

begin



fun makeset where 
  "makeset (S,[]) = S" |
  "makeset (S,(x#xs)) = makeset (insert x S, xs)"

lemma makeset_set_aux: "makeset (S,xs) = S \<union> set xs"
  apply(induct xs arbitrary: S) by auto

corollary Z: "makeset ({},xs) = set xs" using makeset_set_aux by fast  

fun t_insert :: "nat \<Rightarrow> nat" where "t_insert n = 3*n"
fun t_makeset :: "nat \<Rightarrow> nat" where "t_makeset n = n * t_insert n"

definition "makeset_SPEC xs = SPECT [set xs \<mapsto> t_makeset (length xs)]"


definition "makeset_impl xs \<equiv> do {
      as \<leftarrow> RETURNT xs;
      S \<leftarrow> RETURNT {};
      s \<leftarrow> RETURNT (S,xs);
      r \<leftarrow> whileT (\<lambda>(S,as). as \<noteq> [])
        (\<lambda>(S,as). do {
               (*   ASSERT (as\<noteq>[]);
                  ASSERT (length as \<le> length xs);*)
                  x \<leftarrow> RETURNT (hd as);
                  as' \<leftarrow> RETURNT (tl as);
                  S' \<leftarrow> REST [insert x S \<mapsto> t_insert (length xs)];
                  RETURNT (S',as')
          } ) s;
      RETURNT (fst r)
    }"

thm whileT_rule'''
(*
lemma ASSERT_bindT: "ASSERT B \<bind> f = SPECT M \<longleftrightarrow> (B \<and> f () = SPECT M)"
  unfolding ASSERT_def iASSERT_def by simp

*)

lemma k: "y\<noteq>[] \<Longrightarrow> makeset (insert (hd y) x, tl y) = makeset (x, y)"
  apply (cases y) by auto

lemma "makeset_impl xs \<le> makeset_SPEC xs"
  unfolding makeset_SPEC_def makeset_impl_def apply simp

  apply(rule Refinement_by_T)
  apply (simp only: T_bindT)
  apply(simp only: T_RETURNT)
  apply(rule T_conseq4)
   apply(rule whileT_rule'''[where I="\<lambda>s. if makeset s = makeset ({},xs) then Some (length (snd s) * t_insert (length xs) ) else None" ])
  apply simp 
  subgoal (* progress *)
    apply(auto split: prod.splits)
    apply(auto simp add: ASSERT_bindT)
    sorry
  subgoal (* IS *)
    apply (auto split: if_splits)
  apply (simp only: T_bindT)
  apply(simp only: T_RETURNT)
    apply(simp only: T_REST)
    apply(subst k) apply simp apply simp
    apply(auto simp: mm3_def mm2_def) 
    by (simp add: left_diff_distrib')
   apply simp
  (* post condition *)
  apply (auto   split: if_splits)
  unfolding Z apply simp apply simp 
  unfolding mm3_def by simp


end