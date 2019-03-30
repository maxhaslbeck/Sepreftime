theory OutputSensitive
  imports "../Sepreftime" "../RefineMonadicVCG"
"../Refine_Imperative_HOL/IICF/Impl/IICF_Array_ListN" 
begin

definition "divide_SPEC n d = REST [ (n div d, n mod d) \<mapsto> n div d ]"

definition ddivide :: "nat \<Rightarrow> nat \<Rightarrow> (nat*nat) nrest" where
  "ddivide n d = RECT (\<lambda> df (q,r). if r \<ge> d then do {
          q' \<leftarrow> SPECT [q+1\<mapsto>1]; r'\<leftarrow> SPECT [r-d\<mapsto>1]; df (q',r') } else RETURNT (q,r)) (0,n)"


definition ddivide' :: "nat \<Rightarrow> nat \<Rightarrow> (nat*nat) nrest" where
  "ddivide' n d =  whileT (\<lambda>(q,r). r \<ge> d) (\<lambda>(q,r).  do {
          SPECT [ (q+1,r-d) \<mapsto> 1 ] }) (0,n) "
 


lemma "d>0 \<Longrightarrow> ddivide' n d \<le> divide_SPEC n d"
  unfolding  divide_SPEC_def ddivide'_def
  unfolding whileIET_def[symmetric, where I="\<lambda>(q,r). q*d+r=n"
        and E="\<lambda>(q,r). r div d"]  
  apply(rule T_specifies_I)
  apply (vcg' \<open>-\<close>)
  subgoal by simp
  subgoal for s a b   
    apply (auto simp: mm3_def)
    subgoal  
      using div_le_mono by auto   
    subgoal sorry
    done
  subgoal by auto
  done





end