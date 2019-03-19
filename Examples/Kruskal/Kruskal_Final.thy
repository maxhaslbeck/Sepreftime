theory Kruskal_Final
imports Union_Find_Time Kruskal_Impl "SepLogicTime_RBTreeBasic.MergeSort_Impl"
begin


datatype wrap = W (extr: "(nat \<times> int \<times> nat)")

instantiation wrap :: linorder
begin
fun less_eq_wrap  where "less_eq_wrap (W (a2,a,a3)) (W (b2,b,b3)) = lexordp (\<le>) [a,a2,a3] [b,b2,b3]"
fun less_wrap  where "less_wrap (W (a2,a,a3)) (W (b2,b,b3)) = lexordp (<) [a,a2,a3] [b,b2,b3]"


instance  
  apply standard
  subgoal for x y apply(cases x; cases y) 
      subgoal for xa xaa apply(cases xa; cases xaa) apply auto 
  subgoal for x   apply(cases x ) by auto 
  subgoal for x y z apply(cases x; cases y; cases z) by auto 
  subgoal for x y apply(cases x; cases y) apply auto 
    subgoal for x y apply(cases x; cases y) by auto  

    sorry
  done
  sorry
end


fun wrap_encode :: "wrap \<Rightarrow> nat" where
  "wrap_encode (W a) = to_nat a"

instance wrap :: heap
  apply (rule heap_class.intro)
  apply (rule countable_classI [of "wrap_encode"])
  apply (case_tac x, simp_all, case_tac y, simp_all)
  .. 


fun maxn' :: "wrap array \<Rightarrow> nat \<Rightarrow> nat Heap" where
  "maxn' p 0 = return 0"
|  "maxn' p (Suc n) = do {
       l \<leftarrow> Array.nth p n;
      (case l of W (a,w,b) \<Rightarrow> do { 
            mn \<leftarrow> maxn' p n;
            return (max mn (max a b))
        } )
    }"

abbreviation "maxnode L \<equiv> Max (insert 0 (set (map fst L) \<union> set (map (snd o snd) L)))"

lemma maxn'_rule: 
  "n\<le>length xs \<Longrightarrow> <p\<mapsto>\<^sub>axs * timeCredit_assn(n*2+1)> maxn' p n <\<lambda>r. p\<mapsto>\<^sub>axs *  \<up>(r=maxnode (take n (map extr xs)))>"
proof(induct n)
  case 0
  then show ?case by (sep_auto simp: zero_time) 
next
  case (Suc n)
  from Suc(2) show ?case 
    apply (sep_auto simp: zero_time)
  apply(auto split: wrap.splits)
    apply (sep_auto heap: Suc(1) simp: zero_time) 
    apply(simp add: take_Suc_conv_app_nth)
    apply(subst Max_insert[symmetric]) apply simp apply simp
    apply(subst max.commute)
    apply(subst max.assoc)
    apply(subst Max_insert[symmetric]) apply simp apply simp
    apply(subst Max_insert[symmetric]) apply simp apply simp
    apply(subst (2) insert_commute)
    apply(subst (1) insert_commute)
    apply(subst Max_insert) apply simp apply simp
    apply (simp del: Max_insert)
    apply(rule arg_cong[where f="Max"]) by auto 
qed

definition "maxn p = do { l \<leftarrow> Array.len p; maxn' p l }"

lemma maxn_rule: "<p\<mapsto>\<^sub>axs * timeCredit_assn(length xs*2+2)> maxn p <\<lambda>r. p\<mapsto>\<^sub>axs *  \<up>(r=maxnode  (map extr xs))>"
  unfolding maxn_def by(sep_auto heap: maxn'_rule length_rule simp: zero_time) 


definition sortEdges  :: "(nat \<times> int \<times> nat) list \<Rightarrow> ((nat \<times> int \<times> nat) list * nat) Heap"  where
  "sortEdges l = do {
      a \<leftarrow> Array.of_list (map W l);
      merge_sort_impl a;
      mn \<leftarrow> maxn a; 
      sl \<leftarrow> Array.freeze a;
      return (map extr sl, 0)
    }"

definition sortEdges_time :: "nat \<Rightarrow> nat" where
  "sortEdges_time n = (n+1) + merge_sort_time n + (n*2+2) +  (n+1) + 1"


lemma of_list_map_rule: "<timeCredit_assn (1 + length xs)>
    Array.of_list (map f xs) <\<lambda>r. r \<mapsto>\<^sub>a (map f xs)>"
  using of_list_rule[where xs="map f xs"]
  by auto

lemma mergeSort_map_rule:  
  "<p \<mapsto>\<^sub>a (map f l) * timeCredit_assn(merge_sort_time (length l))>
   merge_sort_impl p
   <\<lambda>_. p \<mapsto>\<^sub>a sort (map f l)>\<^sub>t"  
  using mergeSort_correct[where xs="(map f l)"] by auto

lemma maxn_sort_maprule: "<p\<mapsto>\<^sub>asort (map f xs) * timeCredit_assn(length xs*2+2)> maxn p <\<lambda>r. p\<mapsto>\<^sub>asort (map f xs) *  \<up>(r=maxnode  (map extr (sort (map f xs))))>"
  using maxn_rule[where xs="sort (map f xs)"] by auto


lemma freeze_sort_maprule:
  "<a \<mapsto>\<^sub>a sort (map f xs) * timeCredit_assn(1 + length xs)> Array.freeze a <\<lambda>r. a \<mapsto>\<^sub>a sort (map f xs) * \<up>(r = sort (map f xs))>" 
  using freeze_rule[where xs="sort (map f xs)"] by auto

lemma sortEdges_rule: "<timeCredit_assn(sortEdges_time (length l))> sortEdges l <\<lambda>(sl, mn). \<up>(sorted_wrt edges_less_eq sl)>\<^sub>t"
  unfolding sortEdges_def  sortEdges_time_def
  apply(sep_auto heap: mergeSort_map_rule maxn_sort_maprule of_list_map_rule  freeze_sort_maprule )
  sorry



interpretation sortMaxnode sortEdges sort_time'
  apply(unfold_locales)
  apply (auto simp add: hfref_def mop_sortEdges_def)
  subgoal for t c a
    apply(rule extract_cost_otherway'[OF _ sortEdges_rule, where Cost_lb="sortEdges_time (length c)"])
    apply sep_auto
     apply sep_auto
    sorry
  done




end