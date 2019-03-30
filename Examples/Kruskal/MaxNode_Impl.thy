theory MaxNode_Impl
  imports Union_Find_Time Kruskal_Impl "SepLogicTime_RBTreeBasic.MergeSort_Impl"
  "../Remdups"
begin  


datatype wrap = W (extr: "(nat \<times> int \<times> nat)")

instantiation wrap :: linorder
begin
fun less_eq_wrap  where "less_eq_wrap (W (a2,a,a3)) (W (b2,b,b3)) = (if a=b then (if a2=b2 then (if a3=b3 then True else a3<b3) else a2<b2) else a<b)"
fun less_wrap  where "less_wrap (W (a2,a,a3)) (W (b2,b,b3)) = (if a=b then (if a2=b2 then (if a3=b3 then False else a3<b3) else a2<b2) else a<b)"


instance  
  apply standard
  subgoal for x y apply(cases x; cases y) 
      subgoal for xa xaa apply(cases xa; cases xaa) by auto done
  subgoal for x   apply(cases x ) by auto 
  subgoal for x y z apply(cases x; cases y; cases z)  subgoal for xa xaa xb apply(cases xa; cases xaa; cases xb) by (auto split: if_splits) done
  subgoal for x y apply(cases x; cases y) by (auto split: if_splits) 
  subgoal for x y apply(cases x; cases y) by auto  
  done
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


thm destroy_rule remdups_rule

term remdups_impl

definition sortEdges'  :: "(nat \<times> int \<times> nat) list \<Rightarrow> ((nat \<times> int \<times> nat) list * nat) Heap"  where
  "sortEdges' l = do {
      da \<leftarrow> remdups_impl (map W l);
      a \<leftarrow> destroy da;
      merge_sort_impl a;
      mn \<leftarrow> maxn a; 
      sl \<leftarrow> Array.freeze a;
      return (map extr sl, mn)
    }"


definition sortEdges'_time :: "nat \<Rightarrow> nat" where
  "sortEdges'_time n = remdups_time n + 3 + merge_sort_time n + (n*2+2) +  (n+1) + 1"
 
lemma merge_sort_time_O[asym_bound]:
  " merge_sort_time \<in> \<Theta>(\<lambda>n. n * ln n)"
  using merge_sort_time_O by auto

lemma sortEdges'_time_bound[asym_bound]: "sortEdges'_time \<in> \<Theta>(\<lambda>n. n * ln n)"
  unfolding sortEdges'_time_def
  by(auto2)


definition sortEdges  :: "(nat \<times> int \<times> nat) list \<Rightarrow> ((nat \<times> int \<times> nat) list * nat) Heap"  where
  "sortEdges l = do {
      a \<leftarrow> Array.of_list (map W l);
      merge_sort_impl a;
      mn \<leftarrow> maxn a; 
      sl \<leftarrow> Array.freeze a;
      return (map extr sl, mn)
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


lemma sorted_wrap: "sorted_wrt Kruskal_Refine.edges_less_eq (map extr (sort l))"
proof -
  have "sorted (sort l)"   using sorted_sort by auto
  with sorted_sorted_wrt have A: "sorted_wrt (\<le>) (sort l)" by metis 

  have p: "\<And>x y. x \<le> y \<Longrightarrow>  Kruskal_Refine.edges_less_eq (extr x) (extr y) "
    subgoal for x y
      apply(cases x; cases y) apply (simp add: Kruskal_Refine.edges_less_eq_def)
      subgoal for xa xaa apply(cases xa; cases xaa) by (auto split: if_splits)
      done
    done

  show ?thesis
    apply(simp add: sorted_wrt_map)
    apply(rule sorted_wrt_mono_rel[OF _ A])
    using  p by blast
qed


lemma extrW: "x \<in> S \<Longrightarrow> x \<in> extr ` W ` S "
  unfolding extr_def  
  by (metis extr_def imageI wrap.sel)  

lemma extr_W_on_set: "extr ` W ` S = S"
  by (auto simp: extrW)

lemma freeze_sort_maprule:
  "<a \<mapsto>\<^sub>a sort (map f xs) * timeCredit_assn(1 + length xs)> Array.freeze a <\<lambda>r. a \<mapsto>\<^sub>a sort (map f xs) * \<up>(r = sort (map f xs))>" 
  using freeze_rule[where xs="sort (map f xs)"] by auto

lemma sortEdges_rule: "<timeCredit_assn(sortEdges_time (length l))> sortEdges l <\<lambda>(sl, mn). \<up>(sorted_wrt edges_less_eq sl)>\<^sub>t"
  unfolding sortEdges_def  sortEdges_time_def
  by(sep_auto heap: mergeSort_map_rule maxn_sort_maprule of_list_map_rule  freeze_sort_maprule simp: sorted_wrap )

lemma sortEdges_rule2: "<timeCredit_assn(sortEdges_time (length l))> sortEdges l <\<lambda>(sl, mn). \<up>(set sl = set l \<and> mn=max_node l \<and> sorted_wrt edges_less_eq sl)>\<^sub>t"
  unfolding sortEdges_def  sortEdges_time_def
  apply(sep_auto heap: mergeSort_map_rule maxn_sort_maprule of_list_map_rule  freeze_sort_maprule simp: extrW sorted_wrap )
  apply(simp add: max_node_def)
  using extr_W_on_set    
  by (metis (no_types, lifting) image_comp) 

thm remdups_rule
lemma remdup_map_rule:
  "< timeCredit_assn (remdups_time (length l))> 
          remdups_impl (map W l)
        <\<lambda>r. \<exists>\<^sub>Ara. da_assn id_assn ra r * \<up> (set (map W l) = set ra \<and> distinct ra)>\<^sub>t"
  using remdups_rule[where as="map W l"] by simp

 
lemma da_assn_id: "da_assn id_assn = dyn_array" 
  unfolding da_assn_def by simp   


thm atake_time_def

lemma atake_time_mono: "x\<le>y \<Longrightarrow> atake_time x \<le> atake_time y" by(auto simp: atake_time_def)
lemma adrop_time_mono: "x\<le>y \<Longrightarrow> adrop_time x \<le> adrop_time y" by(auto simp: adrop_time_def)
lemma mergeinto_time_mono: "x\<le>y \<Longrightarrow> mergeinto_time x \<le> mergeinto_time y" by(auto simp: mergeinto_time_def)

lemma merge_sort_time_mono: "x\<le>y \<Longrightarrow> merge_sort_time x \<le> merge_sort_time y"
proof(induct y arbitrary: x rule: less_induct)
  case (less y)
  then show ?case
  proof (cases "y\<le>1")
    case   True
    note t=this
    with less show ?thesis by simp   
  next
    case f: False
    then show ?thesis
    proof(cases "x\<le>1")
      case True
      with f show ?thesis by (simp add: atake_time_def)
    next
      case False 
      from False f less(2) show ?thesis apply (simp add:  )
        by(auto intro!: add_mono intro: atake_time_mono adrop_time_mono mergeinto_time_mono less(1)) 
    qed
  qed
qed 

lemma mergeSort_smaller_rule:   
  shows
  "length ra \<le>  ll \<Longrightarrow>
  <p \<mapsto>\<^sub>a ra * timeCredit_assn(merge_sort_time ll)>
   merge_sort_impl p
   <\<lambda>_. p \<mapsto>\<^sub>a sort ra>\<^sub>t"  
  apply(rule ht_cons_rule[where P'="p \<mapsto>\<^sub>a ra * timeCredit_assn (merge_sort_time (length ra)) * true"])
    apply(simp only: mult.assoc)
    apply(rule match_first)  apply(rule gc_time)
  apply(rule merge_sort_time_mono) apply simp
  defer  apply(rule fi_rule[where F=true]) apply(rule mergeSort_correct[where xs="ra"])
   apply sep_auto+
  done

lemma maxn_sort_smallerrule: "length xs \<le> S \<Longrightarrow> <p\<mapsto>\<^sub>axs * timeCredit_assn(S*2+2)> maxn p <\<lambda>r. p\<mapsto>\<^sub>axs *  \<up>(r=maxnode  (map extr xs))>\<^sub>t"
  apply(rule ht_cons_rule[where P'="p \<mapsto>\<^sub>a xs * timeCredit_assn (2*(length xs)+2) * true"])
    apply(simp only: mult.assoc)
    apply(rule match_first)  apply(rule gc_time)  apply simp
  defer  apply(rule fi_rule[where F=true]) apply(rule maxn_rule[where xs="xs"])
   apply sep_auto+
  done 

lemma freeze_smallerrule: "length xs \<le> S \<Longrightarrow> <a \<mapsto>\<^sub>a xs * timeCredit_assn(1 + S)> Array.freeze a <\<lambda>r. a \<mapsto>\<^sub>a xs * \<up>(r = xs)>\<^sub>t"
  apply(rule ht_cons_rule[where P'="a \<mapsto>\<^sub>a xs * timeCredit_assn (1+(length xs)) * true"])
    apply(simp only: mult.assoc)
    apply(rule match_first)  apply(rule gc_time)  apply simp
  defer  apply(rule fi_rule[where F=true]) apply(rule freeze_rule[where xs="xs"])
   apply sep_auto+
  done 
 

lemma distinct_sort: "distinct a \<Longrightarrow> distinct (sort a)"   
  by simp  

lemma sortEdges'_rule: "<timeCredit_assn(sortEdges'_time (length l))>
           sortEdges' l 
      <\<lambda>(sl, mn). \<up>(sorted_wrt edges_less_eq sl \<and> set l = set sl \<and> distinct sl \<and> max_node l = mn)>\<^sub>t"
  unfolding sortEdges'_def  sortEdges'_time_def
  apply(sep_auto heap: remdup_map_rule) 
   apply(rule fi_rule[where F="timeCredit_assn(7 + (3 * length l + ( merge_sort_time (length l))))", OF  ht_cons_rule[OF _ _ remdup_map_rule]])
     apply (rule ent_refl) apply (rule ent_refl)
  subgoal by (simp add: norm_assertion_simps dollarD)
  apply(simp add: da_assn_id)                               
  apply(sep_auto heap: destroy_rule remdup_map_rule mergeSort_map_rule maxn_sort_maprule of_list_map_rule  freeze_sort_maprule simp: sorted_wrap )
   apply(sep_auto heap: mergeSort_smaller_rule[where ll="length l"])
  subgoal  
    by (metis distinct_length_le length_map set_map)  
  apply(sep_auto heap: maxn_sort_smallerrule[where S="length l"])
  subgoal 
    by (metis distinct_length_le length_map set_map)  
  apply(sep_auto heap: freeze_smallerrule[where S="length l"])
  subgoal 
    by (metis distinct_length_le length_map set_map)  
  apply (sep_auto simp: sorted_wrap )
  subgoal 
    using extrW by blast 
  subgoal  
    using extr_W_on_set by blast   
  subgoal apply(simp add: distinct_map)  
    by (simp add: inj_onI wrap.expand)  
  subgoal unfolding max_node_def 
    using extr_W_on_set    
    by (metis (no_types, lifting) image_comp)   
  done 


lemma ll: "list_assn id_assn   = pure Id" 
  by (simp add: list_assn_pure_conv)  

interpretation sortMaxnode sortEdges' sortEdges'_time
  apply(unfold_locales)                       
  apply (auto simp add: hfref_def mop_sortEdges_def)
  subgoal for t c a
    apply(rule extract_cost_otherway'[OF _ sortEdges'_rule, where Cost_lb="sortEdges'_time (length c)"])
      apply sep_auto
    subgoal 
      apply (auto simp: list_assn_pure_conv   )
      apply(simp add: pure_def) apply sep_auto unfolding max_node_def by simp
    subgoal 
      apply (auto simp: list_assn_pure_conv   ) apply(simp only: ran_emb' pure_def) by auto 
    done
  done




end