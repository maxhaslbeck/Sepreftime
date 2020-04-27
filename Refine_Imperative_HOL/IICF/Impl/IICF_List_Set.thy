theory IICF_List_Set
  imports "Imperative_HOL_Time.IHT_Linked_List" 
      "../Intf/IICF_Set"  "NREST.RefineMonadicVCG"
begin
 

subsection "library for some set implementation via linked list"
 

definition set_init_t :: "nat" where "set_init_t = 1"

definition list_set_assn :: "_ set \<Rightarrow> _ os_list \<Rightarrow> assn"  where
  "list_set_assn S p =
        (\<exists>\<^sub>AL. os_list L p * \<up>(distinct L \<and> S = set L))"


subsubsection "empty set init"
term os_empty
thm os_empty_rule
definition "list_set_empty = os_empty" 

lemma list_set_empty_rule: "<$ 1> list_set_empty <list_set_assn {}>"
  unfolding list_set_assn_def list_set_empty_def
  by(sep_auto heap: os_empty_rule simp: zero_time)


lemma mop_set_empty_rule[sepref_fr_rules]:
  "(uncurry0 list_set_empty, uncurry0 (PR_CONST (mop_set_empty t)))
     \<in> [\<lambda>_. 1 \<le> t () ]\<^sub>a unit_assn\<^sup>k \<rightarrow> list_set_assn"
  apply sepref_to_hoare
  unfolding autoref_tag_defs mop_set_empty_def 
  apply (rule extract_cost_otherway'[OF _ list_set_empty_rule])
    apply (  solve_entails )
   apply (  solve_entails )  by (auto simp: ran_emb')   


subsubsection "pick element"

term os_pop
thm os_pop_rule
definition "list_set_pick_extract = os_pop" 
 
lemma Case_rule[sep_decon_rules]: "(c = None \<Longrightarrow> <P> f <Q>) \<Longrightarrow> (\<And>b. c = Some b \<Longrightarrow> <P> g b <Q>) \<Longrightarrow> <P> case c of None \<Rightarrow> f | Some b \<Rightarrow> g b <Q>"
  by (auto split: option.splits) 

lemma raise_rule: "P \<Longrightarrow>\<^sub>A false \<Longrightarrow> <P> raise msg <Q>"
  by (simp add: hoare_triple_def)

lemma return_rule':
  "<$1> return x <\<lambda>r. \<up>(r = x)>" by auto2 

lemma list_set_pick_extract_rule :
  "S \<noteq> {} \<Longrightarrow> <list_set_assn S p * $2>
   list_set_pick_extract p
   <\<lambda>(x,r'). list_set_assn (S-{x}) r' * \<up>(x \<in> S)>\<^sub>t"
  unfolding list_set_assn_def list_set_pick_extract_def os_pop_def
  apply(sep_auto heap: raise_rule) 
  subgoal  
    by (metis hd_Cons_tl mod_false' os_list.simps(3))
  subgoal for L apply (cases L) apply simp by simp
  subgoal for L pa
    apply (cases L) apply simp
    by(sep_auto heap: ref_rule return_rule' lookup_rule) 
  done
 

lemma mop_set_pick_extract_rule[sepref_fr_rules]:
  "(list_set_pick_extract, PR_CONST (mop_set_pick_extract t))
     \<in> [\<lambda>x. 2 \<le> t x]\<^sub>a list_set_assn\<^sup>d \<rightarrow> id_assn \<times>\<^sub>a list_set_assn"
  apply sepref_to_hoare
  unfolding autoref_tag_defs mop_set_pick_extract_def
  apply(rule hnr_ASSERT)
  apply (rule extract_cost_otherway'[OF _ list_set_pick_extract_rule])
  apply (  solve_entails ) apply simp
  apply (case_tac r) 
   apply (  solve_entails )  defer apply(subst prod_assn_pair_conv) 
  apply (  solve_entails ) by (auto simp: ran_emb')   



subsubsection "insert new element"

term os_prepend

thm os_prepend_rule

definition "list_set_insert k b = os_prepend k b"

lemma list_set_insert_rule:
  "x\<notin>S \<Longrightarrow> <list_set_assn S n * $2> list_set_insert x n <list_set_assn (insert x S)>" 
  unfolding list_set_insert_def list_set_assn_def
  by (sep_auto heap: os_prepend_rule) 
 
lemma mop_set_insert_rule[sepref_fr_rules]:
  "(uncurry list_set_insert, uncurry (PR_CONST (mop_set_insert t)))
     \<in> [\<lambda>(a, b). 2 \<le> t (a, b) \<and> a\<notin>b]\<^sub>a id_assn\<^sup>k *\<^sub>a list_set_assn\<^sup>d \<rightarrow> list_set_assn"
  apply sepref_to_hoare
  unfolding autoref_tag_defs mop_set_insert_def
  apply (rule extract_cost_otherway'[OF _ list_set_insert_rule])
  by sep_auto+




subsubsection "test emptiness"

term os_is_empty
thm os_is_empty_rule
definition "list_set_isempty = os_is_empty" 

lemma list_set_isempty_rule:
  "<list_set_assn S p * $ 1> list_set_isempty p <\<lambda>r. list_set_assn S p * \<up> (r = (S = {}))>"
  unfolding list_set_isempty_def list_set_assn_def
  by(sep_auto heap: os_is_empty_rule simp: zero_time)

lemma mop_set_isempty_rule[sepref_fr_rules]:
    "(list_set_isempty, PR_CONST (mop_set_isempty t))
   \<in> [\<lambda>S. 1 \<le> t S]\<^sub>a list_set_assn\<^sup>k \<rightarrow> bool_assn"
  apply sepref_to_hoare
  unfolding autoref_tag_defs mop_set_isempty_def 
  apply (rule extract_cost_otherway'[OF _ list_set_isempty_rule])  
  apply solve_entails apply auto
  by solve_entails   
    
  
hide_type IHT_Linked_List.node 

end
