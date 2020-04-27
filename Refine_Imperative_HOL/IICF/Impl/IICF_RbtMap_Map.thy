section \<open>Implementation of Maps by Red Black Trees\<close>
theory IICF_RbtMap_Map
  imports  "Imperative_HOL_Time.IHT_Red_Black_Tree" "../Intf/IICF_Map"
begin

  hide_const(open) R B

(* inspired by Separation_Logic_Imperative_HOL/Examples/Array_Map_Impl *)

definition rbt_map_map_assn where [rewrite_ent]:
  "rbt_map_map_assn MM p = (\<exists>\<^sub>AM. rbt_map_assn M p * \<up>(MM = meval M))"

subsubsection "empty map init via rbtree"
 
definition "map_empty = tree_empty"

declare [[print_trace]] 
setup \<open>fold del_prfstep_thm @{thms rbt_map_assn_def}\<close>

lemma meval_empty_map[rewrite]: "meval empty_map = Map.empty" unfolding empty_map_def by auto

setup \<open>add_rewrite_rule @{thm meval.simps}\<close>
theorem map_empty_rule [hoare_triple]:
  "<$1> map_empty <rbt_map_map_assn (Map.empty)>"
  unfolding map_empty_def by auto2

lemma mop_map_empty_rule[sepref_fr_rules]:
  "1 \<le> n () \<Longrightarrow> (uncurry0 map_empty, uncurry0 (PR_CONST (mop_map_empty n))) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a rbt_map_map_assn"
  apply sepref_to_hoare
  unfolding mop_map_empty_def autoref_tag_defs
  apply (rule extract_cost_otherway'[OF _ map_empty_rule  ])
  by (sep_auto simp: emb'_def)+ 

subsubsection "update map via rbtree insert"

definition "map_update p k x = rbt_insert k x p"

lemma keys_of_dom_meval: "keys_of M = dom (meval M)"
  unfolding keys_of_def by auto

abbreviation "sizeM1' m \<equiv> 1 + card (dom m)" 

lemma sizeM1'_sizeM1[rewrite]: "sizeM1' (meval M) = sizeM1 M"
  by(simp add: keys_of_dom_meval   sizeM1_def)

lemma meval_update[rewrite]: "meval ( M { k \<rightarrow> v }) = (meval M)(k \<mapsto> v)"
   by (auto simp: update_map_def)
  
theorem map_update_rule [hoare_triple]:
  "<rbt_map_map_assn M m * $ (rbt_insert_logN (sizeM1' M))>
           map_update m k v 
   <rbt_map_map_assn ( M( k \<mapsto> v ))>\<^sub>t"
  unfolding map_update_def
  by auto2


lemma mop_set_insert_rule[sepref_fr_rules]: "(uncurry2 map_update, uncurry2 (PR_CONST (mop_map_update t)))
  \<in> [\<lambda>((a, b), x). rbt_insert_logN (sizeM1' a) \<le> t ((a, b), x)]\<^sub>a rbt_map_map_assn\<^sup>d *\<^sub>a id_assn\<^sup>k *\<^sub>a id_assn\<^sup>k \<rightarrow> rbt_map_map_assn"
  apply sepref_to_hoare
  unfolding mop_map_update_def autoref_tag_defs
  apply (rule extract_cost_otherway'[OF _ map_update_rule  ])
    by (auto simp: emb'_def | solve_entails; auto)+ 

subsubsection "dom_member map via rbtree search"

definition "map_dom_member m k = do {
                  v \<leftarrow> rbt_search k m;
                  return (v\<noteq>None) }"

lemma M[rewrite]: "M\<langle>x\<rangle>\<noteq>None \<longleftrightarrow> x:dom (meval M)"
  unfolding keys_of_iff[symmetric] keys_of_dom_meval by simp
 
theorem map_dom_member_rule [hoare_triple]:
  "<rbt_map_map_assn M m * $ (rbt_search_time_logN (sizeM1' M)+1)>
           map_dom_member m x  
   <\<lambda>r. rbt_map_map_assn M m * \<up>(r\<longleftrightarrow>x\<in>dom M)>\<^sub>t"
  unfolding map_dom_member_def
  by auto2

lemma mop_mem_set_rule[sepref_fr_rules]:
  "(uncurry map_dom_member, uncurry (PR_CONST (mop_map_dom_member t)))
   \<in> [\<lambda>(a, b). rbt_search_time_logN (sizeM1' a) + 1 \<le> t (a, b)]\<^sub>a rbt_map_map_assn\<^sup>k *\<^sub>a id_assn\<^sup>k \<rightarrow> bool_assn"
  apply sepref_to_hoare
  unfolding mop_map_dom_member_def autoref_tag_defs 
  apply (rule extract_cost_otherway'[OF _ map_dom_member_rule  ])
  by (auto simp: emb'_def | solve_entails; auto)+ 

subsubsection "lookup map via rbtree search"

definition "map_lookup m k = do {
                  v \<leftarrow> rbt_search k m;
                  return (the v) }"

theorem map_lookup_rule [hoare_triple]:
  "x\<in>dom M \<Longrightarrow> <rbt_map_map_assn M m * $ (rbt_search_time_logN (sizeM1' M)+1)>
           map_lookup m x  
   <\<lambda>r. rbt_map_map_assn M m * \<up>(r=the (M x))>\<^sub>t"
  unfolding map_lookup_def  rbt_map_map_assn_def  
  by (sep_auto simp del: One_nat_def heap: rbt_search simp: sizeM1'_sizeM1 zero_time)  
 
lemma mop_map_lookup_rule[sepref_fr_rules]:
  "(uncurry map_lookup, uncurry (PR_CONST (mop_map_lookup t)))
     \<in> [\<lambda>(a, b). rbt_search_time_logN (sizeM1' a) + 1 \<le> t (a, b)]\<^sub>a rbt_map_map_assn\<^sup>k *\<^sub>a id_assn\<^sup>k \<rightarrow> id_assn"
  apply sepref_to_hoare 
  unfolding mop_map_lookup_def autoref_tag_defs  
  apply(rule hnr_ASSERT)
  apply(rule extract_cost_otherway'[OF _ map_lookup_rule   ])
  by sep_auto+ 
   



end