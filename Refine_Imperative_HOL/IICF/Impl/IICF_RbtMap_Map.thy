theory IICF_RbtMap_Map
  imports  "SepLogicTime_RBTreeBasic.RBTree_Impl" "../Intf/IICF_Map"
begin

(* inspired by Separation_Logic_Imperative_HOL/Examples/Array_Map_Impl *)
 
  
thm rbt_delete_rule

term Map.empty
term rbt_map_assn
definition rbt_map_map_assn where [rewrite_ent]: "rbt_map_map_assn MM p =
        (\<exists>\<^sub>AM. rbt_map_assn M p * \<up>(MM = meval M))"

subsubsection "empty map init via rbtree"
 

definition "map_empty = tree_empty"

declare [[print_trace]] 
setup {* fold del_prfstep_thm @{thms rbt_map_assn_def} *}

lemma meval_empty_map[rewrite]: "meval empty_map = Map.empty" unfolding empty_map_def by auto

setup {* add_rewrite_rule @{thm meval.simps} *}
theorem map_empty_rule [hoare_triple]:
  "<$1> map_empty <rbt_map_map_assn (Map.empty)>"
  unfolding map_empty_def by auto2

lemma mop_map_empty_rule[sepref_fr_rules]:
  "1\<le>n \<Longrightarrow> hn_refine (emp) map_empty emp rbt_map_map_assn (PR_CONST (mop_map_empty n))"

  unfolding autoref_tag_defs mop_map_empty_def  
  apply (rule extract_cost_otherway[OF _ map_empty_rule, where Cost_lb=1 and F=emp])
  apply simp  
  subgoal 
    apply(rule ent_true_drop(2))
    unfolding rbt_map_map_assn_def 
    apply simp apply(rule ent_ex_preI) subgoal for M
  apply(rule ent_ex_postI[where x="Map.empty"])
      apply(rule ent_ex_postI[where x=M]) by simp
    done       
  by (auto intro: entails_triv simp: )

subsubsection "update map via rbtree insert"


thm rbt_insert_rule

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



lemma mop_set_insert_rule[sepref_fr_rules]:
  "rbt_insert_logN (sizeM1' M) \<le> t M \<Longrightarrow> 
      hn_refine (hn_val Id k k' * hn_val Id x x' * hn_ctxt rbt_map_map_assn M p)
       (map_update p k' x')
       (hn_val Id k k'* hn_val Id x x' * hn_invalid rbt_map_map_assn M p) rbt_map_map_assn ( PR_CONST (mop_map_update t) $ M $ k $ x)"

  unfolding mop_map_update_def autoref_tag_defs
  apply (rule extract_cost_otherway[OF _  map_update_rule, where F="hn_val Id k k' * hn_val Id x x' * hn_invalid rbt_map_map_assn M p" ])
  unfolding mult.assoc
    apply(rotatel)  apply(rotatel)
    apply rotater  apply rotater  apply rotater apply rotater   apply taker apply(rule isolate_first)
  apply (simp add: gr_def hn_ctxt_def)  apply(rule invalidate_clone)
  unfolding hn_ctxt_def
    apply(rule match_first)  apply (rule entails_triv)

   apply rotatel apply rotatel apply takel apply swapl apply takel
                apply taker   apply swapr apply taker 
   apply(rule isolate_first) 
  unfolding gr_def apply(simp only: ex_distrib_star' pure_def)
    apply(rule inst_ex_assn) apply simp apply safe prefer 2
     apply(rule entails_triv) 
  by (auto) 



subsubsection "dom_member map via rbtree search"


thm rbt_search

definition "map_dom_member m k = do {
                  v \<leftarrow> rbt_search k m;
                  return (v\<noteq>None) }"

lemma M[rewrite]: "M\<langle>x\<rangle>\<noteq>None \<longleftrightarrow> x:dom (meval M)"
  unfolding keys_of_iff[symmetric] keys_of_dom_meval by simp


thm return_rule
thm SepAuto.return_rule
theorem map_dom_member_rule [hoare_triple]:
  "<rbt_map_map_assn M m * $ (rbt_search_time_logN (sizeM1' M)+1)>
           map_dom_member m x  
   <\<lambda>r. rbt_map_map_assn M m * \<up>(r\<longleftrightarrow>x\<in>dom M)>\<^sub>t"
  unfolding map_dom_member_def
  by auto2



lemma mop_mem_set_rule[sepref_fr_rules]:
  "rbt_search_time_logN (sizeM1' M) + 1 \<le> t M \<Longrightarrow>
    hn_refine (hn_val Id x x' * hn_ctxt rbt_map_map_assn M p)
     (map_dom_member p x')
     (hn_ctxt (pure Id) x x' * hn_ctxt rbt_map_map_assn M p) id_assn ( PR_CONST (mop_map_dom_member t) $ M $ x)"

  unfolding autoref_tag_defs mop_map_dom_member_def
  apply (rule extract_cost_otherway[OF _  map_dom_member_rule]) unfolding mult.assoc
  unfolding hn_ctxt_def
    apply rotatel apply(rule match_first) apply(rule match_first)       
   apply (rule entails_triv)
  apply rotater
   apply(rule match_first) apply (simp add: pure_def)   apply safe
    apply(rule inst_ex_assn[where x="x \<in> dom M"])  by (auto simp: emb'_def) 


subsubsection "lookup map via rbtree search"


thm rbt_search

definition "map_lookup m k = do {
                  v \<leftarrow> rbt_search k m;
                  return (the v) }"
 

lemma s[resolve]: "x \<in> dom M \<Longrightarrow> M = meval Ma \<Longrightarrow>  v = Ma\<langle>x\<rangle> \<Longrightarrow> xa = the v \<Longrightarrow> xa =
                     the (M x)"  
  by simp

thm return_rule
thm SepAuto.return_rule
theorem map_lookup_rule [hoare_triple]:
  "x\<in>dom M \<Longrightarrow> <rbt_map_map_assn M m * $ (rbt_search_time_logN (sizeM1' M)+1)>
           map_lookup m x  
   <\<lambda>r. rbt_map_map_assn M m * \<up>(r=the (M x))>\<^sub>t"
  unfolding map_dom_member_def
  apply auto2  sorry

theorem map_lookup_rule [hoare_triple]:
  "x\<in>dom M \<Longrightarrow> <rbt_map_map_assn M m * $ (rbt_search_time_logN (sizeM1' M)+1)>
           map_lookup m x  
   <\<lambda>r. rbt_map_map_assn M m * \<up>(r=the (M x))>\<^sub>t"
  unfolding map_lookup_def  rbt_map_map_assn_def 
  apply(rule bind_rule) 
   apply(rule pre_rule[OF _ frame_rule[OF rbt_search]] )
  apply(rule match_first)
  apply(rule frame_rule[OF)
  unfolding map_dom_member_def
  apply auto2  oops




lemma mop_map_lookup_rule[sepref_fr_rules]:
  "rbt_search_time_logN (sizeM1' M) + 1 \<le> t M \<Longrightarrow>
    hn_refine (hn_val Id x x' * hn_ctxt rbt_map_map_assn M p)
     (map_lookup p x')
     (hn_ctxt (pure Id) x x' * hn_ctxt rbt_map_map_assn M p) id_assn ( PR_CONST (mop_map_lookup t) $ M $ x)"

  unfolding autoref_tag_defs mop_map_lookup_def 
  apply(rule hnr_ASSERT) apply(rule hn_refine_preI)
  apply (rule extract_cost_otherway[OF _ map_lookup_rule] ) unfolding mult.assoc
  unfolding hn_ctxt_def
    apply rotatel apply(rule match_first) apply(rule match_first)       
     apply (rule entails_triv)
  subgoal by (simp add: pure_def )
  apply rotater
   apply(rule match_first) apply (simp add: pure_def)   apply safe
    apply(rule inst_ex_assn[where x="the (M x)"])  by (auto simp: emb'_def) 



end