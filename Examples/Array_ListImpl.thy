theory Array_ListImpl
imports List_Interface
begin

section "Implement the List Interface with an array"

definition "array_assn xs p = p \<mapsto>\<^sub>a xs"

lemmas [safe_constraint_rules] = CN_FALSEI[of is_pure "array_assn" for A]

lemma mop_lookup_list_as_array_rule[sepref_fr_rules]:
  "1 \<le> n \<Longrightarrow> x < length xs \<Longrightarrow>
    hn_refine (hn_ctxt array_assn xs p * hn_val Id x x')
     (Array.nth p (x'::nat))
     (hn_ctxt array_assn xs p * hn_ctxt (pure Id) x x') id_assn ( PR_CONST (mop_lookup_list n) $  xs $ x)"
  unfolding autoref_tag_defs mop_lookup_list_def
  apply (rule extract_cost_otherway[OF _  nth_rule, where F="nat_assn x x'"]) unfolding mult.assoc
  unfolding hn_ctxt_def array_assn_def
      apply(rule match_first) apply rotatel apply(rule match_first) apply (simp add: pure_def)  
   apply(rule match_first) apply (simp add: pure_def)   apply safe 
    apply(rule inst_ex_assn[where x="xs ! x"]) apply simp apply simp  done


thm mop_lookup_list_as_array_rule[to_hfref]


end