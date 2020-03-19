section "Implement the List Interface with an array"
theory IICF_Array_ListN
imports "../Intf/IICF_List"
begin


definition "array_assn xs p = p \<mapsto>\<^sub>a xs"

lemmas [safe_constraint_rules] = CN_FALSEI[of is_pure "array_assn" for A]

context 
  notes [intro!] = hfrefb_to_hoare_triple
  notes [simp] = pure_def hn_ctxt_def invalid_assn_def uncurry_t_def
                noparam_t_def oneparam_t_def
begin  

  lemma mop_list_lookup_rule_aux:
    "(uncurry Array_Time.nth, uncurry_t mop_lookup_list)
                      \<in> [\<lambda>(a, b). b < length a,\<lambda>_. 1]\<^sub>b array_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> id_assn"
    by (sep_auto simp: array_assn_def mop_lookup_list_def)

  lemmas mop_list_lookup_rule[sepref_fr_rules] = mop_list_lookup_rule_aux[hfb_to_hnr]

end

end