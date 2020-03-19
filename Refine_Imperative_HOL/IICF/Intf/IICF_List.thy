section \<open>List Interface\<close>
theory IICF_List
imports 
  "../../Sepref"
  "List-Index.List_Index"
begin

lemma param_index[param]: 
  "\<lbrakk>single_valued A; single_valued (A\<inverse>)\<rbrakk> \<Longrightarrow> (index,index) \<in> \<langle>A\<rangle>list_rel \<rightarrow> A \<rightarrow> nat_rel"
  unfolding index_def[abs_def] find_index_def 
  apply (subgoal_tac "(((=), (=)) \<in> A \<rightarrow> A \<rightarrow> bool_rel)")
  apply parametricity
  by (simp add: pres_eq_iff_svb)


(* TODO: Move? *)
subsection \<open>Swap two elements of a list, by index\<close>

definition "swap l i j \<equiv> l[i := l!j, j:=l!i]"
lemma swap_nth[simp]: "\<lbrakk>i < length l; j<length l; k<length l\<rbrakk> \<Longrightarrow>
  swap l i j!k = (
    if k=i then l!j
    else if k=j then l!i
    else l!k
  )"
  unfolding swap_def
  by auto

lemma swap_set[simp]: "\<lbrakk> i < length l; j<length l \<rbrakk> \<Longrightarrow> set (swap l i j) = set l"  
  unfolding swap_def
  by auto

lemma swap_multiset[simp]: "\<lbrakk> i < length l; j<length l \<rbrakk> \<Longrightarrow> mset (swap l i j) = mset l"  
  unfolding swap_def
  by (auto simp: mset_swap)


lemma swap_length[simp]: "length (swap l i j) = length l"  
  unfolding swap_def
  by auto

lemma swap_same[simp]: "swap l i i = l"
  unfolding swap_def by auto

lemma distinct_swap[simp]: 
  "\<lbrakk>i<length l; j<length l\<rbrakk> \<Longrightarrow> distinct (swap l i j) = distinct l"
  unfolding swap_def
  by auto

lemma map_swap: "\<lbrakk>i<length l; j<length l\<rbrakk> 
  \<Longrightarrow> map f (swap l i j) = swap (map f l) i j"
  unfolding swap_def 
  by (auto simp add: map_update)

lemma swap_param[param]: "\<lbrakk> i<length l; j<length l; (l',l)\<in>\<langle>A\<rangle>list_rel; (i',i)\<in>nat_rel; (j',j)\<in>nat_rel\<rbrakk>
  \<Longrightarrow> (swap l' i' j', swap l i j)\<in>\<langle>A\<rangle>list_rel"
  unfolding swap_def
  by parametricity

lemma swap_param_fref: "(uncurry2 swap,uncurry2 swap) \<in> 
  [\<lambda>((l,i),j). i<length l \<and> j<length l]\<^sub>f (\<langle>A\<rangle>list_rel \<times>\<^sub>r nat_rel) \<times>\<^sub>r nat_rel \<rightarrow> \<langle>A\<rangle>list_rel"
  apply rule apply clarsimp
  unfolding swap_def
  apply parametricity
  by simp_all

lemma param_list_null[param]: "(List.null,List.null) \<in> \<langle>A\<rangle>list_rel \<rightarrow> bool_rel"
proof -
  have 1: "List.null = (\<lambda>[] \<Rightarrow> True | _ \<Rightarrow> False)" 
    apply (rule ext) subgoal for l by (cases l) (auto simp: List.null_def)
    done 
  show ?thesis unfolding 1 by parametricity
qed

subsection \<open>Operations\<close>

context
  fixes t ::  "'c list \<Rightarrow> nat"
begin

  definition "mop_append x xs = SPECT [ (x#xs) \<mapsto> t xs]"

  lemma progress_mop_append[progress_rules]: "t xs > 0 \<Longrightarrow> progress (mop_append x xs)"
    unfolding mop_append_def by (auto intro!: progress_rules simp add:   zero_enat_def) 

  lemma mop_append: "tt \<le> lst (SPECT [ (x#xs) \<mapsto> t xs]) Q \<Longrightarrow> tt
           \<le> lst (mop_append x xs) Q" unfolding mop_append_def by simp

  sepref_register "mop_append" 
end

 


context
  fixes n::"unit \<Rightarrow> nat"
begin
  definition "mop_empty_list = SPECT [ [] \<mapsto> enat (n ()) ]"

  sepref_register "mop_empty_list" 
end

context
  fixes t::"('a *'a list) \<Rightarrow> nat"
begin
  definition "mop_push_list  x xs = SPECT [ ( xs @ [x] ) \<mapsto> enat (t (x, xs)) ]"
  
  sepref_register "mop_push_list" 
end


context
  fixes t:: "'a list \<times> nat \<Rightarrow> nat"
begin
  definition "mop_lookup_list xs i = SPECT [ xs ! i \<mapsto> enat (t (xs,i)) ]"

  sepref_register "mop_lookup_list" 
end

end
