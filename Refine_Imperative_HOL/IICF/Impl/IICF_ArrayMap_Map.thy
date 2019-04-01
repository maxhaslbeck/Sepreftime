theory IICF_ArrayMap_Map
  imports "../Intf/IICF_Map" "SepLogicTime_RBTreeBasic.RBTree_Impl"
begin

(* inspired by Separation_Logic_Imperative_HOL/Examples/Array_Map_Impl *)

  subsection "Array Map"

  type_synonym 'v array_map = "'v option array"

  definition "iam_of_list l \<equiv> (\<lambda>i. if i<length l then l!i else None)"

  lemma finite_dom_iam_of_list: "finite (dom (iam_of_list l))"
    by(auto intro: subset_eq_atLeast0_lessThan_finite
          simp: iam_of_list_def domIff split: if_splits)


  definition is_liam   where
    "is_liam s m a \<equiv> \<exists>\<^sub>Al f. snd a\<mapsto>\<^sub>rf * fst a\<mapsto>\<^sub>al * \<up>(length l=s \<and> card (dom m) = f \<and> m=iam_of_list l)"


  definition new_liam :: "nat \<Rightarrow> (('a::{heap}) array_map \<times> 'b::{heap,zero} ref) Heap"  where
    "new_liam n = do { a \<leftarrow> Array.new n None; s\<leftarrow>Ref.ref 0; return (a,s) } "

lemma return_rule':
  "<$1> return x <\<lambda>r. \<up>(r = x)>" by auto2


schematic_goal "\<And>x xa. x \<mapsto>\<^sub>a replicate n None * xa \<mapsto>\<^sub>r 0 * $0\<Longrightarrow>\<^sub>A xa \<mapsto>\<^sub>r 0 * x \<mapsto>\<^sub>a ?f51 x xa  * $0"
  apply solve_entails oops
 
lemma new_liam_rule: "<$(n+3)> new_liam n <is_liam n (Map.empty)>" unfolding new_liam_def is_liam_def
    apply(sep_auto heap: ref_rule return_rule' )
    prefer 3 unfolding zero_time apply solve_entails by (auto simp: iam_of_list_def) 

lemma mop_map_empty_rule:
  "s+3\<le>t \<Longrightarrow> hn_refine (emp) (new_liam s) emp (is_liam s) (PR_CONST (mop_map_empty t))"
  unfolding autoref_tag_defs mop_map_empty_def  
  apply (rule extract_cost_otherway[OF _ new_liam_rule, where Cost_lb="s+3" and F=emp])
    apply solve_entails+
  by auto 

thm mop_map_empty_rule[to_hfref]

definition "mop_map_empty_fs s t = SPECT [ Map.empty \<mapsto> t]"

context
  fixes s::nat and t ::  " nat"
begin
  sepref_register "  (mop_map_empty_fs s t )" 
  print_theorems 
end

  lemma  mop_map_empty_fs: "tt \<le> lst (SPECT [ Map.empty \<mapsto> t  ])  Q
        \<Longrightarrow> tt \<le> lst (mop_map_empty_fs s t ) Q" unfolding mop_map_empty_fs_def by simp


  definition "mop_map_empty_fixed_length s = mop_map_empty "
  context fixes s :: nat begin
      sepref_register " (mop_map_empty_fixed_length s)"
  print_theorems 

  (*    lemma [def_pat_rules]: "mop_map_empty_fixed_length$s \<equiv> UNPROTECT (mop_map_empty_fixed_length s)"
      by simp *)
  end

lemma mop_map_empty_add_mn: "mop_map_empty = mop_map_empty_fs s"  by(auto simp: mop_map_empty_def mop_map_empty_fs_def)

lemma mop_map_empty_rule'[sepref_fr_rules]:
  "s+3\<le>n \<Longrightarrow> hn_refine (emp) (new_liam s) emp (is_liam s) (PR_CONST (mop_map_empty_fs s n))"
  unfolding mop_map_empty_fs_def apply(rule mop_map_empty_rule[unfolded mop_map_empty_def]) by simp

term RECT
thm sep_heap_rules
thm sep_decon_rules

definition update_liam where
    "update_liam m k v = do {
          ov \<leftarrow> Array.nth (fst m) k;
          a \<leftarrow> Array.upd k (Some v) (fst m);
          (if ov = None then do {
              s \<leftarrow> Ref.lookup (snd m);
              Ref.update (snd m) (s+1);
              return (a,snd m)
            } else return (a, snd m))
        }
      "


 

thm return_rule
thm return_rule
lemma zz: "xs!i = n \<Longrightarrow> xs[i:=n] = xs" by auto

lemma "<$2> if c=0 then return d else return 0 <\<lambda>r. \<up>(r = 0)>\<^sub>t"
  apply(sep_auto) oops

lemma knotin_dom_iam_of_listI: "l ! k = None \<Longrightarrow> k \<notin> dom (iam_of_list l)"
  by(auto simp: iam_of_list_def split: if_splits)

lemma kin_dom_iam_of_listI: "k < length l \<Longrightarrow> l ! k = Some y \<Longrightarrow>  k \<in> dom (iam_of_list l) "
  by(auto simp: iam_of_list_def)

lemma iam_of_list_update: "k < length l \<Longrightarrow> iam_of_list (l[k := Some v]) = iam_of_list l(k \<mapsto> v)"   
  by (auto simp: iam_of_list_def split: if_splits)
 

lemma update_liam_rule: "k<n \<Longrightarrow> <is_liam n M m * $6> update_liam m k v <\<lambda>r. is_liam n (M(k:=Some v)) r >\<^sub>t"
  unfolding update_liam_def is_liam_def
  apply(sep_auto heap: nth_rule lookup_rule update_rule return_rule')
    apply(auto simp:   zz  card_insert finite_dom_iam_of_list
              set_minus_singleton_eq knotin_dom_iam_of_listI iam_of_list_update )
  apply(sep_auto heap: return_rule')    
   apply(auto intro!: card_Suc_Diff1   simp:    iam_of_list_update finite_dom_iam_of_list )
  by(auto simp: iam_of_list_def) 


lemma mop_set_insert_rule[sepref_fr_rules]:
  "(uncurry2 update_liam, uncurry2 (PR_CONST (mop_map_update t)))
     \<in> [\<lambda>((a, b), x). 6 \<le> t a \<and> b < mn]\<^sub>a (is_liam mn)\<^sup>d *\<^sub>a nat_assn\<^sup>k *\<^sub>a id_assn\<^sup>k \<rightarrow> is_liam mn"
  apply sepref_to_hoare 
  unfolding mop_map_update_def autoref_tag_defs
  apply (rule extract_cost_otherway'[OF _  update_liam_rule ])
  by (auto simp: emb'_def | solve_entails; auto)+  


definition dom_member_liam where
    "dom_member_liam m k = do { f \<leftarrow> Array.nth (fst m) k; return (f \<noteq> None) }"


lemma dom_member_liam_rule: "k<n  \<Longrightarrow> <is_liam n M m * $2> dom_member_liam m k <\<lambda>r. is_liam n M m * \<up>(r\<longleftrightarrow>k\<in>dom M)  >\<^sub>t"
  unfolding dom_member_liam_def is_liam_def
  apply(sep_auto heap: nth_rule return_rule' )
  by(auto simp: iam_of_list_def)


lemma mop_mem_set_rule[sepref_fr_rules]:
  "2 \<le> t M \<Longrightarrow> x < n \<Longrightarrow>
    hn_refine (hn_val Id x x' * hn_ctxt (is_liam n) M p)
     (dom_member_liam p x')
     (hn_ctxt (pure Id) x x' * hn_ctxt (is_liam n) M p) id_assn ( PR_CONST (mop_map_dom_member t) $ M $ x)"
  apply sepref_to_hoare 
  unfolding autoref_tag_defs mop_map_dom_member_def
  apply (rule extract_cost_otherway'[OF _  dom_member_liam_rule])  
  by (auto simp: emb'_def | solve_entails; auto)+   







definition nth_liam where
    "nth_liam m k = do { f \<leftarrow> Array.nth (fst m) k; return (the f) }"

lemma nth_liam_rule: "k<n \<Longrightarrow> k \<in> dom M \<Longrightarrow> <is_liam n M m * $2> nth_liam m k <\<lambda>r. is_liam n M m * \<up>(r=the (M k))>\<^sub>t"
  unfolding nth_liam_def is_liam_def
  apply(sep_auto heap: nth_rule return_rule' )
  by(auto simp: iam_of_list_def)





lemma mop_map_lookup_rule[sepref_fr_rules]:
  "2 \<le> t M \<Longrightarrow> x < n \<Longrightarrow> 
    hn_refine (hn_val Id x x' * hn_ctxt (is_liam n) M p)
     (nth_liam p x')
     (hn_ctxt (pure Id) x x' * hn_ctxt (is_liam n) M p) id_assn ( PR_CONST (mop_map_lookup t) $ M $ x)"
  apply sepref_to_hoare
  unfolding autoref_tag_defs mop_map_lookup_def 
  apply(rule hnr_ASSERT) 
  apply (rule extract_cost_otherway'[OF _ nth_liam_rule] )
    by (auto | solve_entails; auto)+  








end