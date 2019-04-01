theory UnionFind_Impl
imports  "../../Refine_Imperative_HOL/Sepref" UnionFind  
begin

section "Union find Implementation"

subsection "MOP interface"

context
  fixes t ::  "nat \<Rightarrow> nat"
begin

  definition "mop_per_init n = SPECT [ per_init' n \<mapsto> enat (t n) ]"

  lemma progress_mop_per_init[progress_rules]: "t n > 0 \<Longrightarrow> progress (mop_per_init n)"
    unfolding mop_per_init_def by (auto intro!: progress_rules simp add:   zero_enat_def) 

  lemma mop_per_init: "tt \<le> lst (SPECT [ per_init' n \<mapsto> t n]) Q \<Longrightarrow> tt
           \<le> lst (mop_per_init n) Q" unfolding mop_per_init_def by simp

  sepref_register "mop_per_init" 
end

context
  fixes t ::  "('a \<times> 'a) set \<Rightarrow> nat"
begin

  definition "mop_per_compare R a b = SPECT [ per_compare R a b \<mapsto> enat (t R) ]"

  sepref_register "mop_per_compare" 
end

context
  fixes t ::  "('a \<times> 'a) set \<Rightarrow> nat"
begin

  definition "mop_per_union R a b = SPECT [ per_union R a b \<mapsto> enat (t R) ]"

  sepref_register "mop_per_union" 
end



subsection "Implementation Locale"


type_synonym uf = "nat array \<times> nat array"

locale UnionFind_Impl = 
  fixes is_uf :: "(nat\<times>nat) set \<Rightarrow> uf \<Rightarrow> assn"
      and uf_init :: "nat \<Rightarrow> uf Heap"
      and uf_init_time :: "nat \<Rightarrow> nat"
      and uf_cmp :: "uf \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool Heap"
      and uf_cmp_time :: "nat \<Rightarrow> nat"
      and uf_union :: "uf \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> uf Heap"
      and uf_union_time :: "nat \<Rightarrow> nat"
    assumes 
per_init'_sepref_rule[sepref_fr_rules]:  "\<And>t x' x. uf_init_time x' \<le> t x' \<Longrightarrow>
     hn_refine (hn_ctxt nat_assn x' x) (uf_init x)
         (hn_ctxt nat_assn x' x)  
             is_uf (PR_CONST (mop_per_init t) $  x' )" 

  and

per_compare_sepref_rule[sepref_fr_rules]:  "\<And>t R' R a' a b' b . uf_cmp_time (card (Domain R')) \<le> t R' \<Longrightarrow>
     hn_refine (hn_ctxt is_uf R' R * hn_ctxt nat_assn a' a * hn_ctxt nat_assn b' b) (uf_cmp R a b)
         (hn_ctxt is_uf R' R * hn_ctxt nat_assn a' a * hn_ctxt nat_assn b' b) 
             bool_assn (PR_CONST (mop_per_compare t) $  R' $ a' $ b' )" 

  and

per_union_sepref_rule[sepref_fr_rules]:  "\<And>t R' R a' a b' b . a' \<in> Domain R' \<Longrightarrow> b' \<in> Domain R'
  \<Longrightarrow> uf_union_time (card (Domain R')) \<le> t R' \<Longrightarrow> 
     hn_refine (hn_ctxt is_uf R' R * hn_ctxt nat_assn a' a * hn_ctxt nat_assn b' b) (uf_union R a b)
         (hn_invalid is_uf R' R * hn_ctxt nat_assn a' a * hn_ctxt nat_assn b' b) 
             is_uf (PR_CONST (mop_per_union t) $  R' $ a' $ b' )" 

begin


thm per_init'_sepref_rule[to_hfref]
thm per_compare_sepref_rule[to_hfref]
thm per_union_sepref_rule[to_hfref]


end



end