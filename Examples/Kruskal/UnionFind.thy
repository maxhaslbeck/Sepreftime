theory UnionFind
imports Main
    "Collections.Partial_Equivalence_Relation"
begin



section "firstpart of SeprefUF"

  type_synonym 'a per = "('a\<times>'a) set"


  definition "per_init D \<equiv> {(i,i) | i. i\<in>D}"
  definition [simp]: "per_compare R a b \<equiv> (a,b)\<in>R"

  definition per_init' :: "nat \<Rightarrow> nat per" where "per_init' n \<equiv> {(i,i) |i. i<n}"

  lemma per_init_of_nat_range: "per_init {i. i<N} = per_init' N"
    by (auto simp: per_init_def per_init'_def)

  lemma per_init_per[simp, intro!]:
    "part_equiv (per_init D)"
    unfolding per_init_def
    by (auto simp: part_equiv_def sym_def trans_def)

  lemma per_init_self: "(a,b)\<in>per_init D \<Longrightarrow> a=b"
    unfolding per_init_def by simp

  lemma per_union_impl: "(i,j)\<in>R \<Longrightarrow> (i,j)\<in>per_union R a b"
    by (auto simp: per_union_def)

  lemma per_union_related:
    "part_equiv R \<Longrightarrow> a\<in>Domain R \<Longrightarrow> b\<in>Domain  R \<Longrightarrow> (a,b)\<in>per_union R a b"
    unfolding per_union_def
    by (auto simp: part_equiv_refl)

  lemma part_equiv_refl':
    "part_equiv R \<Longrightarrow> x\<in>Domain R \<Longrightarrow> (x,x)\<in>R"
    using part_equiv_refl[of R x] by blast


  definition per_supset_rel :: "('a per \<times> 'a per) set" where
    "per_supset_rel
      \<equiv> {(p1,p2). p1 \<inter> Domain p2 \<times> Domain p2 = p2 \<and> p1 - (Domain p2 \<times> Domain p2) \<subseteq> Id}"

  lemma per_supset_rel_dom: "(p1, p2) \<in> per_supset_rel \<Longrightarrow> Domain p1 \<supseteq> Domain p2"
    by (auto simp: per_supset_rel_def)
  
  lemma per_supset_compare:
    "(p1, p2) \<in> per_supset_rel \<Longrightarrow> x1\<in>Domain p2 \<Longrightarrow> x2\<in>Domain p2 \<Longrightarrow> per_compare p1 x1 x2 \<longleftrightarrow> per_compare p2 x1 x2"
    by (auto simp: per_supset_rel_def)
  
  lemma per_supset_union: "(p1, p2) \<in> per_supset_rel \<Longrightarrow> x1\<in>Domain p2 \<Longrightarrow> x2\<in>Domain p2 \<Longrightarrow>
    (per_union p1 x1 x2, per_union p2 x1 x2) \<in> per_supset_rel"
    apply (clarsimp simp: per_supset_rel_def per_union_def Domain_unfold )
    apply (intro subsetI conjI)
    apply blast
    apply force
    done



end