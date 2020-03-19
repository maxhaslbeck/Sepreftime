section \<open>Set Interface\<close>
theory IICF_Set
imports "../../Sepref"
begin

subsection \<open>Operations\<close>

context 
  notes [simp] = IS_LEFT_UNIQUE_def (* Argh, the set parametricity lemmas use single_valued (K\<inverse>) here. *)
begin

context
  fixes t ::  "unit \<Rightarrow> nat"
begin
  definition "mop_set_empty = SPECT [ {} \<mapsto> enat (t ()) ]"

  lemma mop_set_empty: "tt \<le> lst (SPECT [ {} \<mapsto> (t ()) ]) Q \<Longrightarrow> tt
           \<le> lst (mop_set_empty) Q" unfolding mop_set_empty_def by simp

  sepref_register "mop_set_empty" 
end


context
  fixes t ::  "'c set \<Rightarrow> nat"
begin
  definition "mop_set_isempty S = SPECT [ S={} \<mapsto> t S ]"

  lemma  mop_set_isempty: "tt \<le> lst (SPECT [ S={} \<mapsto> t S ])  Q
        \<Longrightarrow> tt \<le> lst (mop_set_isempty S) Q" unfolding mop_set_isempty_def by simp
 
  sepref_register "mop_set_isempty" 
end


context
  fixes t ::  "'c set \<Rightarrow> nat"
begin
  definition "mop_set_pick S = do { ASSERT (S\<noteq>{}); SPECT (emb (\<lambda>x. x\<in>S) (t S)) }"

  lemma  mop_set_pick: "tt \<le> lst (SPECT (emb (\<lambda>x. x\<in>S) (t S)))  Q
        \<Longrightarrow> S \<noteq> {} \<Longrightarrow> tt \<le> lst (mop_set_pick S) Q" unfolding mop_set_pick_def by simp

  lemma progress_mop_set_pick[progress_rules]: "t S > 0 \<Longrightarrow> progress (mop_set_pick S)"
    unfolding mop_set_pick_def by (auto intro!: progress_rules simp add:   zero_enat_def) 

  sepref_register "mop_set_pick" 
end

context
  fixes t ::  "'c set \<Rightarrow> nat"
begin
  definition "mop_set_pick_extract S = do { ASSERT (S\<noteq>{}); SPECT (emb (\<lambda>(x,C). x\<in>S \<and> C=S-{x}) (t S)) }"

  lemma  mop_set_pick_extract: "tt \<le> lst (SPECT (emb (\<lambda>(x,C). x\<in>S \<and> C=S-{x}) (t S))) Q
        \<Longrightarrow> S \<noteq> {} \<Longrightarrow> tt \<le> lst (mop_set_pick_extract S) Q" unfolding mop_set_pick_extract_def by simp

  thm progress_rules

  lemma progress_mop_set_pick_extract[progress_rules]: "t S > 0 \<Longrightarrow> progress (mop_set_pick_extract S)"
    unfolding mop_set_pick_extract_def by (auto intro!: progress_rules simp add:   zero_enat_def) 

  sepref_register "mop_set_pick_extract" 
end
 


context
  fixes t:: "('c * 'c set) \<Rightarrow> nat" 
begin
  definition "mop_set_member x S = SPECT [ x \<in> S \<mapsto> enat (t (x,S)) ]"
  sepref_register "mop_set_member" 
  print_theorems 
end

 

context
  fixes t ::  "('c set * 'c) \<Rightarrow> nat"
begin
  definition "mop_set_del S x = SPECT [ S - {x} \<mapsto> t (S,x)]"

  lemma  mop_set_del: "tt \<le> lst (SPECT [ S - {x} \<mapsto> t (S,x)])  Q
        \<Longrightarrow> tt \<le> lst (mop_set_del S x) Q" unfolding mop_set_del_def by simp


  lemma progress_mop_set_del[progress_rules]: "t (S,x) > 0 \<Longrightarrow> progress (mop_set_del S x)"
      unfolding mop_set_del_def  by (auto intro: progress_rules simp add:   zero_enat_def) 

  sepref_register "mop_set_del" 
end


context 
  fixes t :: "('c*'c set) \<Rightarrow> nat"
begin

  definition "mop_set_insert x S = SPECT [insert x S \<mapsto> t (x,S)]"

  lemma mop_set_insert: "tt \<le> lst (SPECT [ (insert x S) \<mapsto> t (x,S)]) Q \<Longrightarrow>
         tt \<le> lst (mop_set_insert x S) Q" unfolding mop_set_insert_def by simp

  sepref_register "mop_set_insert" 
end

end
end

