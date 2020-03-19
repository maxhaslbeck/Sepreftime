section \<open>Map Interface\<close>
theory IICF_Map     
imports "../../Sepref"
begin
  
subsection \<open>Parametricity for Maps\<close>
definition [to_relAPP]: "map_rel K V \<equiv> (K \<rightarrow> \<langle>V\<rangle>option_rel)
  \<inter> { (mi,m). dom mi \<subseteq> Domain K \<and> dom m \<subseteq> Range K }"
(*
definition [to_relAPP]: "map_rel K V \<equiv> (K \<rightarrow> \<langle>V\<rangle>option_rel)
  \<inter> { (mi,m). dom mi \<subseteq> Domain K \<and> dom m \<subseteq> Range K 
      \<and> ran mi \<subseteq> Domain V \<and> ran m \<subseteq> Range V }"
*)

lemma bi_total_map_rel_eq:
  "\<lbrakk>IS_RIGHT_TOTAL K; IS_LEFT_TOTAL K\<rbrakk> \<Longrightarrow> \<langle>K,V\<rangle>map_rel = K \<rightarrow> \<langle>V\<rangle>option_rel"
  unfolding map_rel_def IS_RIGHT_TOTAL_def IS_LEFT_TOTAL_def
  by (auto dest: fun_relD)
  
lemma map_rel_Id[simp]: "\<langle>Id,Id\<rangle>map_rel = Id" 
  unfolding map_rel_def by auto

lemma map_rel_empty1_simp[simp]: 
  "(Map.empty,m)\<in>\<langle>K,V\<rangle>map_rel \<longleftrightarrow> m=Map.empty"
  apply (auto simp: map_rel_def)
  by (meson RangeE domIff option_rel_simp(1) subsetCE tagged_fun_relD_none)

lemma map_rel_empty2_simp[simp]: 
  "(m,Map.empty)\<in>\<langle>K,V\<rangle>map_rel \<longleftrightarrow> m=Map.empty"
  apply (auto simp: map_rel_def)
  by (meson Domain.cases domIff fun_relD2 option_rel_simp(2) subset_eq)

lemma map_rel_obtain1:
  assumes 1: "(m,n)\<in>\<langle>K,V\<rangle>map_rel"
  assumes 2: "n l = Some w"
  obtains k v where "m k = Some v" "(k,l)\<in>K" "(v,w)\<in>V"
  using 1 unfolding map_rel_def
proof clarsimp
  assume R: "(m, n) \<in> K \<rightarrow> \<langle>V\<rangle>option_rel"
  assume "dom n \<subseteq> Range K"
  with 2 obtain k where "(k,l)\<in>K" by auto
  moreover from fun_relD[OF R this] have "(m k, n l) \<in> \<langle>V\<rangle>option_rel" .
  with 2 obtain v where "m k = Some v" "(v,w)\<in>V" by (cases "m k"; auto)
  ultimately show thesis by - (rule that)
qed

lemma map_rel_obtain2:
  assumes 1: "(m,n)\<in>\<langle>K,V\<rangle>map_rel"
  assumes 2: "m k = Some v"
  obtains l w where "n l = Some w" "(k,l)\<in>K" "(v,w)\<in>V"
  using 1 unfolding map_rel_def
proof clarsimp
  assume R: "(m, n) \<in> K \<rightarrow> \<langle>V\<rangle>option_rel"
  assume "dom m \<subseteq> Domain K"
  with 2 obtain l where "(k,l)\<in>K" by auto
  moreover from fun_relD[OF R this] have "(m k, n l) \<in> \<langle>V\<rangle>option_rel" .
  with 2 obtain w where "n l = Some w" "(v,w)\<in>V" by (cases "n l"; auto)
  ultimately show thesis by - (rule that)
qed

lemma param_dom[param]: "(dom,dom)\<in>\<langle>K,V\<rangle>map_rel \<rightarrow> \<langle>K\<rangle>set_rel"
  apply (clarsimp simp: set_rel_def; safe)
  apply (erule (1) map_rel_obtain2; auto)
  apply (erule (1) map_rel_obtain1; auto)
  done

subsection \<open>Interface Type\<close>

sepref_decl_intf ('k,'v) i_map is "'k \<rightharpoonup> 'v"

lemma [synth_rules]: "\<lbrakk>INTF_OF_REL K TYPE('k); INTF_OF_REL V TYPE('v)\<rbrakk> 
  \<Longrightarrow> INTF_OF_REL (\<langle>K,V\<rangle>map_rel) TYPE(('k,'v) i_map)" by simp

subsection \<open>Operations\<close>


context
  fixes t ::  "unit \<Rightarrow> nat"
begin
  definition "mop_map_empty  = SPECT [ Map.empty \<mapsto> t ()]"

  lemma  mop_map_empty: "tt \<le> lst (SPECT [ Map.empty \<mapsto> t () ]) Q 
        \<Longrightarrow> tt \<le> lst (mop_map_empty ) Q" unfolding mop_map_empty_def by simp

  sepref_register "mop_map_empty" 
end


context
  fixes t ::  "(( 'a \<Rightarrow> 'b option) * 'a) * 'b \<Rightarrow> nat"
begin
  definition "mop_map_update m k v = SPECT [ m(k \<mapsto> v) \<mapsto> t ((m,k),v)]"


  lemma  mop_map_update: "tt \<le> lst (SPECT [ m(k \<mapsto> v) \<mapsto> t ((m,k),v)])  Q
        \<Longrightarrow> tt \<le> lst (mop_map_update m k v) Q" unfolding mop_map_update_def by simp

  sepref_register "mop_map_update" 
end


context
  fixes t ::  "('a \<Rightarrow> 'b option) * 'a \<Rightarrow> nat"
begin
  definition "mop_map_dom_member m x = SPECT (emb (\<lambda>b. b \<longleftrightarrow> x\<in>dom m) (t (m,x)))"


  lemma  mop_map_dom_member: "tt \<le> lst (SPECT (emb (\<lambda>b. b \<longleftrightarrow> x\<in>dom m) (t (m,x))))  Q
        \<Longrightarrow> tt \<le> lst (mop_map_dom_member m x) Q" unfolding mop_map_dom_member_def by simp

  sepref_register "mop_map_dom_member" 
end

context
  fixes t ::  "('a \<Rightarrow> 'b option) * 'a \<Rightarrow> nat"
begin
  definition "mop_map_lookup m x = do {
        ASSERT (x\<in>dom m);
        SPECT [  (the (m x)) \<mapsto> t (m,x)]
      }"


  lemma  mop_map_lookup: "tt \<le> lst (SPECT [  (the (m x)) \<mapsto> t (m,x)]) Q
        \<Longrightarrow> x : dom m 
        \<Longrightarrow> tt \<le> lst (mop_map_lookup m x) Q" unfolding mop_map_lookup_def by simp

  lemma progress_mop_map_lookup[progress_rules]: "t (m,x) > 0 \<Longrightarrow> progress (mop_map_lookup m x)"
      unfolding mop_map_lookup_def by (auto intro!: progress_rules simp add:   zero_enat_def) 

  sepref_register "mop_map_lookup"
end

end
