section \<open>Matrix Interface\<close>
theory IICF_Matrix
imports "../../Sepref"
begin

subsection \<open>Relator and Interface\<close>
definition [to_relAPP]: "mtx_rel A \<equiv> nat_rel \<times>\<^sub>r nat_rel \<rightarrow> A"

lemma mtx_rel_id[simp]: "\<langle>Id\<rangle>mtx_rel = Id" unfolding mtx_rel_def by auto

type_synonym 'a mtx = "nat\<times>nat \<Rightarrow> 'a"
sepref_decl_intf 'a i_mtx is "nat\<times>nat \<Rightarrow> 'a"

lemma [synth_rules]: "INTF_OF_REL A TYPE('a) \<Longrightarrow> INTF_OF_REL (\<langle>A\<rangle>mtx_rel) TYPE('a i_mtx)"
  by simp

subsection \<open>Operations\<close>  

definition op_mtx_new :: "'a mtx \<Rightarrow> 'a mtx" where [simp]: "op_mtx_new c \<equiv> c"

sepref_decl_op (no_def) mtx_new: "op_mtx_new" :: "(nat_rel\<times>\<^sub>rnat_rel \<rightarrow> A) \<rightarrow> \<langle>A\<rangle>mtx_rel"
  apply (rule fref_ncI) unfolding op_mtx_new_def[abs_def] mtx_rel_def 
  by parametricity

(* TODO: Ad-hoc rule *)
lemma mtx_init_adhoc_frame_match_rule[sepref_frame_match_rules]:
  "hn_val (nat_rel\<times>\<^sub>rnat_rel \<rightarrow> A) x y \<Longrightarrow>\<^sub>t hn_val (nat_rel\<times>\<^sub>rnat_rel \<rightarrow> the_pure (pure A)) x y"
  by simp

context
  fixes t ::  "('a mtx * (nat*nat)) => nat"
begin
  definition "mop_matrix_get (m::_ mtx) e = SPECT [m e \<mapsto> enat (t (m,e))]"

  lemma matrix_get: "\<And>tt. tt \<le> lst (SPECT [ m e \<mapsto> t (m,e)]) Q \<Longrightarrow> tt
           \<le> lst (mop_matrix_get m e) Q" unfolding mop_matrix_get_def by simp 


  lemma progress_mop_matrix_get[progress_rules]: "t (m,e) > 0 \<Longrightarrow> progress (mop_matrix_get m e)"
    unfolding mop_matrix_get_def by (auto intro!: progress_rules simp add:   zero_enat_def) 

  sepref_register "mop_matrix_get" 
end 

context
  fixes t ::  "(('b mtx * (nat*nat)) * 'b) \<Rightarrow> nat"
begin
  definition "mop_matrix_set (m::'b mtx) e v = SPECT [m(e:=v) \<mapsto> enat (t ((m,e),v))]"

  lemma matrix_set: "\<And>tt. tt \<le> lst (SPECT [ m(e:=v) \<mapsto> t ((m,e),v)]) Q \<Longrightarrow> tt
           \<le> lst (mop_matrix_set m e v) Q" unfolding mop_matrix_set_def by simp 
 
  sepref_register "mop_matrix_set" 
  print_theorems 
end 
    
definition mtx_nonzero :: "_ mtx \<Rightarrow> (nat\<times>nat) set" where "mtx_nonzero m \<equiv> {(i,j). m (i,j)\<noteq>0}"

lemma mtx_nonzeroD:
  "\<lbrakk>\<not>i<N; mtx_nonzero m \<subseteq> {0..<N}\<times>{0..<M}\<rbrakk> \<Longrightarrow> m(i,j) = 0"
  "\<lbrakk>\<not>j<M; mtx_nonzero m \<subseteq> {0..<N}\<times>{0..<M}\<rbrakk> \<Longrightarrow> m(i,j) = 0"
  by (auto simp: mtx_nonzero_def)



  subsubsection \<open>Square Matrix\<close>

  definition [simp]: "op_amtx_new (N::nat) (M::nat) \<equiv> op_mtx_new"  

context fixes N M :: nat
    and t :: "nat \<Rightarrow> nat \<Rightarrow> nat"  
    begin

    definition "mop_amtx_new c =  SPECT [op_amtx_new N M c \<mapsto> t N M] "


    sepref_register "mop_amtx_new"
end

end

