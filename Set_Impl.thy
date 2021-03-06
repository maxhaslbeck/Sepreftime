theory Set_Impl
  imports HNR_While "Imperative_HOL_Time.RBTree_Impl"  DataRefinement
begin


hide_const R B


subsection "library for some set implementation"

term rbt_map_assn
thm rbt_search rbt_insert_rule


definition Z :: "(('a, unit) Mapping_Str.map \<times> 'a set) set"
  where "Z = {(c,a)|c a. keys_of c = a}"

subsubsection "empty set init via rbtree"

definition set_init_t :: "nat" where "set_init_t = 1"

definition set_init_SPEC :: "nat set nrest" where
  "set_init_SPEC \<equiv> SPECT [{} \<mapsto> set_init_t ]"


lemma set_init_hnr:
  "hn_refine (emp) tree_empty emp rbt_map_assn (\<Down>Z (set_init_SPEC))"
  sorry

definition rbt_map_assn' where "rbt_map_assn' a c =
        (\<exists>\<^sub>AM. rbt_map_assn M c * \<up>((M,a)\<in>Z))"

definition rbt_set_assn where [rewrite_ent]: "rbt_set_assn S p =
        (\<exists>\<^sub>AM. rbt_map_assn M p * \<up>(S = keys_of M))"

definition [rewrite]: "rbt_set_insert k b = rbt_insert k () b"

lemma g[rewrite]: "card (keys_of M) + 1 = sizeM1 M"
     by (auto simp: sizeM1_def)

setup \<open>fold del_prfstep_thm @{thms rbt_map_assn_def}\<close>  

declare [[print_trace]]
thm rbt_insert_rule rbt_insert_rule'
theorem rbt_insert_rule_abs [hoare_triple]:
  "<rbt_set_assn S p * $(rbt_insert_logN (card S + 1))> rbt_set_insert x p <rbt_set_assn (insert x S)>\<^sub>t"
  by auto2 

lemma a[rewrite]: "S = keys_of M \<Longrightarrow> M\<langle>x\<rangle> = Some () \<longleftrightarrow> x \<in> S"  
  by (simp add: keys_of_iff)  
                        
theorem rbt_search_abs [hoare_triple]:
  "<rbt_set_assn S b * $(rbt_search_time_logN (card S + 1))> rbt_search x b <\<lambda>r. rbt_set_assn S b * \<up>(r = Some () \<longleftrightarrow> x \<in> S)>\<^sub>t"
  by auto2


definition "set_empty = tree_empty"

theorem set_empty_rule [hoare_triple]:
  "<$1> set_empty <rbt_set_assn {}>" by auto2
 

lemma keys_of_empty_Map_empty: "{} = keys_of M \<longleftrightarrow> M=Map Map.empty"
  by(auto simp: keys_of_def meval_ext )   


lemma inst_ex_assn: "A \<Longrightarrow>\<^sub>A B x \<Longrightarrow> A \<Longrightarrow>\<^sub>A (\<exists>\<^sub>Ax. B x)"
  using entails_ex_post by blast 

lemma norm_ex_assn: "A \<Longrightarrow>\<^sub>A (\<exists>\<^sub>Ax. B x * C)  \<Longrightarrow> A \<Longrightarrow>\<^sub>A (\<exists>\<^sub>Ax. B x) * C"
  by (simp add: ex_distrib_star)

lemma fl': "(b \<Longrightarrow> A \<Longrightarrow>\<^sub>A B) \<Longrightarrow>  \<up>b *  A  \<Longrightarrow>\<^sub>A B"  
  by (simp add: assn_times_comm entails_def)

lemma fl: "A \<Longrightarrow>\<^sub>A B \<Longrightarrow> b \<Longrightarrow> A \<Longrightarrow>\<^sub>A B * \<up>b"  
  using entails_pure_post by blast  
lemma fl_: "A \<Longrightarrow>\<^sub>A B \<Longrightarrow> b \<Longrightarrow> A \<Longrightarrow>\<^sub>A \<up>b * B "  
  using fl assn_times_comm  by simp

lemma set_init_hnr'_short:
  "hn_refine (emp) set_empty emp rbt_set_assn (set_init_SPEC)"
  unfolding set_init_SPEC_def
  apply (rule extract_cost_otherway[OF _ set_empty_rule, where Cost_lb=1 and F=emp])
  apply simp apply(rule entails_triv) 
  subgoal 
    apply(rule ent_true_drop(2))
    by (auto intro!: inst_ex_assn fl entails_triv simp:   rbt_map_assn'_def )  
   by (auto intro: entails_triv simp: set_init_t_def)


lemma set_init_hnr':
  "hn_refine (emp) tree_empty emp rbt_map_assn' (set_init_SPEC)"
proof -
  from rbt_empty_rule[unfolded hoare_triple_def]
  have A: "\<And>h as \<sigma> r n t.
     pHeap h as n \<Turnstile> $ 1 \<Longrightarrow>
     run tree_empty (Some h) \<sigma> r t \<Longrightarrow>
     \<sigma> \<noteq> None \<and>
     pHeap (the \<sigma>) (new_addrs h as (the \<sigma>)) (n - t) \<Turnstile> rbt_map_assn empty_map r \<and>
     t \<le> n \<and> relH {a. a < heap.lim h \<and> a \<notin> as} h (the \<sigma>) \<and> heap.lim h \<le> heap.lim (the \<sigma>)" by blast

  thm entailsD
    
  show ?thesis unfolding hn_refine_def  set_init_SPEC_def set_init_t_def rbt_map_assn'_def
    apply auto
  proof (goal_cases)
    case (1 h as n)
    then have "pHeap h as (n + 1) \<Turnstile> emp * $ 1"
      using diff_add_inverse2 le_add2 mod_timeCredit_dest by presburger 
    then have ph: "pHeap h as (n + 1) \<Turnstile> $ 1" by simp

    note A[OF ph] run_and_execute
    have
      "(\<exists>h' t r. execute tree_empty h = Some (r, h', t) \<and> (pHeap h' (new_addrs h as h') (n + 1 - t) \<Turnstile> rbt_map_assn empty_map r \<and>
    t \<le> n + 1 \<and> relH {a. a < heap.lim h \<and> a \<notin> as} h h' \<and> heap.lim h \<le> heap.lim h'))" apply(simp only: run_and_execute[symmetric])
      using  A[OF ph]  by blast
    then obtain h' t and r:: "(nat, unit) rbt_node ref option" where
        heap: "pHeap h' (new_addrs h as h') (n + 1 - t) \<Turnstile> rbt_map_assn empty_map r"
     and   "execute tree_empty h = Some (r, h', t)" 
                "t \<le> n + 1" " relH {a. a < heap.lim h \<and> a \<notin> as} h h'" "heap.lim h \<le> heap.lim h'" by blast
    from heap have heap': "pHeap h' (new_addrs h as h') (Suc n - t) \<Turnstile> rbt_map_assn empty_map r" by simp
    show ?case apply(rule exI[where x=h'])  apply(rule exI[where x=t])   apply(rule exI[where x=r]) 
      apply safe
      apply fact
        apply (rule exI[where x=1]) apply safe apply simp apply fact
      subgoal apply(auto simp: keys_of_empty_Map_empty empty_map_def Z_def) apply(rule entailsD[OF _ heap'])  
        unfolding empty_map_def 
        by (smt entails_def entails_ex_post entails_frame'' entails_true match_rest one_assn_rule pure_assn_rule)    
      apply fact
      apply fact
      done
  qed
qed

subsubsection "set insertion via rbtree"

definition set_ins_t :: "nat\<Rightarrow>nat" where "set_ins_t n = rbt_insert_logN (n+1)"

definition set_ins_SPEC where
  "set_ins_SPEC x S \<equiv> SPECT [insert x S \<mapsto> set_ins_t (card S)]"


lemma set_ins_hnr:
  "hn_refine (rbt_map_assn M p) (rbt_insert x () p) emp rbt_map_assn (\<Down>Z (set_ins_SPEC x S))"
  sorry

lemma ent_ex: "(\<And>x. P x \<Longrightarrow>\<^sub>A Q) \<Longrightarrow> (\<exists>\<^sub>Ax. P x) \<Longrightarrow>\<^sub>A Q"
  by (meson entails_ex) 


lemma isolate_first: "\<And>A B C. \<Gamma> \<Longrightarrow>\<^sub>A \<Gamma>' \<Longrightarrow> A \<Longrightarrow>\<^sub>A B \<Longrightarrow> \<Gamma> * A \<Longrightarrow>\<^sub>A \<Gamma>' * B"  
  by (simp add: ent_star_mono)  

lemma inZ_conv: "(M, S) \<in> Z \<longleftrightarrow> (S = keys_of M)" unfolding Z_def by auto

lemma set_ins_hnr':
  "hn_refine (rbt_map_assn' S p * hn_val Id x x') (rbt_insert x' () p) (hn_val Id x x') rbt_map_assn' (set_ins_SPEC x S)"
  sorry

lemma set_ins_hnr_abs:
  "hn_refine (rbt_set_assn S p * hn_val Id x x') (rbt_set_insert x' p) (hn_val Id x x') rbt_set_assn (set_ins_SPEC x S)"

  unfolding set_ins_SPEC_def
  apply (rule extract_cost_otherway[OF _  rbt_insert_rule_abs ]) unfolding mult.assoc
    apply(rule match_first)
    apply rotatel apply(rule match_first) apply (rule entails_triv)

   apply rotatel apply rotatel apply takel apply taker apply(rule isolate_first)
  unfolding gr_def apply(simp only: ex_distrib_star')
    apply(rule inst_ex_assn)
    apply rotater unfolding hn_ctxt_def pure_def 
  apply(rule fl') apply (simp add: pure_conj[symmetric])
      apply(intro fl ) apply(rule entails_triv)
  apply simp
   apply(rule entails_triv) 
  by (auto simp: set_ins_t_def) 

subsubsection "set membership via rbtree"

fun set_mem_t :: "nat\<Rightarrow>nat" where "set_mem_t n = rbt_search_time_logN (n + 1)"

definition set_mem_SPEC where
  "set_mem_SPEC x S \<equiv> SPECT [ (x \<in> S) \<mapsto> set_mem_t (card S)]"

definition Y :: "(unit option \<times> bool) set" where
    "Y = {(c,a)|c a. c = Some () \<longleftrightarrow> a}"

lemma set_mem_hnr:
  "hn_refine (rbt_map_assn M p) (rbt_search x p) (rbt_map_assn M p) (pure Id) (\<Down>Y (set_mem_SPEC x S))"
  sorry

definition Y' :: "bool \<Rightarrow> unit option \<Rightarrow> assn" where
  "Y' b v = \<up>(  v = Some () \<longleftrightarrow> b )"
 
lemma set_mem_hnr':
  "hn_refine (rbt_map_assn' S p * hn_val Id x x') (rbt_search (x'::nat) p) (rbt_map_assn' S p * hn_val Id x x') Y' ( (set_mem_SPEC x S))"
  sorry 

lemma set_mem_hnr_abs:
  "hn_refine (rbt_set_assn S p * hn_val Id x x') (rbt_search (x'::nat) p) (rbt_set_assn S p * hn_val Id x x') Y' ( (set_mem_SPEC x S))"
  unfolding set_mem_SPEC_def
  apply (rule extract_cost_otherway[OF _  rbt_search_abs ]) unfolding mult.assoc
    apply(rule match_first)
    apply rotatel apply(rule match_first) apply (rule entails_triv)

   apply(rule match_first) 
  apply(rule fl') unfolding hn_ctxt_def pure_def apply rotatel
  apply(rule fl')  apply(rule fl_) apply(simp only: ex_distrib_star[symmetric])
    apply(rule inst_ex_assn) unfolding Y'_def unfolding mult.assoc
    apply(rule fl_)   apply(rule fl_) apply(rule entails_triv)
  apply simp apply simp apply simp by simp 

(* theorems that should be visible from the outside *)

(* init *)
thm set_init_hnr'_short set_init_SPEC_def
             
(* insert *)
thm set_ins_hnr_abs set_ins_SPEC_def

(* membership test *)
thm set_mem_hnr_abs set_mem_SPEC_def



end