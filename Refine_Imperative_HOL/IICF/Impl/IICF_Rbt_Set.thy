theory IICF_Rbt_Set
  imports "SepLogicTime_RBTreeBasic.RBTree_Impl" 
      "../Intf/IICF_Set"  "../../../RefineMonadicVCG" "../../Sepref"
begin

hide_const R B

subsection "library for some set implementation"


subsubsection "interface"
 




term rbt_map_assn
thm rbt_search rbt_insert_rule


definition Z :: "(('a, unit) Mapping_Str.map \<times> 'a set) set"
  where "Z = {(c,a)|c a. keys_of c = a}"

subsubsection "empty set init via rbtree"

definition set_init_t :: "nat" where "set_init_t = 1"

definition set_init_SPEC :: "nat set nrest" where
  "set_init_SPEC \<equiv> SPECT [{} \<mapsto> set_init_t ]"

definition rbt_map_assn' where "rbt_map_assn' a c =
        (\<exists>\<^sub>AM. rbt_map_assn M c * \<up>((M,a)\<in>Z))"

definition rbt_set_assn :: "_ set \<Rightarrow> (_, unit) rbt_node ref option \<Rightarrow> assn"  where [rewrite_ent]:
  "rbt_set_assn S p =
        (\<exists>\<^sub>AM. rbt_map_assn M p * \<up>(S = keys_of M))"

definition [rewrite]: "rbt_set_insert k b = rbt_insert k () b"

lemma g[rewrite]: "card (keys_of M) + 1 = sizeM1 M"
     by (auto simp: sizeM1_def)


definition rbt_pick where   "rbt_pick p = do {(case p of 
     None \<Rightarrow> return None |
     Some pp \<Rightarrow> do {
     t \<leftarrow> !pp;
     return (Some (key t))
   }) }"

lemma rbt_pick_rule [hoare_triple]:
  "<btree t p *$2>
   rbt_pick  p
   <\<lambda>r. btree t p * \<up>( (t = Leaf \<longrightarrow> r = None) \<and> (t\<noteq>Leaf \<longrightarrow> the r \<in> rbt_set t) )>\<^sub>t"
@proof @case "t = Leaf"  @qed

definition  rbt_map_pick where    "rbt_map_pick p = rbt_pick p"

lemma rbt_map_Leaf: "rbt_map (Leaf) = empty_map"
  by (simp add: rbt_map_def)

lemma neq_ext: "(\<exists>x. f x \<noteq>  g x ) \<Longrightarrow> f \<noteq> g" by auto


lemma meval_ext_neg: " M\<langle>x\<rangle> \<noteq> N\<langle>x\<rangle> \<Longrightarrow> M \<noteq> N"
  apply (cases M) apply (cases N) by auto
 
  


lemma rbt_map_Leaf_conv: "M = rbt_map t \<Longrightarrow> (t = Leaf) = (M = empty_map)"
  apply(cases t) apply (simp_all add: rbt_map_def empty_map_def) 
  subgoal for c l k v r apply(rule meval_ext_neg[where x=k])
    apply(simp only:  meval.simps)
    apply(simp only: map_of_alist_nil'[symmetric]) by simp 
  done

lemma empty_rbt_map_is_Leaf: "rbt_map t = empty_map \<Longrightarrow> t = Leaf"
  by(simp add: rbt_map_Leaf_conv)

lemma rbt_map_Leaf_is_empty_map: "rbt_map Leaf = empty_map "
  by(simp add: rbt_map_def)

lemma dd: "M= rbt_map t \<Longrightarrow> t = Leaf \<Longrightarrow> M = empty_map"
  by(simp add: rbt_map_def)

declare rbt_set_keys_of [forward]

lemma rbt_map_pick_rule [hoare_triple]:
  "<rbt_map_assn M p * $ 2>
   rbt_map_pick  p
   <\<lambda>r. rbt_map_assn M p * \<up>( (M = empty_map \<longrightarrow> r = None) \<and> (M\<noteq>empty_map \<longrightarrow> the r \<in> keys_of M))>\<^sub>t"
  by auto2



thm tree_is_empty_rule
declare tree_is_empty_rule [hoare_triple]

definition "rbt_map_isempty b = tree_is_empty b"
 

lemma rbt_map_isempty_rule[hoare_triple]: "<rbt_map_assn M b * $1> rbt_map_isempty b <\<lambda>r. rbt_map_assn M b * \<up> (r \<longleftrightarrow> (M = empty_map))>\<^sub>t"
  by auto2

setup {* fold del_prfstep_thm @{thms rbt_map_assn_def} *}   




definition  rbt_set_pick where    "rbt_set_pick p = do {
        s \<leftarrow> rbt_map_pick p;
        return (the s) }"

 
theorem rbt_set_pick_rule [hoare_triple]:
  "S\<noteq>{} \<Longrightarrow> <rbt_set_assn S b * $4> rbt_set_pick b <\<lambda>r. rbt_set_assn S b * \<up>(r \<in> S)>\<^sub>t"
  by auto2

definition  rbt_set_isempty where    "rbt_set_isempty p =rbt_map_isempty p"

lemma rbt_set_isempty_rule: "<rbt_set_assn S b * $1> rbt_set_isempty b <\<lambda>r. rbt_set_assn S b * \<up> (r \<longleftrightarrow> (S = {}))>\<^sub>t"
  by auto2


declare [[print_trace]]
thm rbt_insert_rule rbt_insert_rule'
theorem rbt_insert_rule_abs [hoare_triple]:
  "<rbt_set_assn S p * $(rbt_insert_logN (card S + 1))> rbt_set_insert x p <rbt_set_assn (insert x S)>\<^sub>t"
  by auto2 

lemma a[rewrite]: "S = keys_of M \<Longrightarrow> M\<langle>x\<rangle> = Some () \<longleftrightarrow> x \<in> S"  
  by (simp add: keys_of_iff)  



definition [rewrite]: "rbt_set_delete b k = rbt_delete k  b"

theorem rbt_delete_rule_abs [hoare_triple]:
  "<rbt_set_assn S p * $(rbt_delete_time_logN (card S + 1))> rbt_set_delete p x <rbt_set_assn (S -  {x})>\<^sub>t"
  by auto2 

thm rbt_delete_rule


(*
theorem rbt_search_abs [hoare_triple]:
  "<rbt_set_assn S b * $(rbt_search_time_logN (card S + 1))> rbt_search x b <\<lambda>r. rbt_set_assn S b * \<up>(r = Some () \<longleftrightarrow> x \<in> S)>\<^sub>t"
  by auto2
*)

definition rbt_mem :: "'a::{heap,linorder} \<Rightarrow> ('a, unit) rbt_node ref option \<Rightarrow> bool Heap" where [rewrite]:
  "rbt_mem x p = do {
      f \<leftarrow> rbt_search x p;
      return (f = Some ()) }"

     
theorem rbt_mem_rule [hoare_triple]:
  "<rbt_set_assn S b * $(rbt_search_time_logN (card S + 1) + 1)> rbt_mem x b <\<lambda>r. rbt_set_assn S b * \<up>(r = (x \<in> S))>\<^sub>t"
  by auto2



definition paint :: "color \<Rightarrow> ('a::heap, 'b::heap) btree \<Rightarrow> unit Heap" where
  "paint c p = (case p of
    None \<Rightarrow> return ()
  | Some pp \<Rightarrow> do {
     t \<leftarrow> !pp;
     pp := Node (lsub t) c (key t) (val t) (rsub t)
   })"
  
lemma paint_rule [hoare_triple]:
  "<btree t p *$2>
   paint c p
   <\<lambda>_. btree (RBTree.paint c t) p>\<^sub>t"
@proof @case "t = Leaf" @qed


definition "set_empty = tree_empty"

theorem set_empty_rule [hoare_triple]:
  "<$1> set_empty <rbt_set_assn {}>" by auto2
 

lemma keys_of_empty_Map_empty: "{} = keys_of M \<longleftrightarrow> M=Map Map.empty"
  by(auto simp: keys_of_def meval_ext )   


lemma inst_ex_assn: "A \<Longrightarrow>\<^sub>A B x \<Longrightarrow> A \<Longrightarrow>\<^sub>A (\<exists>\<^sub>Ax. B x)"
  using entails_ex_post by blast 

lemma norm_ex_assn: "A \<Longrightarrow>\<^sub>A (\<exists>\<^sub>Ax. B x * C)  \<Longrightarrow> A \<Longrightarrow>\<^sub>A (\<exists>\<^sub>Ax. B x) * C"
  by (simp)

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
  apply simp  
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

lemma ent_ex: "(\<And>x. P x \<Longrightarrow>\<^sub>A Q) \<Longrightarrow> (\<exists>\<^sub>Ax. P x) \<Longrightarrow>\<^sub>A Q"
  by (meson entails_ex) 


lemma isolate_first: "\<And>A B C. \<Gamma> \<Longrightarrow>\<^sub>A \<Gamma>' \<Longrightarrow> A \<Longrightarrow>\<^sub>A B \<Longrightarrow> \<Gamma> * A \<Longrightarrow>\<^sub>A \<Gamma>' * B"  
  by (simp add: ent_star_mono)  

lemma inZ_conv: "(M, S) \<in> Z \<longleftrightarrow> (S = keys_of M)" unfolding Z_def by auto


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
    apply(rule fl') apply (simp ) apply safe
  prefer 4  apply(rule entails_triv) 
  by (auto simp: set_ins_t_def) 

subsubsection "set membership via rbtree"

fun set_mem_t :: "nat\<Rightarrow>nat" where "set_mem_t n = rbt_search_time_logN (n + 1)"

definition set_mem_SPEC :: "'a \<Rightarrow> 'a set \<Rightarrow> bool nrest" where
  "set_mem_SPEC x S \<equiv> SPECT [ (x \<in> S) \<mapsto> set_mem_t (card S)]"

definition Y :: "(unit option \<times> bool) set" where
    "Y = {(c,a)|c a. c = Some () \<longleftrightarrow> a}"

definition Y' :: "bool \<Rightarrow> unit option \<Rightarrow> assn" where
  "Y' b v = \<up>(  v = Some () \<longleftrightarrow> b )"
 
(* theorems that should be visible from the outside *)

(* init *)
thm set_init_hnr'_short set_init_SPEC_def
             
(* insert *)
thm set_ins_hnr_abs set_ins_SPEC_def

(* membership test *)
(* thm set_mem_hnr_abs set_mem_SPEC_def *)

subsubsection "implement the interface"

lemma mop_set_empty_rule[sepref_fr_rules]:
  "1\<le>n \<Longrightarrow> hn_refine (emp) set_empty emp rbt_set_assn (PR_CONST (mop_set_empty n))"

  unfolding autoref_tag_defs mop_set_empty_def  
  apply (rule extract_cost_otherway[OF _ set_empty_rule, where Cost_lb=1 and F=emp])
  apply simp  
  subgoal 
    apply(rule ent_true_drop(2))
    by (auto intro!: inst_ex_assn fl entails_triv simp:   rbt_map_assn'_def )  
   by (auto intro: entails_triv simp: set_init_t_def)


lemma mop_set_insert_rule[sepref_fr_rules]:
  "rbt_insert_logN (card S + 1) \<le> t S \<Longrightarrow> 
      hn_refine (hn_val Id x x' * hn_ctxt rbt_set_assn S p)
       (rbt_set_insert x' p)
       (hn_val Id x x' * hn_invalid rbt_set_assn S p) rbt_set_assn ( PR_CONST (mop_set_insert t) $ x $ S)"

  unfolding mop_set_insert_def autoref_tag_defs
  apply (rule extract_cost_otherway[OF _  rbt_insert_rule_abs, where F="hn_val Id x x' * hn_invalid rbt_set_assn S p" ])
  unfolding mult.assoc
    apply(rotatel)
    apply rotater  apply rotater  apply rotater   apply taker apply(rule isolate_first)
  apply (simp add: gr_def hn_ctxt_def)  apply(rule invalidate_clone)
  unfolding hn_ctxt_def
    apply(rule match_first)  apply (rule entails_triv)

   apply rotatel apply rotatel apply swapl apply takel apply swapr apply taker 
   apply(rule isolate_first) 
  unfolding gr_def apply(simp only: ex_distrib_star' pure_def)
    apply(rule inst_ex_assn) apply simp apply safe prefer 4 
     apply(rule entails_triv) 
  by (auto) 


lemma mop_set_delete_rule[sepref_fr_rules]:
  "rbt_delete_time_logN (card S + 1) \<le> t S \<Longrightarrow> 
      hn_refine (hn_val Id x x' * hn_ctxt rbt_set_assn S p)
       (rbt_set_delete p x')
       (hn_val Id x x' * hn_invalid rbt_set_assn S p) rbt_set_assn ( PR_CONST (mop_set_del t) $ S $ x)"

  unfolding mop_set_del_def autoref_tag_defs
  apply (rule extract_cost_otherway[OF _  rbt_delete_rule_abs, where F="hn_val Id x x' * hn_invalid rbt_set_assn S p" ])
  unfolding mult.assoc
    apply(rotatel)
    apply rotater  apply rotater  apply rotater   apply taker apply(rule isolate_first)
  apply (simp add: gr_def hn_ctxt_def)  apply(rule invalidate_clone)
  unfolding hn_ctxt_def
    apply(rule match_first)  apply (rule entails_triv)

   apply rotatel apply rotatel apply swapl apply takel apply swapr apply taker 
   apply(rule isolate_first) 
  unfolding gr_def apply(simp only: ex_distrib_star' pure_def)
    apply(rule inst_ex_assn) apply simp apply safe prefer 4 
     apply(rule entails_triv) 
  by (auto) 



lemma mop_mem_set_rule[sepref_fr_rules]:
  "rbt_search_time_logN (card S + 1) + 1 \<le> t S \<Longrightarrow>
    hn_refine (hn_val Id x x' * hn_ctxt rbt_set_assn S p)
     (rbt_mem (x') p)
     (hn_ctxt (pure Id) x x' * hn_ctxt rbt_set_assn S p) id_assn ( PR_CONST (mop_set_member t) $  x $ S)"

  unfolding autoref_tag_defs mop_set_member_def
  apply (rule extract_cost_otherway[OF _  rbt_mem_rule]) unfolding mult.assoc
  unfolding hn_ctxt_def
    apply rotatel apply(rule match_first) apply(rule match_first)       
   apply (rule entails_triv)
  apply rotater
   apply(rule match_first) apply (simp add: pure_def)   apply safe
    apply(rule inst_ex_assn[where x="x \<in> S"])  by auto 


thm rbt_set_isempty_rule


lemma mop_set_isempty_rule[sepref_fr_rules]:
  "1 \<le> t S \<Longrightarrow>
    hn_refine (hn_ctxt rbt_set_assn S p)
     (rbt_set_isempty  p)
     (hn_ctxt rbt_set_assn S p) id_assn ( PR_CONST (mop_set_isempty t) $ S)"

  unfolding autoref_tag_defs mop_set_isempty_def             
  apply (rule extract_cost_otherway[OF _  rbt_set_isempty_rule, where F="emp" ]) unfolding mult.assoc
  unfolding hn_ctxt_def  apply(rule match_first) apply simp      
     apply (rule entails_triv)
   apply(rule match_first)   apply clarsimp   
   apply (simp add: pure_def)    
    apply(rule inst_ex_assn[where x="S = {}"]) apply (simp add: dom_emb'_eq)
  by (auto split: if_splits simp add: ran_def emb'_def)



lemma mop_set_pick_rule[sepref_fr_rules]:
  "4 \<le> t S \<Longrightarrow>
    hn_refine (hn_ctxt rbt_set_assn S p)
     (rbt_set_pick  p)
     (hn_ctxt rbt_set_assn S p) id_assn ( PR_CONST (mop_set_pick t) $ S)"

  unfolding autoref_tag_defs mop_set_pick_def
  apply(rule hnr_ASSERT)
  apply (rule extract_cost_otherway[OF _  rbt_set_pick_rule, where F = emp]) unfolding mult.assoc
  unfolding hn_ctxt_def  apply(rule match_first) apply simp      
     apply (rule entails_triv)
  apply simp 
   apply(rule match_first) apply clarsimp
   
   apply (simp add: pure_def)   subgoal for r
    apply(rule inst_ex_assn[where x="r"]) by (simp add: dom_emb'_eq)
  by (auto split: if_splits simp add: ran_def emb'_def)

thm mop_set_pick_rule[to_hfref]

lemma "(rbt_set_pick, PR_CONST (mop_set_pick t)) \<in> [\<lambda>S. 4 \<le> t S]\<^sub>a rbt_set_assn\<^sup>k \<rightarrow> id_assn"
  apply sepref_to_hoare
  unfolding autoref_tag_defs mop_set_pick_def
  apply(rule hnr_ASSERT)
  apply (rule extract_cost_otherway'[OF _ rbt_set_pick_rule])
     apply solve_entails apply auto[]
  oops
  


definition "rbt_set_pick_extract S = do { v \<leftarrow> mop_set_pick (\<lambda>_. 4) S;
                              C \<leftarrow> mop_set_del (\<lambda>S. rbt_delete_time_logN (card S + 1)) S v;
                              RETURNT (v,C) }"

lemma rbt_set_pick_extract_refines: "rbt_delete_time_logN (card S + 1) + 4 \<le> t S \<Longrightarrow> rbt_set_pick_extract S \<le> mop_set_pick_extract t S"
  unfolding mop_set_pick_extract_def rbt_set_pick_extract_def mop_set_pick_def mop_set_del_def
  apply(rule le_ASSERTI)
  apply(rule T_specifies_I)
  by (vcg' \<open>simp add: Some_le_emb'_conv\<close>)

lemma rbt_set_pick_extract_refines': "(rbt_set_pick_extract, PR_CONST (mop_set_pick_extract t)) \<in> [\<lambda>S. rbt_delete_time_logN (card S + 1) + 4 \<le> t S]\<^sub>f Id \<rightarrow> \<langle>Id\<rangle>nrest_rel"
  apply(rule frefI)
  apply(rule nrest_relI) using rbt_set_pick_extract_refines by auto

schematic_goal mop_set_pick_extract_rule':
      notes [id_rules] = 
        itypeI[Pure.of S "TYPE('a set)"] 
      shows
  "hn_refine (hn_ctxt rbt_set_assn S p) (?c::?'c Heap) ?\<Gamma>' ?R (rbt_set_pick_extract S)"
  unfolding rbt_set_pick_extract_def
  apply sepref done

concrete_definition (in -) set_pick_extract uses mop_set_pick_extract_rule'
print_theorems

    sepref_register "set_pick_extract " 
 

lemmas kruskal_ref_spec[sepref_fr_rules] = set_pick_extract.refine[FCOMP rbt_set_pick_extract_refines']
 




end
