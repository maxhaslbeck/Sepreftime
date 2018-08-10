theory Remdups_Example
imports HNR_While "SepLogicTime_RBTreeBasic.RBTree_Impl" DataRefinement
begin


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

lemma set_init_hnr':
  "hn_refine (emp) tree_empty emp rbt_map_assn' (set_init_SPEC)"
  sorry


subsubsection "set insertion via rbtree"

fun set_ins_t :: "nat\<Rightarrow>nat" where "set_ins_t n = 4*n"

definition set_ins_SPEC where
  "set_ins_SPEC x S \<equiv> SPECT [insert x S \<mapsto> set_ins_t (card S)]"


lemma set_ins_hnr:
  "hn_refine (rbt_map_assn M p) (rbt_insert x () p) emp rbt_map_assn (\<Down>Z (set_ins_SPEC x S))"
  sorry

lemma set_ins_hnr':
  "hn_refine (rbt_map_assn M p) (rbt_insert x () p) emp rbt_map_assn' (set_ins_SPEC x S)"
  sorry


subsubsection "set membership via rbtree"

fun set_mem_t :: "nat\<Rightarrow>nat" where "set_mem_t n = 4*n"

definition set_mem_SPEC where
  "set_mem_SPEC x S \<equiv> SPECT [ (x \<in> S) \<mapsto> set_mem_t (card S)]"

definition Y :: "(unit option \<times> bool) set" where
    "Y = {(c,a)|c a. c = Some () \<longleftrightarrow> a}"

lemma set_mem_hnr:
  "hn_refine (rbt_map_assn M p) (rbt_search x p) (rbt_map_assn M p) (pure Id) (\<Down>Y (set_mem_SPEC x S))"
  sorry



subsection "remdups"

fun rd_t :: "nat\<Rightarrow>nat" where "rd_t n = n * (set_ins_t n + set_mem_t n + 0 + 0 + 0 + 10)"

definition "rd_SPEC as \<equiv> SPECT [remdups as \<mapsto> rd_t (length as)]"



definition rd_impl1 :: "nat list \<Rightarrow> (nat list) nrest" where
  "rd_impl1 as = do {
          ys \<leftarrow> RETURNT [];
          S \<leftarrow> set_init_SPEC;
          whileT (\<lambda>(xs,ys,S). length xs > 0)
            (\<lambda>(xs,ys,S). do {                          
                          ASSERT (length xs > 0);
                          ASSERT (length xs + length ys \<le> length as);
                          ASSERT (card S \<le> length ys);
                          x \<leftarrow> RETURNT (hd xs);
                          xs \<leftarrow> RETURNT (tl xs);
                          b \<leftarrow> set_mem_SPEC x S;
                          (if b
  then  RETURNT (xs,ys,S)
  else do { S \<leftarrow> set_ins_SPEC x S;
            ys \<leftarrow> SPECT [x#ys\<mapsto> 10];
            RETURNT (xs,ys,S)
  } ) }) (as,ys,S);
          RETURNT ys
      }"



lemma rd_impl1_refines: "rd_impl1 as \<le> rd_SPEC as" sorry


lemma hn_ctxt_triple: "\<And>A B C .
    hn_ctxt (\<lambda>(c1, c2, c3) (a1, a2, a3). A c1 a1  * B c2 a2 * C c3 a3 ) (c1, c2, c3) (a1, a2, a3)
    = hn_ctxt A c1 a1 * hn_ctxt B c2 a2 * hn_ctxt C c3 a3"
  unfolding hn_ctxt_def by simp


lemma hn_ctxt_triple'': "\<And>A B C .
    hn_ctxt (\<lambda>(c1, c2, c3) (a1, a2, a3). A c1 a1  * B c2 a2 * C c3 a3 ) s s'
    = hn_ctxt A (fst s) (fst s') * hn_ctxt B (fst (snd s)) (fst (snd s')) * hn_ctxt C (snd (snd s)) (snd (snd s'))"
  unfolding hn_ctxt_def  
  by (simp add: case_prod_beta')  

lemma hn_ctxt_triple': "hn_val Id as as * (hn_val Id x x' * hn_ctxt rbt_map_assn' xa S') \<Longrightarrow>\<^sub>A
       hn_ctxt (\<lambda>(c1, c2, c3) (a1, a2, a3). pure Id c1 a1 * (pure Id c2 a2 * rbt_map_assn' c3 a3)) (as, x, xa) (as, x', S')"
  unfolding hn_ctxt_def apply simp 
  by (simp add: entails_triv) 


lemma isolate_first: "\<And>A B C. \<Gamma> \<Longrightarrow>\<^sub>A \<Gamma>' \<Longrightarrow> A \<Longrightarrow>\<^sub>A B \<Longrightarrow> \<Gamma> * A \<Longrightarrow>\<^sub>A \<Gamma>' * B"  
 
  by (simp add: ent_star_mono)  

lemma add_triv: "\<And>B C x. hn_ctxt (pure Id) x x * B \<Longrightarrow>\<^sub>A C \<Longrightarrow> B \<Longrightarrow>\<^sub>A C"
  unfolding hn_ctxt_def pure_def  
  using assn_times_comm entails_pure by fastforce  

lemma hd_entails:
  "hn_val Id a ab \<Longrightarrow>\<^sub>A hn_val Id (hd a) (hd ab)"
  unfolding hn_ctxt_def   
  by (metis entails_def entails_pure' pair_in_Id_conv pure_app_eq) 

schematic_goal rd_hnr:
 "hn_refine emp ?C ?G ?R (rd_impl1 as)"
  unfolding rd_impl1_def
  apply(rule hnr_bind)
    apply(rule hnr_uRETURN_pure[where R=Id]) 
      apply simp

   apply(rule hnr_bind) apply simp
   apply(rule hnr_frame)
      apply(rule set_init_hnr')

     apply(simp add: entailst_def) apply(rule match_rest) apply simp

  
  apply(rule hnr_bind)

  unfolding whileT_I' WHILEIT_to_monadic     
      apply(rule hn_monadic_WHILE_aux[where Rs="\<lambda>(c1,c2,c3) (a1,a2,a3). (pure Id) c1 a1 * (pure Id) c2 a2 * rbt_map_assn' c3 a3"])
  unfolding entailst_def
          apply rotatel apply(rule match_first)
          apply(rule ent_true_drop(2))
          apply rotatel apply(rule add_triv[where x=as]) 
          apply(rule hn_ctxt_triple')
  unfolding hn_ctxt_triple''

         defer

  apply simp apply(rule match_rest) apply simp

        apply(auto simp del: nres_bind_left_identity) [1]
  (* the loop body *)

  apply(rule hnr_ASSERT)
  apply(rule hnr_ASSERT)
        apply(rule hnr_ASSERT)
  apply(rule hnr_bind)

          apply(rule hnr_frame[OF hnr_uRETURN_pass])   
  apply(simp add: entailst_def)
          apply(rule ent_true_drop(2))
  apply rotater
          apply(rule isolate_first)
  using hd_entails
  apply(rule hd_entails)



end