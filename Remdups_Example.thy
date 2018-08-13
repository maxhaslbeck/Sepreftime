theory Remdups_Example
imports HNR_While "SepLogicTime_RBTreeBasic.RBTree_Impl" DataRefinement 
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
  "hn_refine (rbt_map_assn' S p) (rbt_insert x' () p) emp rbt_map_assn' (set_ins_SPEC x S)"
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

definition Y' :: "bool \<Rightarrow> unit option \<Rightarrow> assn" where
  "Y' b v = \<up>(  v = Some () \<longleftrightarrow> b )"
 
lemma set_mem_hnr':
  "hn_refine (rbt_map_assn' S p) (rbt_search (x'::nat) p) (rbt_map_assn' S p) Y' ( (set_mem_SPEC x S))"
  sorry 


subsection "remdups"

fun rd_t :: "nat\<Rightarrow>nat" where "rd_t n = n * (set_ins_t n + set_mem_t n + 0 + 0 + 0 + 10)"

definition "rd_SPEC as \<equiv> SPECT [remdups as \<mapsto> rd_t (length as)]"



definition rd_impl1 :: "nat list \<Rightarrow> (nat list) nrest" where
  "rd_impl1 as = do {
          ys \<leftarrow> RETURNT [];
          S \<leftarrow> set_init_SPEC;
          zs \<leftarrow> RETURNT as;
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
            ys \<leftarrow> RETURNT (x#ys); (* SPECT [x#ys\<mapsto> 10]; *)
            RETURNT (xs,ys,S)
  } ) }) (zs,ys,S);
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
  "hn_val Id (a::nat list) ab \<Longrightarrow>\<^sub>A hn_ctxt (pure Id) (hd a) (hd ab)"
  unfolding hn_ctxt_def   
  by (metis entails_def entails_pure' pair_in_Id_conv pure_app_eq) 



lemma zuf: "\<up> True * true =  true"  
  by (simp add: abel_semigroup.commute assn_ext mult.abel_semigroup_axioms)  


lemma [simp]: "h\<Turnstile>\<up>b \<longleftrightarrow> (h\<Turnstile>emp \<and> b)" 
  using one_assn_rule pure_assn_rule by auto 

lemma hn_refine_hd: " hn_refine (hn_val Id s' s)
           (ureturn (hd s))
       (hn_val Id s' s)
       (pure Id) (RETURNT (hd s'))"
  unfolding hn_refine_def apply (auto simp: zuf mult.assoc  execute_ureturn pure_def hn_ctxt_def)
   apply(rule exI[where x=0]) apply (auto simp: zero_enat_def relH_def )      
    using models_in_range top_assn_rule  
    by (metis (full_types) mod_false zuf)  


lemma hn_refine_tl: " hn_refine (hn_val Id s' s)
           (ureturn (tl s))
       (hn_val Id s' s)
       (pure Id) (RETURNT (tl s'))"
  unfolding hn_refine_def apply (auto simp: zuf mult.assoc  execute_ureturn pure_def hn_ctxt_def)
   apply(rule exI[where x=0]) apply (auto simp: zero_enat_def relH_def )      
    using models_in_range top_assn_rule  
    by (metis (full_types) mod_false zuf)  


lemma hnr_cons_rule: " hn_refine (hn_val Id xs' xs * hn_val Id x' x)
           (ureturn (x#xs))
       (hn_val Id xs' xs * hn_val Id x' x)
       (pure Id) (RETURNT (x'#xs'))"
  unfolding hn_refine_def apply (auto simp: zuf mult.assoc  execute_ureturn pure_def hn_ctxt_def)
   apply(rule exI[where x=0]) apply (auto simp: zero_enat_def relH_def )      
  using models_in_range top_assn_rule by blast 

lemma hn_refine_less: " hn_refine (hn_val nat_rel s' s * hn_val nat_rel x' x)
           (ureturn (x < s))
       (hn_val nat_rel s' s * hn_val nat_rel x' x)
       (pure bool_rel) (RETURNT (x' < s'))"
  unfolding hn_refine_def apply (auto simp: zuf mult.assoc  execute_ureturn pure_def hn_ctxt_def)
   apply(rule exI[where x=0]) apply (auto simp: zero_enat_def relH_def )      
    using models_in_range top_assn_rule by blast 


lemma manual1: "
  hn_val Id a ab \<Longrightarrow>\<^sub>A hn_val Id a (XX x' x'a (fst s) (fst (snd s)) (snd (snd s))) \<Longrightarrow>
   XX = (\<lambda>x' x'a ab ac ba. X x' x'a (ab, ac, ba)) \<Longrightarrow>
hn_val Id a ab \<Longrightarrow>\<^sub>A hn_val Id a (X x' x'a s)" by auto

schematic_goal "f a = f (?X (a,b,c))"
  by simp

schematic_goal "hn_val Id a ab \<Longrightarrow>\<^sub>A hn_val Id a (?S x' x'a (ab, ac, ba))"
  apply(rule entails_triv)      done

schematic_goal "\<And>ab ac ba. f ab = f (?S (ab, ac, ba))"
  apply(rule refl)      oops

lemma rewr: "P (S' a b c) \<Longrightarrow> S' = (\<lambda>a b c. S (a,b,c)) \<Longrightarrow> P (S (a,b,c))"
  by auto


schematic_goal "\<And>ab ac ba. f ab = f (?S (ab, ac, ba))"
  apply(rule rewr )
  apply(rule refl) apply sim      oops

schematic_goal "\<And>x x' xa x'a a aa b ab ac ba.
       RETURNT x \<le> RETURNT [] \<Longrightarrow>
       RETURNT xa \<le> set_init_SPEC \<Longrightarrow> a \<noteq> [] \<Longrightarrow> length a + length aa \<le> length as \<Longrightarrow> card b \<le> length aa \<Longrightarrow> hn_val Id a ab \<Longrightarrow>\<^sub>A hn_val Id a (?s73 x' x'a (ab, ac, ba))"
  apply(rule entails_triv)      oops


subsection \<open>Product Types\<close>
text \<open>Some notion for product types is already defined here, as it is used 
  for currying and uncurrying, which is fundamental for the sepref tool\<close>
definition prod_assn :: "('a1\<Rightarrow>'c1\<Rightarrow>assn) \<Rightarrow> ('a2\<Rightarrow>'c2\<Rightarrow>assn) 
  \<Rightarrow> 'a1*'a2 \<Rightarrow> 'c1*'c2 \<Rightarrow> assn" where
  "prod_assn P1 P2 a c \<equiv> case (a,c) of ((a1,a2),(c1,c2)) \<Rightarrow>
  P1 a1 c1 * P2 a2 c2"


notation prod_assn (infixr "\<times>\<^sub>a" 70)
  
lemma prod_assn_pure_conv[simp]: "prod_assn (pure R1) (pure R2) = pure (R1 \<times>\<^sub>r R2)"
  by (auto simp: pure_def prod_assn_def pure_conj intro!: ext)

lemma prod_assn_pair_conv[simp]: 
  "prod_assn A B (a1,b1) (a2,b2) = A a1 a2 * B b1 b2"
  unfolding prod_assn_def by auto

lemma prod_assn_true[simp]: "prod_assn (\<lambda>_ _. true) (\<lambda>_ _. true) = (\<lambda>_ _. true)"
  by (auto intro!: ext simp: hn_ctxt_def prod_assn_def)


lemma prod_assn_ctxt: "prod_assn A1 A2 x y = z \<Longrightarrow> hn_ctxt (prod_assn A1 A2) x y = z"
  by (simp add: hn_ctxt_def)

lemma hn_case_prod':
  assumes FR: "\<Gamma>\<Longrightarrow>\<^sub>thn_ctxt (prod_assn P1 P2) p' p * \<Gamma>1"
  assumes Pair: "\<And>a1 a2 a1' a2'. \<lbrakk>p'=(a1',a2')\<rbrakk> 
    \<Longrightarrow> hn_refine (hn_ctxt P1 a1' a1 * hn_ctxt P2 a2' a2 * \<Gamma>1 * hn_invalid (prod_assn P1 P2) p' p) (f a1 a2) 
          (hn_ctxt P1' a1' a1 * hn_ctxt P2' a2' a2 * hn_ctxt XX1 p' p * \<Gamma>1') R (f' a1' a2')"
  shows "hn_refine \<Gamma> (case_prod f p) (hn_ctxt (prod_assn P1' P2') p' p * \<Gamma>1')
    R (case_prod (\<lambda>a b. f' a b) p')" (is "?G \<Gamma>")
    apply1 (rule hn_refine_cons_pre[OF FR])
    apply1 extract_hnr_invalids
    apply1 (cases p; cases p'; simp add: prod_assn_pair_conv[THEN prod_assn_ctxt])
    apply (rule hn_refine_cons[OF _ Pair _ entt_refl])
  subgoal
    apply (simp add: hn_ctxt_def entailst_def)
          apply(rule ent_true_drop(2))
          apply(rule ent_true_drop(2)) apply(rule entails_triv) done
    applyS simp
      subgoal
        apply  (simp add: hn_ctxt_def entailst_def mult.assoc)
    apply(rule match_first)
    apply(rule match_first) apply(rotatel)
    apply(rule match_first)  by simp
      done

    term "pure (Id) \<times>\<^sub>a  pure (Id) \<times>\<^sub>a  rbt_map_assn'"
  (* nat list \<times> nat list \<times> nat set \<Rightarrow> ?'a23 \<Rightarrow> assn *)

lemma hn_ctxt_prod_split: "hn_ctxt (A \<times>\<^sub>a B) (a, b) (a', b') = hn_ctxt A a a' * hn_ctxt B b b'"
  by (simp add: prod_assn_def hn_ctxt_def)

lemma hn_ctxt_prod_split': "hn_ctxt (A \<times>\<^sub>a B) (a, b) s' = hn_ctxt A a (fst s') * hn_ctxt B b (snd s')"
  by (simp add: prod_assn_def hn_ctxt_def  case_prod_beta')  

lemma hn_ctxt_prod_split'': "s'=(a',b') \<Longrightarrow> hn_ctxt (A \<times>\<^sub>a B) (a, b) s' = hn_ctxt A a a' * hn_ctxt B b b'"
  by (simp add: prod_assn_def hn_ctxt_def  case_prod_beta')  

lemma t: "true = true * true"  
  by simp  

lemma or_merge: "((B1 * C1) \<or>\<^sub>A (B1 * C2)) = (B1) * (C1 \<or>\<^sub>A C2)"
  apply(rule ent_iffI)
  subgoal  by (simp add: ent_disjE match_first) 
  subgoal sledgehammer sorry
  oops
lemma "A * ((B1 * C1) \<or>\<^sub>A (B1 * C2)) = (A * B1) * (C1 \<or>\<^sub>A C2)"
  apply (simp add: assn_times_assoc or_merge)
  oops

lemma or_merge: "((B1 * C1) \<or>\<^sub>A (B1 * C2)) \<Longrightarrow>\<^sub>A (B1) * (C1 \<or>\<^sub>A C2)" 
  by (simp add: ent_disjE match_first) 

lemma or_merge_succ_step: "A * ((B1 * C1) \<or>\<^sub>A (B1 * C2)) \<Longrightarrow>\<^sub>A gr A B1 * (C1 \<or>\<^sub>A C2)"
  apply (simp add: assn_times_assoc gr_def )
  apply(rule match_first) using or_merge by auto

lemma or_merge_rotatel: "A * ((B1 * C1) \<or>\<^sub>A (B2 * C2)) \<Longrightarrow>\<^sub>A A * ((C1 * B1) \<or>\<^sub>A (B2 * C2))"
  apply(rule match_first)  
  by (simp add: assn_times_comm entails_triv)
lemma or_merge_rotater: "A * ((B1 * C1) \<or>\<^sub>A (B2 * C2)) \<Longrightarrow>\<^sub>A A * ((B1 * C1) \<or>\<^sub>A (C2 * B2))"
  apply(rule match_first)  
  by (simp add: assn_times_comm entails_triv)
 
lemma addemp_triv: "emp * A \<Longrightarrow>\<^sub>A B \<Longrightarrow> A \<Longrightarrow>\<^sub>A B"
  by simp 

lemma invalid_pure_recover: "invalid_assn (pure R) x y = pure R x y * true"
  apply (rule ent_iffI) 
  subgoal
    apply (rule entailsI)
    unfolding invalid_assn_def
    by (auto simp: pure_def assn_times_comm) 
  subgoal
    unfolding invalid_assn_def
    apply (auto simp: pure_def) 
    using entailsI entails_frame by fastforce 
  done    

lemma hn_invalid_prod_split: "hn_invalid (A \<times>\<^sub>a B) (a, b) (a', b')
      \<Longrightarrow>\<^sub>A hn_invalid A a a' * hn_invalid B b b'" 
  apply(auto simp: hn_ctxt_def invalid_assn_def  )
  by (smt SepLogic_Misc.mod_pure_star_dist entails_def merge_true_star mod_starD mult.left_commute mult_commute_abs) 

lemma forward_ent: "A \<Longrightarrow>\<^sub>A A' \<Longrightarrow> A' * B \<Longrightarrow>\<^sub>A C \<Longrightarrow> A * B \<Longrightarrow>\<^sub>A C"
  using entails_frame' by blast 

lemma forward_ent_snd: "B \<Longrightarrow>\<^sub>A B' \<Longrightarrow> A * B' \<Longrightarrow>\<^sub>A C \<Longrightarrow> A * B \<Longrightarrow>\<^sub>A C"
  sorry
 
lemma underA: "A \<Longrightarrow>\<^sub>A A' \<Longrightarrow> A \<or>\<^sub>A B \<Longrightarrow>\<^sub>A A' \<or>\<^sub>A B"
  sorry

   

schematic_goal rd_hnr:
 "hn_refine emp ?C ?G ?R (rd_impl1 as)" using [[goals_limit = 1]]
  unfolding rd_impl1_def
  apply(rule hnr_bind)
    apply(rule hnr_uRETURN_pure[where R=Id]) 
      apply simp

   apply(rule hnr_bind) apply simp
   apply(rule hnr_frame)
      apply(rule set_init_hnr')

     apply(simp add: entailst_def) apply(rule match_rest) apply simp

  
  apply(rule hnr_bind)
      apply(rule hnr_frame[OF hnr_uRETURN_pure[where R=Id]]) apply simp
  apply(simp) apply(rule entt_refl)


  apply(rule hnr_bind)

  unfolding whileT_I' unfolding WHILEIT_to_monadic     
(*      apply(rule hn_monadic_WHILE_aux[where Rs="\<lambda>(c1,c2,c3) (a1,a2,a3). (pure Id) c1 a1 * (pure Id) c2 a2 * rbt_map_assn' c3 a3"])
  unfolding entailst_def
          apply rotatel apply(rule match_first)
          apply(rule ent_true_drop(2))
          apply rotatel apply(rule add_triv[where x=as]) 
          apply(rule hn_ctxt_triple')
  unfolding hn_ctxt_triple''
 *) 
     apply(rule hn_monadic_WHILE_aux[where Rs="pure (Id) \<times>\<^sub>a  (pure (Id) \<times>\<^sub>a  rbt_map_assn')"])
  unfolding entailst_def apply(simp  )
           apply(rule ent_true_drop(2)) apply(rotater)
          apply(rule ent_true_drop(2))
           apply(subst hn_ctxt_prod_split'') prefer 2
            apply(subst hn_ctxt_prod_split'') prefer 2
             apply rotater apply(rule match_first)  apply(rule match_first)  apply(rule entails_triv) apply simp
           apply simp
    (* loop guard *)
  defer 
  apply(rule match_rest) apply simp

   (* the loop body *)
   apply(rule hn_case_prod')        
    apply(simp add: entailst_def  )
          apply rotatel apply(rule match_first) apply(rule match_rest) apply simp

         apply(rule hn_refine_cons_post'[OF hn_case_prod'])
           apply(simp add: entailst_def  )
           apply rotatel  apply (rule match_first)
  apply rotater apply (rule match_first) apply (rule entails_triv) 
         
  apply(rule hnr_ASSERT)
  apply(rule hnr_ASSERT)
          apply(rule hnr_ASSERT) 
  (* the hd operation *)
  apply(rule hnr_bind[where Rh="pure Id"]) 
          apply(rule hnr_frame[OF hn_refine_hd])   
            apply(simp add: entailst_def) apply rotatel apply rotatel apply rotatel apply rotater apply (rule match_first)
  apply rotater 
            apply(rule ent_true_drop(2)) apply (rule entails_triv)
  (* the tl operation *)
  apply(rule hnr_bind[where Rh="pure Id"]) 
          apply(rule hnr_frame[OF hn_refine_tl])   
             apply(simp add: entailst_def mult.assoc) apply rotater apply rotatel apply rotatel    apply rotatel  apply rotatel
                apply (rule match_first)
  apply rotater 
            apply(rule ent_true_drop(2)) apply (rule entails_triv)
  (* the \<in> operation *)
  apply(rule hnr_bind )              
  apply(rule hnr_frame)
               apply(rule set_mem_hnr') 
  apply(simp add: entailst_def)
            apply(rule ent_true_drop(2)) 
              apply rotater   apply rotatel apply rotatel apply rotatel
              apply(rule isolate_first) apply(simp add: hn_ctxt_def) apply(rule entails_triv)
              apply (rule entails_triv)

  (* the if Block *)
             apply(rule hnr_If')
                apply rotater apply rotatel apply rotatel apply rotatel apply rotatel apply rotatel apply rotatel apply rotatel
                apply(rule isolate_first)
  apply(simp add: hn_ctxt_def Y'_def pure_def   )    
                 apply(rule entails_triv) 
  apply rotater 
            apply(rule ent_true_drop(2)) 
                apply (rule entails_triv)

  (* 1st if-branch (element already in list ) *)
               apply(rule hnr_frame) 
                apply(rule hnr_uRETURN_pass)

  
               apply(simp add: entailst_def)
  apply rotater apply rotatel apply rotatel apply swapl apply swapl
  apply swapl apply swapl  apply swapl apply swapl  
               apply swapl apply swapl  apply swapl apply takel apply takel 
  apply(rule isolate_first)
                apply(simp add:  gr_def     ) 
                apply(subst hn_ctxt_prod_split'') prefer 2
  apply(simp add: mult.assoc)
  apply(rule match_first)
                apply(subst hn_ctxt_prod_split'') prefer 2
  apply(rule match_first) apply(simp add: hn_ctxt_def) apply(rule entails_triv)
  apply simp apply simp
  apply rotater 
            apply(rule ent_true_drop(2)) 
                apply (rule entails_triv)

  (* 2nd if-branch (element should be added ) *)

  apply (rule hnr_bind)
  (* \<rightarrow> add element into Set *)
  apply (rule hnr_frame)
  apply(rule set_ins_hnr')
                apply(simp add: entailst_def)
            apply(rule ent_true_drop(2)) 
                apply rotater apply rotatel apply rotatel apply rotatel apply rotatel apply rotatel apply rotatel
  apply(rule match_first) 
                apply (rule entails_triv)

               apply (rule hnr_bind)
  (* \<rightarrow> append element *)

  apply (simp)
  apply (rule hnr_frame)
  apply(rule hnr_cons_rule)
                apply(simp add: entailst_def)
            apply(rule ent_true_drop(2)) 
                 apply rotater apply taker apply rotatel apply rotatel apply rotatel
                 apply rotatel apply swapl apply takel apply (rule isolate_first)
                  apply(simp add: gr_def) apply rotatel apply (rule match_first)
                  apply (rule entails_triv) apply(rule entails_triv)

  (* \<rightarrow> return result *)
  apply (rule hnr_frame)
                 apply(rule hnr_uRETURN_pass)

               apply(simp add: entailst_def)
            apply(rule ent_true_drop(2)) 
                apply rotater apply rotatel apply rotatel apply rotatel apply rotatel
                apply swapl apply swapl apply swapl apply takel apply takel
                apply (rule isolate_first)
  apply(simp only: gr_def)
                apply(subst hn_ctxt_prod_split'') prefer 2
  apply(simp add: mult.assoc)
  apply(rule match_first)
                apply(subst hn_ctxt_prod_split'') prefer 2
  apply(rule match_first) apply(simp add: hn_ctxt_def) apply(rule entails_triv)
  apply simp apply simp
                apply (rule entails_triv)
               apply rotatel apply rotatel apply rotatel apply rotatel apply rotatel apply rotatel
               apply rotater apply(simp add: mult.assoc) 
  apply(rule forward_ent[OF hn_invalid_prod_split]) apply rotatel
               apply(rule forward_ent[OF hn_invalid_prod_split])

  apply(simp add: mult.assoc)
               apply(rule match_first)
  apply rotater                         
            apply(rule ent_true_drop(2)) 
               apply(rule entails_triv)

            apply(rule ent_true_drop(2)) 
  apply rotater               
               apply(rule match_first) 
               apply(rule entails_triv)      

            apply(rule ent_true_drop(2)) 
             apply(rule entails_triv)

  (* merge the heap or *)
  apply(simp only: mult.assoc)
            apply(rule addemp_triv)
            apply(rule ent_trans[OF or_merge_succ_step]) 
            apply(rule ent_trans[OF or_merge_succ_step]) 
            apply(rule ent_trans[OF or_merge_succ_step]) 
            apply(rule ent_trans[OF or_merge_rotatel]) 
  apply(simp only: mult.assoc)
            apply(rule ent_trans[OF or_merge_succ_step]) 
            apply(rule ent_trans[OF or_merge_rotatel]) 
            apply(rule ent_trans[OF or_merge_rotater]) 
  apply(simp only: mult.assoc)
            apply(rule ent_trans[OF or_merge_succ_step]) 
    (* too lazy here to do the rest *)

  (* TODO: recover xd *)
            apply(rule forward_ent_snd)
             apply(rule ent_trans) apply(rule underA[OF hn_invalid_prod_split])


  apply(simp only: mult.assoc)
             apply(rule addemp_triv)
            apply(rule ent_trans[OF or_merge_succ_step])
            apply(rule forward_ent_snd)
             apply(rule ent_trans) apply(rule underA[OF hn_invalid_prod_split])
              apply(simp add: hn_ctxt_def invalid_pure_recover)
  apply(rule or_merge)
    

            apply rotater
  apply(simp add: gr_def mult.assoc)
            apply(rule isolate_first)
             apply(simp add: hn_ctxt_def pure_def) apply(rule entails_triv)
  apply rotater
            apply(rule ent_true_drop(2))
            apply(rule entails_triv)

  (* after *)
   (* recover xd *) defer
    

               apply taker
               apply(rule isolate_first)
  apply(simp only: hn_ctxt_def gr_def invalid_pure_recover)
                apply(rule match_first) apply simp
                apply (rule entails_triv)
              apply(simp add: mult.assoc)
  apply rotater 


  using hnr_cons_rule

end