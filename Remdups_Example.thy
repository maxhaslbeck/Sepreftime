theory Remdups_Example
  imports Set_Impl    

begin

 
subsection "remdups"

fun remdups' where
  "remdups' ac [] = ac"
| "remdups' ac (x#xs) = (if x\<in>set ac then remdups' ac xs 
                                       else remdups' (ac@[x]) xs)"

fun remdups2 where
  "remdups2 ac S [] = ac"
| "remdups2 ac S (x#xs) = (if x\<in>set ac then remdups' ac xs 
                                       else remdups' (ac@[x]) xs)"


definition rd_t :: "nat\<Rightarrow>nat" where
  "rd_t n = set_init_t + n * (set_ins_t n + set_mem_t n + 0 + 0 + 0 + 10)"

definition "rd_SPEC as \<equiv> SPECT [remdups' [] as \<mapsto> rd_t (length as)]"
 


definition rd_impl1 :: "nat list \<Rightarrow> (nat list) nrest" where
  "rd_impl1 as = do {
          ys \<leftarrow> RETURNT [];
          S \<leftarrow> set_init_SPEC;
          zs \<leftarrow> RETURNT as;
          (zs,ys,S) \<leftarrow> whileT (\<lambda>(xs,ys,S). length xs > 0)
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

(*

definition rd_impl1 :: "nat list \<Rightarrow> (nat list) nrest" where
  "rd_impl1 as = do {
          ys \<leftarrow> RETURNT [];
          S \<leftarrow> set_init_SPEC;
          zs \<leftarrow> RETURNT as;
          St' \<leftarrow> RETURNT (ys,S);
          St \<leftarrow> RETURNT (zs,St');
          End \<leftarrow> whileT (\<lambda>(xs,ys,S). length xs > 0)
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
  } ) }) St;
            End' \<leftarrow> RETURNT (snd End);
            RETURNT (fst End)
      }"
*)



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
  unfolding hn_ctxt_def by simp  



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

lemma hn_refine_length: " hn_refine (hn_val Id xs' xs)
           (ureturn (length xs))
       (hn_val Id xs' xs)
       (pure Id) (RETURNT (length xs'))"
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
  subgoal   sorry
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
  using forward_ent left_move_back by blast
 
lemma underA: "A \<Longrightarrow>\<^sub>A A' \<Longrightarrow> A \<or>\<^sub>A B \<Longrightarrow>\<^sub>A A' \<or>\<^sub>A B"
    using ent_disjE ent_disjI1_direct ent_disjI2_direct ent_trans by blast

lemma underB: "B \<Longrightarrow>\<^sub>A B' \<Longrightarrow> A \<or>\<^sub>A B \<Longrightarrow>\<^sub>A A \<or>\<^sub>A B'"
  using ent_disjE ent_disjI1_direct ent_disjI2_direct ent_trans by blast 


definition "asd = (\<lambda>x y. true)"
lemma U: "hn_val Id a b \<Longrightarrow>\<^sub>A hn_ctxt asd a b"
  by(auto simp: hn_ctxt_def asd_def)
schematic_goal "hn_val Id a b \<Longrightarrow>\<^sub>A hn_ctxt asd a (?p927 b)"
  apply (rule U) oops

schematic_goal "hn_ctxt (\<lambda>x y. true) a b \<Longrightarrow>\<^sub>A hn_ctxt ?R a b"
  by(rule entails_triv)

schematic_goal "hn_ctxt asd a b \<Longrightarrow>\<^sub>A hn_ctxt asd a ?x"
  apply (rule entails_triv)
  thm entails_triv oops

schematic_goal "hn_ctxt asd a b \<Longrightarrow>\<^sub>A hn_ctxt asd a (?x::?'a)"
  by (rule entails_triv)

schematic_goal "hn_ctxt (pure Id) a a1a \<Longrightarrow>\<^sub>A hn_ctxt ?R a (?S a1a a2a)" 
  apply(rule entails_triv) oops
 

lemma b: "RETURNT (case s' of (xs, ys, S) \<Rightarrow> 0 < length xs)
    = (case s' of (xs, ys, S) \<Rightarrow> do { x \<leftarrow> RETURNT 0; y \<leftarrow> RETURNT (length xs); RETURNT (x < y) })"
  apply auto unfolding RETURNT_def by(auto simp: prod.case_distrib)  

thm invalid_pure_recover
lemma invalid_pure_recover': "hn_invalid (pure Id) a1'a a1a
      = hn_ctxt (pure Id) a1'a a1a * true"
  unfolding hn_ctxt_def by(simp add: invalid_pure_recover)

schematic_goal rd_hnr:
  "hn_refine emp (?C::?'a Heap) ?G ?R (rd_impl1 as)" using [[goals_limit = 3]]
  unfolding rd_impl1_def
  apply(rule hnr_bind)
    focus (* line 1 *)
      apply(rule hnr_uRETURN_pure[where R=Id]) 
      apply simp
    solved
 
  apply(rule hnr_bind)
    focus (* line 2 *) 
      apply simp
      apply(rule hnr_frame)
      apply(rule set_init_hnr')

     apply(simp add: entailst_def) apply(rule match_rest) apply simp
    solved
  
  apply(rule hnr_bind)
    focus (* line 3 *)
      apply(rule hnr_frame[OF hnr_uRETURN_pure[where R=Id]]) apply simp
      apply(simp) apply(rule entt_refl)
    solved

  apply(rule hnr_bind)
    focus (* the while loop *)
    unfolding whileT_I' unfolding WHILEIT_to_monadic     
(*      apply(rule hn_monadic_WHILE_aux[where Rs="\<lambda>(c1,c2,c3) (a1,a2,a3). (pure Id) c1 a1 * (pure Id) c2 a2 * rbt_map_assn' c3 a3"])
  unfolding entailst_def
          apply rotatel apply(rule match_first)
          apply(rule ent_true_drop(2))
          apply rotatel apply(rule add_triv[where x=as]) 
          apply(rule hn_ctxt_triple')
  unfolding hn_ctxt_triple''
 *) 
    apply(rule hn_monadic_WHILE_aux[where \<Gamma>="emp" and Rs="pure (Id) \<times>\<^sub>a  (pure (Id) \<times>\<^sub>a  rbt_map_assn')"])
    focus (* WHILE: precondition *)
  unfolding entailst_def apply(simp  )
           apply(rule ent_true_drop(2))  
           apply(subst hn_ctxt_prod_split'') prefer 2
            apply(subst hn_ctxt_prod_split'') prefer 2
      apply rotater apply(rule match_first)  apply(rule match_first)  apply(rule entails_triv)
      apply (rule refl) apply (rule refl)
    solved
    focus  (* WHILE: loop guard *)
      unfolding b
      (* split case_prod *)
      apply(rule hn_case_prod')
      focus (* 1st prod frame *)
           unfolding entailst_def  apply rotatel apply(rule match_first)
          apply(rule match_rest) apply simp
      solved
      apply(rule hn_refine_cons_post')
      apply(rule hn_case_prod')
      focus (* 2nd prod frame *) 
      unfolding entailst_def  apply rotatel  apply(rule match_first)
           apply(rule match_rest) apply simp
      solved 
      (* While: guard: code *)
       focus

      apply(rule hnr_bind) (* bind Wg1 *)
      focus (* While: guard: first return *)
      apply(rule hnr_frame[OF hnr_uRETURN_pure[where R=Id]])
       apply simp
      unfolding entailst_def apply rotater apply rotatel apply rotatel apply (rule match_first)
      apply rotater 
           apply(rule ent_true_drop(2)) 
      apply(rule entails_triv)
      solved

      apply(rule hnr_bind) (* bind Wg2 *)
      focus (* While: guard: second return *)
      apply(rule hnr_frame[OF hn_refine_length])
        apply simp apply (simp add: entailst_def)
      apply(rule ent_true_drop(2)) 
      apply rotatel apply rotater apply(rule match_first)
      apply (rule entails_triv)
      solved
      
      focus (* While: guard: less *)
      apply(rule hnr_frame[OF hn_refine_less])
  apply (simp add: entailst_def)
      apply(rule ent_true_drop(2)) 
      apply rotater apply rotatel apply rotatel apply rotatel apply rotatel apply rotatel apply rotatel
      apply (rule match_first)  apply rotatel  apply rotatel  apply rotatel
      apply (rule match_first)
      apply (rule entails_triv)
      solved
      
      focus (* IMP of bind Wg2 *)
        apply (simp add: entailst_def)   
      apply(rule ent_true_drop(2)) 
      apply rotater   apply rotatel      apply rotatel apply rotatel apply rotatel                  
      apply rotatel     apply(rule match_first) apply(rule entails_triv)
      solved

      focus (* IMP of bind Wg1 *)
      apply rotater  apply rotater apply rotater  apply rotater
      apply (rule match_first) apply rotatel apply rotatel
      apply rotater apply rotater apply rotater apply (rule match_first)
      apply rotater apply rotater  apply (rule match_first)
      apply(rule addemp_triv)
      apply rotatel apply (rule match_first)
      apply(rule ent_true_drop(2)) apply simp apply (rule entails_triv)
      solved
      solved 

      apply rotatel apply rotatel apply (rule match_first) apply (rule match_first)
      apply (rule match_rest)  
      apply(rule ent_true_drop(2)) apply (rule entails_triv)
      solved (* WHILE: loop guard *)

      focus (* While : guard frame *)
      apply(simp add: entailst_def)
      apply(rule ent_true_drop(2))  
      apply(rule entails_triv)
      solved
  

   focus (* WHILE: the loop body *)
      apply(rule hn_case_prod')     
      focus (* 1st prod frame *)
          unfolding entailst_def
          apply rotatel apply(rule match_first) apply(rule match_rest) apply simp
      solved
          apply(rule hn_refine_cons_post')
          focus (* post R *)
          apply(rule hn_case_prod')  
      focus (* 2nd prod frame *)
          unfolding entailst_def
          apply rotatel  apply (rule match_first) apply(rule ent_true_drop_fst) apply(rule ent_true_drop(2))
          apply (rule entails_triv) 
      solved 
      focus (* code *)   
        apply(rule hnr_ASSERT)
        apply(rule hnr_ASSERT)
        apply(rule hnr_ASSERT) 

       apply(rule hnr_bind[where Rh="pure Id"])  (* bind Wb1 *)
      focus (* the hd operation *)
          apply(rule hnr_frame[OF hn_refine_hd])   
            apply(simp add: entailst_def) apply rotatel apply rotatel apply rotatel apply rotater apply (rule match_first)
  apply rotater 
            apply(rule ent_true_drop(2)) apply (rule entails_triv)
     solved (* the hd operation *)

     focus (* prog after hd *)
       apply(rule hnr_bind[where Rh="pure Id"])  (* bind Wb2 *)
      focus (* the tl operation *)
          apply(rule hnr_frame[OF hn_refine_tl])   
             apply(simp add: entailst_def mult.assoc) apply rotater apply rotatel apply rotatel    apply rotatel  apply rotatel
                apply (rule match_first)
  apply rotater 
            apply(rule ent_true_drop(2)) apply (rule entails_triv)
      solved (* the tl operation *)

     focus (* prog after tl *)
    apply(rule hnr_bind )     (* bind Wb3 *)
    focus (* the \<in> operation *)
      apply(rule hnr_frame)
               apply(rule set_mem_hnr') 
        apply(simp add: entailst_def)
            apply(rule ent_true_drop(2)) 
              apply rotater   apply rotatel apply rotatel apply rotatel
          apply(rule isolate_first) apply(simp add: hn_ctxt_def) apply(rule entails_triv)
             apply rotatel apply rotatel apply rotatel
          apply(rule match_first)
              apply (rule entails_triv)
      solved (* the \<in> operation *)

     focus (* prog after \<in> *)
      focus (* the if Block *)
             apply(rule hnr_If')
                apply rotater apply rotatel apply rotatel apply rotatel apply rotatel apply rotatel apply rotatel apply rotatel
                apply(rule isolate_first)
  apply(simp add: hn_ctxt_def Y'_def pure_def   )    
                 apply(rule entails_triv) 
  apply rotater 
            apply(rule ent_true_drop(2)) 
                apply (rule entails_triv)

      focus (* 1st if-branch (element already in list ) *)
               apply(rule hnr_frame) 
                apply(rule hnr_uRETURN_pass)

  
               apply(simp add: entailst_def)
  apply rotater apply rotatel apply swapl apply swapl
  apply swapl apply swapl  apply swapl apply swapl  
               apply swapl apply swapl  apply swapl apply takel apply takel 
  apply(rule isolate_first)
                apply(simp add:  gr_def     ) 
                apply(subst hn_ctxt_prod_split'') prefer 2
  apply(simp add: mult.assoc) apply rotatel
  apply(rule match_first)
                apply(subst hn_ctxt_prod_split'') prefer 2 apply rotatel
  apply(rule match_first) apply(simp add: hn_ctxt_def) apply(rule entails_triv)
  apply simp apply simp
  apply rotater 
            apply(rule ent_true_drop(2)) 
                apply (rule entails_triv)
      solved (* 1st if-branch *)

      focus  (* 2nd if-branch (element should be added ) *)

  apply (rule hnr_bind)
  (* \<rightarrow> add element into Set *)
  apply (rule hnr_frame)
  apply(rule set_ins_hnr')
                apply(simp add: entailst_def)
            apply(rule ent_true_drop(2)) 
                apply rotater apply rotatel apply rotatel apply rotatel apply rotatel apply rotatel
            apply(rule match_first) 
                apply(rule match_first) 
                apply (rule entails_triv)

               apply (rule hnr_bind)
  (* \<rightarrow> append element *)

  apply (simp)
  apply (rule hnr_frame)
  apply(rule hnr_cons_rule)
                apply(simp add: entailst_def)
            apply(rule ent_true_drop(2)) 
                 apply rotater apply taker apply rotatel apply rotatel apply swapl apply swapl
                 apply swapl  apply takel apply (rule isolate_first)
                  apply(simp add: gr_def)  apply (rule match_first)
                  apply (rule entails_triv) apply(rule entails_triv)

  (* \<rightarrow> return result *)
  apply (rule hnr_frame)
                 apply(rule hnr_uRETURN_pass)

               apply(simp add: entailst_def)
            apply(rule ent_true_drop(2)) 
                apply rotater apply rotatel apply rotatel apply rotatel apply rotatel apply rotatel
                apply swapl   apply swapl apply takel apply takel
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
      solved (* 2nd if-branch *)

            apply(rule ent_true_drop(2)) 
             apply(rule entails_triv)
  solved (* the if Block *)
  solved (* prog after \<in> *)

  focus (* IMP of bind Wb3: merge the heap or *)
          unfolding mult.assoc
            apply(rule addemp_triv)
            apply(rule ent_trans[OF or_merge_rotatel])
  apply(simp only: mult.assoc) 
            apply(rule ent_trans[OF or_merge_succ_step]) 
            apply(rule ent_trans[OF or_merge_succ_step]) 
            apply(rule ent_trans[OF or_merge_succ_step])  
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
              apply(simp add:   invalid_pure_recover')
  apply(rule underB)
              apply(rule addemp_triv) apply rotatel
               apply(rule entails_triv) 
  apply(simp only: mult.assoc)
             apply(rule ent_trans[OF or_merge_succ_step]) 
             apply(rule entails_triv)  

            apply(rule forward_ent_snd)
            apply(rule forward_ent_snd)
              apply(rule entails_true)
            apply(rule entails_triv)

            apply rotater
  apply(simp add: gr_def mult.assoc)
            apply(rule isolate_first)
             apply(simp add: hn_ctxt_def pure_def) apply(rule entails_triv)
  apply rotater
  apply rotatel  apply rotatel  apply rotatel  apply rotatel  apply rotatel apply rotatel
            apply(rule ent_true_drop_fst)
            apply(rule ent_true_drop(2))
            apply(rule entails_triv)
  solved (* IMP of bind Wb3: merge the heap or *)
  solved (* prog after tl *)

  focus (* IMP of bind Wb2 *)

  (* after *) 
  apply rotater apply rotatel apply rotatel apply rotatel apply rotatel 
  apply(rule match_first) 
  apply rotater 
            apply(rule ent_true_drop(2))
           apply(rule entails_triv)
  solved (* IMP of bind Wb2 *)
  solved (* prog after hd *)                                

          focus (* IMP of bind Wb1 *)
          unfolding mult.assoc
            apply(rule match_first)
              apply rotater 
            apply(rule match_first) apply rotater   
          apply rotatel apply rotatel apply(rule match_first)    

          apply(rule forward_ent[OF entails_true])
          apply rotater apply(rule isolate_first)
          apply(simp add: hn_ctxt_def) apply(rule entails_triv)
 
            apply(rule ent_true_drop(2))
          apply(rule entails_triv)
          solved (* IMP of bind Wb1 *)
          solved  (* code *)  
          solved  (* post R *)
          focus (* post I *)
            apply rotater apply(rule match_first)
            apply rotater apply rotater apply rotater
              apply(rule addemp_triv) apply rotatel apply(rule match_first)
            apply(rule addemp_triv) apply(rule isolate_first)
            apply(simp add: hn_ctxt_def) apply(rule entails_triv)
              apply(rule ent_true_drop(2))
            apply(rule entails_triv)
          solved (* post I *)
  solved  (* WHILE: the loop body *)
          apply (simp add: entailst_def)
          apply(rule ent_true_drop(2))
          apply (simp add: hn_ctxt_def)
          solved (* the while loop *)

    
   focus (* finally return result *)

      (* split case_prod *)
      apply(rule hn_case_prod')
      focus (* 1st prod frame *)
           unfolding entailst_def  apply rotatel apply rotatel apply(rule isolate_first)
           apply(rule entails_triv)
                  apply(rule match_rest) apply simp
      solved
      apply(rule hn_refine_cons_post')
      apply(rule hn_case_prod')
      focus (* 2nd prod frame *)
      unfolding entailst_def  apply rotatel apply(rule match_first)
           apply(rule match_rest) apply simp
      solved 

  
      apply(rule hn_refine_cons_post')
       apply(rule hnr_frame)  
         apply(rule hnr_uRETURN_pass) unfolding entailst_def mult.assoc
        apply rotater apply(rule isolate_first)  
      (* shit happening here *)apply(rule entails_triv)  
      apply rotater  apply(rule match_rest) apply simp

      unfolding mult.assoc
       apply rotater apply(rule match_first) 
       apply rotatel apply rotatel apply rotatel apply rotatel apply (rule match_first)
       apply rotater  apply rotater apply(rule match_first)
       apply(rule match_rest) apply simp

      apply rotater apply(rule match_first)
      apply rotatel apply rotatel apply (rule match_first)
      apply rotater apply rotater apply (rule match_first)
      apply (rule match_rest) apply simp
  solved (* finally return result *)

      unfolding mult.assoc apply rotater apply (rule match_first)
         apply rotater apply (rule match_rest) apply simp
      apply rotatel
      apply simp
        apply(rule ent_trans[OF hn_invalid_prod_split])
        apply rotater apply(rule match_first)
        apply rotater apply(rule match_rest) apply simp

       apply(rule ent_trans[OF hn_invalid_prod_split])
       apply rotatel apply rotater apply (rule match_first)
       apply rotater apply(rule match_rest) apply simp

      apply rotater 
      apply(rule addemp_triv)
      apply rotatel apply(rule match_first)
      apply rotater apply(rule match_rest) apply simp
        

      done
 

notepad begin
  fix as :: "nat list"
  let ?P = "\<lambda>as.  ureturn [] \<bind>
                     (\<lambda>x'. tree_empty \<bind>
                           (\<lambda>x'a. ureturn as \<bind>
                                  (\<lambda>x'b. heap_WHILET (\<lambda>s. case s of (a1, a1a, a2a) \<Rightarrow> ureturn 0 \<bind> (\<lambda>x'c. ureturn (length a1) \<bind> (\<lambda>x'd. ureturn (x'c < x'd))))
                                          (\<lambda>s. case s of
                                               (a1, a1a, a2a) \<Rightarrow>
                                                 ureturn (hd a1) \<bind>
                                                 (\<lambda>x'c. ureturn (tl a1) \<bind>
                                                        (\<lambda>x'd. RBTree_Impl.rbt_search x'c a2a \<bind>
                                                               (\<lambda>x'e. if x'e = Some () then ureturn (x'd, a1a, a2a)
                                                                      else RBTree_Impl.rbt_insert x'c () a2a \<bind> (\<lambda>x'f. ureturn (x'c # a1a) \<bind> (\<lambda>x'g. ureturn (x'd, x'g, x'f)))))))
                                          (x'b, x', x'a) \<bind>
                                         (\<lambda>x'c. case x'c of
                                                (a1, a1a, a2a) \<Rightarrow> ureturn a1a))))"

  from   extract_cost_ub[OF hnr_refine[OF rd_impl1_refines rd_hnr, unfolded rd_SPEC_def], where Cost_ub="rd_t (length as)", of as]
  have 1: " <$(rd_t (length as))> ?P as <\<lambda>r. emp * (\<exists>\<^sub>Ara. pure Id ra r * \<up> (ra = remdups' [] as))>\<^sub>t" by simp

  have " <$(rd_t (length as))> ?P as <\<lambda>r. \<up> (r = remdups' [] as)>\<^sub>t" apply(rule post_rule) 
    apply(rule 1) 
    apply (auto simp add: pure_def)  
    by (metis (mono_tags, lifting) entail_equiv_backward entails_ex entails_frame entails_pure)



end

end