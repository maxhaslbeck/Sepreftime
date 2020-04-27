theory MoreCurrAutomation
imports DataRefinementMore
begin


thm T_g_specifies_I

definition (in -) mm3 where
  "mm3 t A = (case A of None \<Rightarrow> None | Some t' \<Rightarrow> if t'\<le>t then Some (t-t') else None)"


lemma Some_le_mm3_Some_conv: "Some t \<le> mm3 t' (Some t'') \<longleftrightarrow> (t'' \<le> t' \<and> t \<le> (t' - t''))"
  by (simp add: mm3_def)
  

lemma Some_le_emb'_conv: "Some t \<le> emb' Q ft x \<longleftrightarrow> Q x \<and> t \<le> ft x"
  by (auto simp: emb'_def)

definition  whileIET :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> bool)
                           \<Rightarrow> ('a \<Rightarrow> ('a,'c::{complete_lattice,plus,zero}) nrest)
                           \<Rightarrow> 'a \<Rightarrow> ('a,'c) nrest" where
  "\<And>E c. whileIET I E b c = whileT b c"



subsection \<open>Progress prover\<close>


definition "progress m \<equiv> \<forall>s' M. m = SPECT M \<longrightarrow> M s' \<noteq> None \<longrightarrow> M s' > Some 0"
lemma progressD: "progress m \<Longrightarrow> m=SPECT M \<Longrightarrow> M s' \<noteq> None \<Longrightarrow> M s' > Some 0"
  by (auto simp: progress_def)


subsection \<open>Progress rules\<close>

named_theorems progress_rules

lemma progress_SELECT_iff: "progress (SELECT P t) \<longleftrightarrow> t > 0"
  unfolding progress_def SELECT_def emb'_def by (auto split: option.splits)

lemmas [progress_rules] = progress_SELECT_iff[THEN iffD2]

lemma progress_REST_iff: "progress (REST [x \<mapsto> t]) \<longleftrightarrow> t>0"
  by (auto simp: progress_def)

lemmas [progress_rules] = progress_REST_iff[THEN iffD2]

lemma progress_ASSERT_bind[progress_rules]: "\<lbrakk>\<Phi> \<Longrightarrow> progress (f ()) \<rbrakk> \<Longrightarrow> progress (ASSERT \<Phi>\<bind>f)"
  apply (cases \<Phi>)
   apply (auto simp: progress_def less_fun_def)
  sorry


lemma progress_SPECT_emb[progress_rules]: "t > 0 \<Longrightarrow> progress (SPECT (emb P t))" by(auto simp: progress_def emb'_def)


lemma Sup_Some: "Sup (S::enat option set) = Some e \<Longrightarrow> \<exists>x\<in>S. (\<exists>i. x = Some i)"
  unfolding Sup_option_def by (auto split: if_splits)

lemma progress_bind[progress_rules]: assumes "progress m \<or> (\<forall>x. progress (f x))"
  shows "progress (m\<bind>f)"
  sorry

method progress methods solver = 
  (rule asm_rl[of "progress _"] , (simp add: le_fun_def less_fun_def split: prod.splits | intro allI impI conjI | determ \<open>rule progress_rules\<close> | rule disjI1; progress \<open>solver\<close>; fail | rule disjI2; progress \<open>solver\<close>; fail | solver)+) []


subsection \<open>VCG splitter\<close>



ML \<open>

  structure VCG_Case_Splitter = struct
    fun dest_case ctxt t =
      case strip_comb t of
        (Const (case_comb, _), args) =>
          (case Ctr_Sugar.ctr_sugar_of_case ctxt case_comb of
             NONE => NONE
           | SOME {case_thms, ...} =>
               let
                 val lhs = Thm.prop_of (hd (case_thms))
                   |> HOLogic.dest_Trueprop |> HOLogic.dest_eq |> fst;
                 val arity = length (snd (strip_comb lhs));
                 (*val conv = funpow (length args - arity) Conv.fun_conv
                   (Conv.rewrs_conv (map mk_meta_eq case_thms));*)
               in
                 SOME (nth args (arity - 1), case_thms)
               end)
      | _ => NONE;
    
    fun rewrite_with_asm_tac ctxt k =
      Subgoal.FOCUS (fn {context = ctxt', prems, ...} =>
        Local_Defs.unfold0_tac ctxt' [nth prems k]) ctxt;
    
    fun split_term_tac ctxt case_term = (
      case dest_case ctxt case_term of
        NONE => no_tac
      | SOME (arg,case_thms) => let 
            val stac = asm_full_simp_tac (put_simpset HOL_basic_ss ctxt addsimps case_thms) 
          in 
          (*CHANGED o stac
          ORELSE'*)
          (
            Induct.cases_tac ctxt false [[SOME arg]] NONE []
            THEN_ALL_NEW stac
          ) 
        end 1
    
    
    )

    fun split_tac ctxt = Subgoal.FOCUS_PARAMS (fn {context = ctxt, ...} => ALLGOALS (
        SUBGOAL (fn (t, _) => case Logic.strip_imp_concl t of
          @{mpat "Trueprop (Some _ \<le> T_g _ ?prog)"} => split_term_tac ctxt prog
         | @{mpat "Trueprop (progress ?prog)"} => split_term_tac ctxt prog  
     (*   | @{mpat "Trueprop (Case_Labeling.CTXT _ _ _ (valid _ _ ?prog))"} => split_term_tac ctxt prog *)
        | _ => no_tac
        ))
      ) ctxt 
      THEN_ALL_NEW TRY o Hypsubst.hyp_subst_tac ctxt

  end
\<close>

method_setup vcg_split_case = \<open>Scan.succeed (fn ctxt => SIMPLE_METHOD' (CHANGED o (VCG_Case_Splitter.split_tac ctxt)))\<close>


named_theorems vcg_rules' 
method vcg'_step methods solver uses rules =
    (intro rules vcg_rules' | vcg_split_case 
        | (progress simp;fail)  | (solver; fail))

method vcg' methods solver uses rules = repeat_all_new \<open>vcg'_step solver rules: rules\<close>




lemma T_g_bindT_I[vcg_rules']: 
  "\<And>t. Some t \<le>  T_g (\<lambda>y. T_g Q (f y) ) M \<Longrightarrow>  Some t \<le> T_g Q (M \<bind> f)"
  sorry


lemma T_g_SPECT_I[vcg_rules']:  "\<And>t. (Some (t' + t ) \<le> Q x)
    \<Longrightarrow>  Some t' \<le> T_g Q (SPECT [ x \<mapsto> t])"
  sorry

lemma (in -) While[vcg_rules']:
  fixes I and E :: "'a \<Rightarrow> 'c::{complete_lattice,minus,zero,order,plus}" and b C s0
  assumes  "I s0"  "(\<And>s. I s \<Longrightarrow> b s \<Longrightarrow> Some 0 \<le> T_g (\<lambda>s'. mm3 (E s) (if I s' then Some (E s') else None)) (C s)) "
     "(\<And>s. progress (C s))"
     "(\<And>x. \<not> b x \<Longrightarrow>  I x \<Longrightarrow>  (E x) \<le> (E s0) \<Longrightarrow>   Some (t +  ((E s0) - E x)) \<le> Q x)"
   shows   "Some t \<le> T_g Q  (whileIET I E b C s0)"
  sorry

lemma (in -) if_T_g[vcg_rules']: "(b \<Longrightarrow> t \<le> T_g Q Ma) \<Longrightarrow> (\<not>b \<Longrightarrow> t \<le> T_g Q Mb) \<Longrightarrow> t  \<le> T_g Q  (if b then Ma else Mb)"
   by (simp add: split_def)


lemma (in -) T_g_ASSERT_I[vcg_rules']: "(\<Phi> \<Longrightarrow> Some t \<le> Q ()) \<Longrightarrow> \<Phi> \<Longrightarrow> Some t \<le> T_g Q (ASSERT \<Phi>)"
  sorry


lemma (in -) T_SELECT[vcg_rules']: 
  assumes  
    "\<forall>x. \<not> P x \<Longrightarrow> Some tt \<le> T_g Q (SPECT [None \<mapsto> tf])"
  and p: "(\<And>x. P x \<Longrightarrow> Some tt \<le> T_g Q (SPECT [Some x \<mapsto> tf]) )"
shows "Some tt \<le> T_g Q (SELECT P tf)"
  sorry

lemma (in-) RETURNT_T_I[vcg_rules']: "t \<le> Q x \<Longrightarrow> t  \<le> T_g Q (RETURNT x)"
  sorry 


subsection \<open>Monotonicity rules for refine_vcg proofs\<close>


lemma RECT_mono[refine_mono]:
  assumes [simp]: "mono2 B'"
  assumes LE: "\<And>F x. (B' F x) \<le> timerefine FF (B F x) "
  shows " (RECT B' x) \<le> timerefine FF (RECT B x)"
  unfolding RECT_def
  apply clarsimp  
  using LE gfp_mono le_fun_def   sorry  


lemma WHILET_refine:
  assumes R0: "(x,x')\<in>R"
  assumes COND_REF: "\<And>x x'. \<lbrakk> (x,x')\<in>R \<rbrakk> \<Longrightarrow> b x = b' x'"
  assumes STEP_REF: 
    "\<And>x x'. \<lbrakk> (x,x')\<in>R; b x; b' x' \<rbrakk> \<Longrightarrow> f x \<le> \<Down>R (timerefine F  (f' x'))"
  shows "whileT b f x \<le> \<Down>R (timerefine F (whileT b' f' x'))"
  sorry

lemma (in -) whileT_mono: 
  assumes "\<And>x. b x \<Longrightarrow> c x \<le> timerefine F (c' x)"
  shows " (whileT b c x) \<le> timerefine F (whileT b c' x)" (*
  unfolding whileT_def apply(rule RECT_mono)
    subgoal by(refine_mono)  
  apply auto apply(rule bindT_mono) using assms by auto *) sorry


thm bindT_refine'

lemma bindT_refine_g:
  fixes R' :: "('a\<times>'b) set" and R::"('c\<times>'d) set"
  assumes R1: "M \<le> \<Down> R' (timerefine F M')"
  assumes R2: "\<And>x x' t t'. \<lbrakk> (x,x')\<in>R'; 
    nofailT M; nofailT M'; inresT2 M x t;  inresT2 M' x' t';
      t \<le> (\<lambda>c. Sum_any (\<lambda>a. t' a * F a c))  
  \<rbrakk> \<Longrightarrow> f x \<le> \<Down> R (timerefine F (f' x'))"
  shows "bindT M (\<lambda>x. f x) \<le> \<Down> R (timerefine F (bindT M' (\<lambda>x'. f' x')))"
    sorry

lemma bindT_refine_g':
  fixes R' :: "('a\<times>'b) set" and R::"('c\<times>'d) set"
  assumes R1: "M \<le> \<Down> R' (timerefine F M')"
  assumes R2: "\<And>x x' t t'. \<lbrakk> (x,x')\<in>R'; 
    nofailT M; nofailT M'; inresT2 M x t;  inresT2 M' x' t';
      t \<le> (\<lambda>c. Sum_any (\<lambda>a. t' a * F a c))  
  \<rbrakk> \<Longrightarrow> f x \<le>   (timerefine F (f' x'))"
  shows "bindT M (\<lambda>x. f x) \<le>  (timerefine F (bindT M' (\<lambda>x'. f' x')))"
    sorry

lemma timerefine_ASSERT: "(\<Phi>' \<Longrightarrow> \<Phi>) \<Longrightarrow> ASSERT \<Phi> \<le> timerefine F (ASSERT \<Phi>')"
  by (auto simp: timerefine_def ASSERT_def iASSERT_def RETURNT_def le_fun_def)

lemma timerefine_SPECT:
  assumes "\<And>x. P' x = None \<Longrightarrow> P x = None"
    and "\<And>x x2. P' x = Some x2 \<Longrightarrow> P x \<le> Some (\<lambda>cc. Sum_any (\<lambda>ac. x2 ac * F ac cc))"
shows "SPECT P \<le> timerefine F (SPECT P')"
  unfolding timerefine_def
  apply (auto split: option.splits simp: le_fun_def)
  using assms by auto

lemma timerefine_RETURNT:
  assumes "x=x'"
shows "RETURNT x \<le> timerefine F (RETURNT x')"
  unfolding RETURNT_def 
  using assms by (auto intro!: timerefine_SPECT simp: le_fun_def) 


thm SELECT_refine
lemma SELECT_refine_g:
  fixes T     
  assumes "\<And>x'. P' x' \<Longrightarrow> \<exists>x. P x"
  assumes "\<And>x. P x \<Longrightarrow>   P' x"
  assumes "T \<le> (\<lambda>cc. Sum_any (\<lambda>ac. T' ac * F ac cc))"
  shows "SELECT P T \<le> timerefine F (SELECT P' T')"
  unfolding SELECT_def
  apply (auto split: if_splits)
   using assms 
   by (auto intro!: timerefine_SPECT simp: emb'_def split: if_splits option.splits)
 (*
proof -
  have "SELECT P T \<le> SELECT P T'"
    using s1 assms(3) by auto
  also have "\<dots> \<le> SELECT P' T'"
    unfolding s2 apply safe
    using assms(1,2) by auto  
  finally show ?thesis .
qed *)



lemma If_refine: "b = b' \<Longrightarrow>
  (b \<Longrightarrow> b' \<Longrightarrow> S1 \<le> \<Down> R (timerefine F S1')) \<Longrightarrow>
  (\<not> b \<Longrightarrow> \<not> b' \<Longrightarrow> S2 \<le> \<Down> R (timerefine F S2')) \<Longrightarrow> (if b then S1 else S2) \<le> \<Down> R (timerefine F (if b' then S1' else S2'))"
  by auto

lemma Case_prod_refine: "(x,x')\<in> \<langle>S1,S2\<rangle>prod_rel \<Longrightarrow>
  (\<And>x x' y y'. (x,x')\<in>S1 \<Longrightarrow> (y,y')\<in>S2 \<Longrightarrow> C x y  \<le> \<Down> R (timerefine F (C' x' y')))
  \<Longrightarrow> (case x of (a,b) \<Rightarrow> C a b) \<le> \<Down> R (timerefine F (case x' of (a',b') \<Rightarrow> C' a' b'))"
  by (auto split: prod.split)

lemma case_prod_refine_g2:
  fixes P Q :: "'a \<Rightarrow> 'b \<Rightarrow> ('c,_) nrest"
  assumes
    "\<And>a b. P a b \<le> \<Down>R (timerefine FF (Q a b))"
  shows
 "(case x of (a,b) \<Rightarrow> P a b) \<le> \<Down>R (timerefine FF (case x of (a,b) \<Rightarrow> Q a b))"
  using assms 
  by (simp add: split_def)

lemma case_prod_refine_g:
  fixes P Q :: "'a \<Rightarrow> 'b \<Rightarrow> ('c,_) nrest"
  assumes
    "\<And>a b. P a b \<le> timerefine FF (Q a b)"
  shows
 "(case x of (a,b) \<Rightarrow> P a b) \<le> timerefine FF (case x of (a,b) \<Rightarrow> Q a b)"
  using assms 
  by (simp add: split_def)

lemma bindT_mono_g: 
  "m \<le> timerefine FF m' \<Longrightarrow> (\<And>x. nofailT m' \<Longrightarrow>  f x \<le> timerefine FF (f' x))
   \<Longrightarrow> bindT m f \<le> timerefine FF (bindT  m' f')"
  sorry


lemma le_ASSERTI_g2:
  fixes M :: "(_,_) nrest"
  shows "(\<Phi> \<Longrightarrow> M \<le> \<Down> R ( timerefine FF M' )) \<Longrightarrow> M \<le> \<Down> R (timerefine FF (ASSERT \<Phi> \<bind> (\<lambda>_. M')))"
  sorry

lemma le_ASSERTI_g:
  fixes M :: "(_,_) nrest"
  shows "(\<Phi> \<Longrightarrow> M \<le> timerefine FF M') \<Longrightarrow> M \<le> timerefine FF (ASSERT \<Phi> \<bind> (\<lambda>_. M'))"
  sorry


lemma ASSERT_leI2: 
  fixes M :: "(_,_) nrest"
  shows "\<Phi> \<Longrightarrow> (\<Phi> \<Longrightarrow> M \<le> \<Down> R( timerefine FF M')) \<Longrightarrow>ASSERT \<Phi> \<bind> (\<lambda>_. M) \<le>  \<Down> R (timerefine FF M')"
  sorry

lemma ASSERT_leI: 
  fixes M :: "(_,_) nrest"
  shows "\<Phi> \<Longrightarrow> (\<Phi> \<Longrightarrow> M \<le> timerefine FF M') \<Longrightarrow> ASSERT \<Phi> \<bind> (\<lambda>_. M) \<le> timerefine FF M'"
  sorry

thm case_option_mono
lemma case_option_mono_g:
  assumes "fn \<le> timerefine FF fn'"
  assumes "\<And>v. x=Some v \<Longrightarrow> fs v \<le> timerefine FF (fs' v)"
  shows "case_option fn fs x \<le> timerefine FF (case_option fn' fs' x)"
  using assms by (auto split: option.split)


lemma case_prod_mono_g: 
  "\<lbrakk>\<And>a b. p=(a,b) \<Longrightarrow> f a b \<le> timerefine FF (f' a b)\<rbrakk> \<Longrightarrow> case_prod f p \<le> timerefine FF (case_prod f' p)"
  by (auto split: prod.split)


lemma nofailT_ASSERT_bind_g:
  fixes M :: "(_,_) nrest"
  shows "nofailT (ASSERT P \<bind> (\<lambda>_. M)) \<longleftrightarrow> (P \<and> nofailT M)"
  sorry


lemma inresT2_REST:
  "\<And>t. inresT2 (REST X) x t \<longleftrightarrow> (\<exists>t'\<ge>enat o t. X x = Some t')" 
  unfolding inresT2_def 
  by auto

lemma inresT2_SPEC[refine_pw_simps]: "inresT2 (SPEC a b) = (\<lambda>x t. a x \<and>  b x \<ge> t)"
  unfolding SPEC_def inresT2_REST
  apply(rule ext)
  by(auto simp: le_fun_def split:  if_splits)



lemma inresT2_SELECT:
 "inresT2 (SELECT Q tt) x t'
     \<longleftrightarrow> ((case x of None \<Rightarrow> \<not>(\<exists>x. Q x) | Some x \<Rightarrow> Q x)  \<and> (t' \<le> tt))"
  by(auto simp: inresT2_def SELECT_def le_fun_def emb'_def) 

lemma pw_inresT2_bindT: "\<And>t. inresT2 (bindT m f) r t \<longleftrightarrow>
     (nofailT m \<longrightarrow> (\<exists>r' t' t''. inresT2 m r' t' \<and> inresT2 (f r') r t'' \<and> t = t' + t''))"
  sorry



  


lemma if_distrib2: "(if b then x else y) * z = (if b then x * z else y * z)"
  by(simp add: if_distrib)


section \<open>Trans rules\<close>

lemma conc_trans_2:
  assumes A: "C \<le> \<Down>R (timerefine F B)" and B: "B \<le> \<Down>R' (timerefine F' A)" 
  shows "C \<le> \<Down>R (\<Down>R'(timerefine F (timerefine F' A)))"
  sorry

section \<open>enum setup\<close>

 

lemma (in enum) sum_to_foldr: "sum f UNIV  
      = foldr (\<lambda>x a. a + f x) enum 0"
  (*= sum_list (map f enum_class.enum)"  *)
  unfolding UNIV_enum using enum_distinct
  apply(simp add: sum.distinct_set_conv_list  )
  apply(simp only: sum_list.eq_foldr foldr_map)  
  by (metis add.commute comp_apply)  

lemma (in enum) Sum_any_to_foldr: "Sum_any f  
      = foldr (\<lambda>x a. a + f x) enum 0"
  apply(subst Sum_any.expand_superset[where A=UNIV])
  by (simp_all add: sum_to_foldr)


end