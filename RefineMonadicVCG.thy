theory RefineMonadicVCG
  imports "Refine_Imperative_HOL/Sepref"
    "Case_Labeling.Case_Labeling"

begin


method repeat_all_new methods m = (m;repeat_all_new \<open>m\<close>)?

lemma R_intro: "A \<le>  \<Down>Id B \<Longrightarrow> A \<le> B" by simp
subsection "ASSERT"


lemma le_R_ASSERTI: "(\<Phi> \<Longrightarrow> M \<le> \<Down> R M') \<Longrightarrow>  M \<le> \<Down> R (ASSERT \<Phi> \<bind> (\<lambda>_. M'))"
  by(auto simp: pw_le_iff refine_pw_simps)

lemma T_ASSERT[vcg_simp_rules]: "Some t \<le> TTT Q (ASSERT \<Phi>) \<longleftrightarrow> Some t \<le> Q () \<and> \<Phi>"
  apply (cases \<Phi>)
   apply vcg'
  done
lemma T_ASSERT_I: "Some t \<le> Q () \<Longrightarrow> \<Phi> \<Longrightarrow> Some t \<le> TTT Q (ASSERT \<Phi>)"
  by(simp add: T_ASSERT T_RETURNT) 


lemma T_RESTemb_iff: "Some t'
       \<le> TTT Q (REST (emb' P t)) \<longleftrightarrow> (\<forall>x. P x \<longrightarrow> Some (t' + t x) \<le> Q x ) "
  by(auto simp: emb'_def T_pw mii_alt aux1)  


lemma T_RESTemb: "(\<And>x. P x \<Longrightarrow> Some (t' + t x) \<le> Q x)
    \<Longrightarrow>  Some t' \<le> TTT Q (REST (emb' P t))  "
  by (auto simp: T_RESTemb_iff)

lemma T_SPECT_I: "(Some (t' + t ) \<le> Q x)
    \<Longrightarrow>  Some t' \<le> TTT Q (SPECT [ x \<mapsto> t])  "
  by(auto simp:   T_pw mii_alt aux1)   
 


definition "valid t Q M = (Some t \<le> TTT Q M)"

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
          @{mpat "Trueprop (Some _ \<le> TTT _ ?prog)"} => split_term_tac ctxt prog
        | @{mpat "Trueprop (progress ?prog)"} => split_term_tac ctxt prog
        | @{mpat "Trueprop (Case_Labeling.CTXT _ _ _ (valid _ _ ?prog))"} => split_term_tac ctxt prog
        | _ => no_tac
        ))
      ) ctxt 
      THEN_ALL_NEW TRY o Hypsubst.hyp_subst_tac ctxt

  end
\<close>

method_setup vcg_split_case = \<open>Scan.succeed (fn ctxt => SIMPLE_METHOD' (CHANGED o (VCG_Case_Splitter.split_tac ctxt)))\<close>


subsection \<open>mm3 and emb\<close>



lemma Some_eq_mm3_Some_conv[vcg_simp_rules]: "Some t = mm3 t' (Some t'') \<longleftrightarrow> (t'' \<le> t' \<and> t = enat (t' - t''))"
  by (simp add: mm3_def)

lemma Some_eq_mm3_Some_conv': "mm3 t' (Some t'') = Some t \<longleftrightarrow> (t'' \<le> t' \<and> t = enat (t' - t''))"
  using Some_eq_mm3_Some_conv by metis


lemma Some_le_emb'_conv[vcg_simp_rules]: "Some t \<le> emb' Q ft x \<longleftrightarrow> Q x \<and> t \<le> ft x"
  by (auto simp: emb'_def)

lemma Some_eq_emb'_conv[vcg_simp_rules]: "emb' Q tf s = Some t \<longleftrightarrow> (Q s \<and> t = tf s)"
  unfolding emb'_def by(auto split: if_splits)

subsection \<open>Setup Labeled VCG\<close>

context
begin
  interpretation Labeling_Syntax .



  
  lemma LCondRule:
    fixes IC CT defines "CT' \<equiv> (''cond'', IC, []) # CT "
    assumes (* "V\<langle>(''vc'', IC, []),(''cond'', IC, []) # CT: p \<subseteq> {s. (s \<in> b \<longrightarrow> s \<in> w) \<and> (s \<notin> b \<longrightarrow> s \<in> w')}\<rangle>"
      and *) "b \<Longrightarrow> C\<langle>Suc IC,(''the'', IC, []) # (''cond'', IC, []) # CT,OC1: valid t Q c1 \<rangle>"
      and "~b \<Longrightarrow> C\<langle>Suc OC1,(''els'', Suc OC1, []) # (''cond'', IC, []) # CT,OC: valid t Q c2 \<rangle>"
    shows "C\<langle>IC,CT,OC: valid t Q (if b then c1 else c2)\<rangle>"
    using assms(2-) unfolding LABEL_simps by (simp add: valid_def)
  
lemma While:
  assumes  "I s0"  "(\<And>s. I s \<Longrightarrow> b s \<Longrightarrow> Some 0 \<le> TTT (\<lambda>s'. mm3 (E s) (if I s' then Some (E s') else None)) (C s))"
     "(\<And>s. progress (C s))"
     "(\<And>x. \<not> b x \<Longrightarrow>  I x \<Longrightarrow>  (E x) \<le> (E s0) \<Longrightarrow>   Some (t + enat ((E s0) - E x)) \<le> Q x)"
   shows   "Some t \<le> TTT Q (whileIET I E b C s0)"
  apply(rule whileIET_rule'[THEN T_conseq4])
  subgoal using assms(2) by simp
  subgoal using assms(3) by simp
  subgoal using assms(1) by simp
  subgoal for x using assms(4) apply(cases "I x") by(auto simp: Some_eq_mm3_Some_conv' split: if_splits)    
  done
    

  lemma LWhileRule:
    fixes IC CT  
    assumes "V\<langle>(''precondition'', IC, []),(''while'', IC, []) # CT: I s0\<rangle>"
      and "\<And>s. I s \<Longrightarrow>  b s \<Longrightarrow>  C\<langle>Suc IC,(''invariant'', Suc IC, []) # (''while'', IC, []) # CT,OC1: valid 0 (\<lambda>s'. mm3 (E s) (if I s' then Some (E s') else None)) (C s)\<rangle>"
      and "\<And>s. V\<langle>(''progress'', IC, []),(''while'', IC, []) # CT: progress (C s)\<rangle>"
      and "\<And>x. \<not> b x \<Longrightarrow>  I x \<Longrightarrow>  (E x) \<le> (E s0) \<Longrightarrow> C\<langle>Suc OC1,(''postcondition'', IC, [])#(''while'', IC, []) # CT,OC: Some (t + enat ((E s0) - E x)) \<le> Q x\<rangle>" 
    shows "C\<langle>IC,CT,OC: valid t Q (whileIET I E b C s0)\<rangle>"
     using assms unfolding valid_def  unfolding LABEL_simps
    apply(rule While) .

  thm whileIET_rule'[THEN T_conseq4, no_vars] T_conseq4
    

lemma validD: "valid t Q M \<Longrightarrow> Some t \<le> TTT Q M" by(simp add: valid_def)


  lemma LABELs_to_concl:
    "C\<langle>IC, CT, OC: True\<rangle> \<Longrightarrow> C\<langle>IC, CT, OC: P\<rangle> \<Longrightarrow> P"
    "V\<langle>x, ct: True\<rangle> \<Longrightarrow> V\<langle>x, ct: P\<rangle> \<Longrightarrow> P"
    unfolding LABEL_simps .

  thm T_ASSERT_I


  lemma LASSERTRule:
    assumes "V\<langle>(''ASSERT'', IC, []),CT: \<Phi>\<rangle>"
      "C\<langle>Suc IC, CT,OC: valid t Q (RETURNT ())\<rangle>"
    shows "C\<langle>IC,CT,OC: valid t Q (ASSERT \<Phi>)\<rangle>"
    using assms unfolding LABEL_simps   
    by (simp add: valid_def )   
 

  lemma LbindTRule:
    assumes "C\<langle>IC,CT,OC: valid t (\<lambda>y. TTT Q (f y)) m\<rangle>"
    shows "C\<langle>IC,CT,OC: valid t Q (bindT m f)\<rangle>"
    using assms unfolding LABEL_simps by(simp add: T_bindT valid_def )

  lemma LRETURNTRule:
    assumes "C\<langle>IC,CT,OC: Some t \<le> Q x\<rangle>"
    shows "C\<langle>IC,CT,OC: valid t Q (RETURNT x)\<rangle>"
    using assms unfolding LABEL_simps   
    by (simp add: valid_def T_RETURNT)  

 
  thm T_SELECT

  
  lemma LSELECTRule:
    fixes IC CT defines "CT' \<equiv> (''cond'', IC, []) # CT "
    assumes (* "V\<langle>(''vc'', IC, []),(''cond'', IC, []) # CT: p \<subseteq> {s. (s \<in> b \<longrightarrow> s \<in> w) \<and> (s \<notin> b \<longrightarrow> s \<in> w')}\<rangle>"
      and *) "\<And>x. P x \<Longrightarrow> C\<langle>Suc IC,(''Some'', IC, []) # (''SELECT'', IC, []) # CT,OC1: valid (t+T) Q (RETURNT (Some x)) \<rangle>"
      and "\<forall>x. \<not> P x \<Longrightarrow> C\<langle>Suc OC1,(''None'', Suc OC1, []) # (''SELECT'', IC, []) # CT,OC: valid (t+T) Q (RETURNT None) \<rangle>"
    shows "C\<langle>IC,CT,OC: valid t Q (SELECT P T)\<rangle>"
    using assms(2-) unfolding LABEL_simps apply (simp add: valid_def) apply(rule T_SELECT) 
    by(auto intro: T_SPECT_I simp add: T_RETURNT) 

  lemma LRESTembRule:
    assumes "\<And>x. P x \<Longrightarrow> C\<langle>IC,CT,OC: Some (t + T x) \<le> Q x\<rangle>"
    shows "C\<langle>IC,CT,OC: valid t Q (REST (emb' P T))\<rangle>"
    using assms unfolding LABEL_simps   
    by (simp add: valid_def T_RESTemb) 

  lemma LRESTsingleRule:
    assumes "C\<langle>IC,CT,OC: Some (t + t') \<le> Q x\<rangle>"
    shows "C\<langle>IC,CT,OC: valid t Q (REST [x\<mapsto>t'])\<rangle>"
    using assms unfolding LABEL_simps   
    by (simp add: valid_def   T_pw mii_alt aux1)

  lemma LTTTinRule:
    assumes "C\<langle>IC,CT,OC: valid t Q M\<rangle>"
    shows "C\<langle>IC,CT,OC: Some t \<le> TTT Q M\<rangle>"
    using assms unfolding LABEL_simps by(simp add:  valid_def )

  lemma LembRule:
    assumes "V\<langle>(''time'', IC, []), CT: t \<le> T x \<rangle>"
      and "V\<langle>(''func'', IC, []), CT: P x \<rangle>"
    shows "C\<langle>IC,CT,IC: Some t \<le> emb' P T x\<rangle>"
    using assms unfolding LABEL_simps   
    by (simp add: emb'_def  )  

  lemma Lmm3Rule:
    assumes "V\<langle>(''time'', IC, []), CT: Va' \<le> Va \<and> t \<le> enat (Va - Va') \<rangle>"
      and "V\<langle>(''func'', IC, []), CT: b \<rangle>"
    shows "C\<langle>IC,CT,IC: Some t \<le> mm3 Va (if b then Some Va' else None) \<rangle>"
    using assms unfolding LABEL_simps   
    by (simp add:  mm3_def  )    
 

  lemma LinjectRule:
    assumes "Some t \<le> TTT Q A \<Longrightarrow> Some t \<le> TTT Q B"
        "C\<langle>IC,CT,OC: valid t Q A\<rangle>"
    shows "C\<langle>IC,CT,OC: valid t Q B\<rangle>"
    using assms unfolding LABEL_simps by(simp add:  valid_def )
  lemma Linject2Rule:
    assumes "A = B"
        "C\<langle>IC,CT,OC: valid t Q A\<rangle>"
    shows "C\<langle>IC,CT,OC: valid t Q B\<rangle>"
    using assms unfolding LABEL_simps by(simp add:  valid_def )


method labeled_VCG_init =  ((rule T_specifies_I validD)+), rule Initial_Label
method labeled_VCG_step uses rules = (rule rules[symmetric, THEN Linject2Rule] 
        LTTTinRule LbindTRule 
        LembRule Lmm3Rule
        LRETURNTRule LASSERTRule LCondRule LSELECTRule
        LRESTsingleRule LRESTembRule LWhileRule  ) | vcg_split_case
 
method labeled_VCG uses rules = labeled_VCG_init, repeat_all_new \<open>labeled_VCG_step rules: rules\<close>
method casified_VCG uses rules = labeled_VCG rules: rules, casify


lemma "do { x \<leftarrow> SELECT P T;
            (case x of None \<Rightarrow> RETURNT (1::nat) | Some t \<Rightarrow> RETURNT (2::nat))
        } \<le> SPECT (emb Q T')"
  apply labeled_VCG   oops



lemma assumes "b" "c"
  shows "do { ASSERT b;
            ASSERT c;
            RETURNT 1 } \<le> SPECT (emb (\<lambda>x. x>(0::nat)) 1)"
  apply labeled_VCG    
proof casify
  case ASSERT then show ?case by fact
  case ASSERTa then show ?case by fact
  case func then show ?case by simp
  case time then show ?case by simp 
qed

lemma "do {      
      (if b then RETURNT (1::nat) else RETURNT 2)
    } \<le> SPECT (emb (\<lambda>x. x>0) 1)"
  apply labeled_VCG    
proof casify
  case cond {
    case the {
      case time 
      then show ?case by simp  
    next
      case func 
      then show ?case by simp   
    }
  next
    case els { (*
      case time 
      then show ?case by simp  
    next *)
      case func 
      then show ?case by simp   
    }
  }
qed simp


lemma assumes "b"
  shows "do {
      ASSERT b;
      (if b then RETURNT (1::nat) else RETURNT 2)
    } \<le> SPECT (emb (\<lambda>x. x>0) 1)"
  apply labeled_VCG    
proof casify
  case ASSERT then show ?case by fact 
  case cond {
    case the {
      case time 
      then show ?case by simp  
    next
      case func 
      then show ?case by simp   
    }
  next
    case els { (*
    case time 
    then show ?case by simp  
  next *)
      case func 
      then show ?case by simp   
    }
  }
qed simp
 

end


(* TODO: move *)

lemma RETURN_le_RETURN_iff[simp]: "RETURNT x \<le> RETURNT y \<longleftrightarrow> x=y"
  apply auto
  by (simp add: pw_le_iff)

lemma [sepref_import_param]: 
  "((=),(=))\<in>Id\<rightarrow>Id\<rightarrow>Id" 
  "((<),(<))\<in>Id\<rightarrow>Id\<rightarrow>Id" 
  by simp_all



lemma SPECT_ub: "T\<le>T' \<Longrightarrow> SPECT (emb' M' T) \<le> SPECT (emb' M' T')"
  unfolding emb'_def by (auto simp: pw_le_iff le_funD order_trans refine_pw_simps)



lemma REST_single_rule[vcg_simp_rules]: "Some t \<le> TTT Q (REST [x\<mapsto>t']) \<longleftrightarrow> Some (t+t') \<le> (Q x)"
  by (simp add: T_REST aux1')

thm T_pw refine_pw_simps

thm pw_le_iff


subsection "progress solver"



method progress methods solver = 
  (rule asm_rl[of "progress _"] , (simp split: prod.splits | intro allI impI conjI | determ \<open>rule progress_rules\<close> | rule disjI1; progress \<open>solver\<close>; fail | rule disjI2; progress \<open>solver\<close>; fail | solver)+) []
method progress' methods solver = 
  (rule asm_rl[of "progress _"] , (vcg_split_case | intro allI impI conjI | determ \<open>rule progress_rules\<close> | rule disjI1 disjI2; progress'\<open>solver\<close> | (solver;fail))+) []


subsection \<open>WHILET refine\<close>

                                         
lemma WHILET_refine:
  assumes R0: "(x,x')\<in>R"
  assumes COND_REF: "\<And>x x'. \<lbrakk> (x,x')\<in>R \<rbrakk> \<Longrightarrow> b x = b' x'"
  assumes STEP_REF: 
    "\<And>x x'. \<lbrakk> (x,x')\<in>R; b x; b' x' \<rbrakk> \<Longrightarrow> f x \<le> \<Down>R (f' x')"
  shows "whileT b f x \<le>\<Down>R (whileT b' f' x')"
  sorry

lemma assumes "(\<And>s t. P s = Some t \<Longrightarrow> \<exists>s'. Some t \<le> Q s' \<and> (s, s') \<in> R)"
  shows SPECT_refine: "SPECT P \<le> \<Down> R (SPECT Q)"
  unfolding conc_fun_def apply (simp add: le_fun_def) apply auto
  subgoal for x apply(cases "P x = None") apply simp
    apply auto subgoal for y 
      apply(frule assms[of x y]) apply auto
      subgoal for s'
      apply(rule dual_order.trans[where b="Q s'"])
         apply(rule Sup_upper) by auto 
      done
    done
  done

subsection \<open>moreStuff involving mm3 and emb\<close>

lemma Some_le_mm3_Some_conv[vcg_simp_rules]: "Some t \<le> mm3 t' (Some t'') \<longleftrightarrow> (t'' \<le> t' \<and> t \<le> enat (t' - t''))"
  by (simp add: mm3_def)




lemma embtimeI: "T \<le> T' \<Longrightarrow> emb P T \<le> emb P T'" unfolding emb'_def by (auto simp: le_fun_def split:  if_splits)

lemma not_cons_is_Nil_conv[simp]: "(\<forall>y ys. l \<noteq> y # ys) \<longleftrightarrow> l=[]" by (cases l) auto

lemma mm3_Some0_eq[simp]: "mm3 t (Some 0) = Some t"
  by (auto simp: mm3_def)


lemma ran_emb': "c \<in> ran (emb' Q t) \<longleftrightarrow> (\<exists>s'. Q s' \<and> t s' = c)"
  by(auto simp: emb'_def ran_def)

lemma ran_emb_conv: "Ex Q \<Longrightarrow>  ran (emb Q t) = {t}"
  by (auto simp: ran_emb')

lemma in_ran_emb_special_case: "c\<in>ran (emb Q t) \<Longrightarrow> c\<le>t"
  apply (cases "Ex Q")
   apply (auto simp: ran_emb_conv)
  apply (auto simp: emb'_def)
  done

lemma dom_emb'_eq[simp]: "dom (emb' Q f) = Collect Q"
  by(auto simp: emb'_def split: if_splits)


lemma emb_le_emb: "emb' P T \<le> emb' P' T' \<longleftrightarrow> (\<forall>x. P x \<longrightarrow> P' x \<and>  T x \<le> T' x)"
  unfolding emb'_def by (auto simp: le_fun_def split: if_splits)



  thm vcg_rules



(* lemmas [vcg_rules] = T_RESTemb_iff[THEN iffD2] *)





subsection \<open>VCG for monadic programs\<close>

subsubsection \<open>old\<close>
thm vcg_rules
thm vcg_simp_rules
declare mm3_Some_conv [vcg_simp_rules]
thm progress_rules 
thm vcg_rules

lemma SS[vcg_simp_rules]: "Some t = Some t' \<longleftrightarrow> t = t'" by simp
lemma SS': "(if b then Some t else None) = Some t' \<longleftrightarrow> (b \<and> t = t')" by simp 

term "(case s of (a,b) \<Rightarrow> M a b)"
lemma case_T[vcg_rules]: "(\<And>a b. s = (a, b) \<Longrightarrow> t \<le> TTT Q (M a b)) \<Longrightarrow> t  \<le> TTT Q (case s of (a,b) \<Rightarrow> M a b)"
  by (simp add: split_def)

subsubsection \<open>new setup\<close>

named_theorems vcg_rules' 
lemma if_T[vcg_rules']: "(b \<Longrightarrow> t \<le> TTT Q Ma) \<Longrightarrow> (\<not>b \<Longrightarrow> t \<le> TTT Q Mb) \<Longrightarrow> t  \<le> TTT Q (if b then Ma else Mb)"
   by (simp add: split_def)
lemma RETURNT_T_I[vcg_rules']: "t \<le> Q x \<Longrightarrow> t  \<le> TTT Q (RETURNT x)"
   by (simp add: T_RETURNT)
   
declare T_SPECT_I [vcg_rules']
declare TbindT_I  [vcg_rules']
declare T_RESTemb [vcg_rules']
declare T_ASSERT_I [vcg_rules']
declare While[ vcg_rules']
thm vcg_rules
  


named_theorems vcg_simps'

declare option.case [vcg_simps']


method vcg'_step methods solver uses rules = (intro rules vcg_rules' | vcg_split_case | (progress simp;fail) | (solver; fail))

method vcg' methods solver uses rules = repeat_all_new \<open>vcg'_step solver rules: rules\<close>

thm T_SELECT
declare T_SELECT [vcg_rules']

lemma "\<And>c. do {  c \<leftarrow> RETURNT None;
            (case_option (RETURNT (1::nat)) (\<lambda>p. RETURNT (2::nat))) c 
      } \<le> SPECT (emb (\<lambda>x. x>(0::nat)) 1)"
  apply(rule T_specifies_I)
  apply(vcg'\<open>-\<close>)  unfolding  option.case   oops
  thm option.case

end