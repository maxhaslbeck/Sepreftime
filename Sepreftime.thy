theory Sepreftime
  imports "HOL-Library.Extended_Nat" "Refine_Monadic.RefineG_Domain"  Refine_Monadic.Refine_Misc  
  "HOL-Library.Monad_Syntax"  
begin


section "Auxiliaries"

subsection "Auxiliaries for option"

lemma less_eq_option_None_is_None': "x \<le> None \<longleftrightarrow> x = None" by(auto simp: less_eq_option_None_is_None)

lemma everywhereNone: "(\<forall>x\<in>X. x = None) \<longleftrightarrow> X = {} \<or> X = {None}"
  by auto

subsection "Auxiliaries for enat"


lemma helper: "x2 \<le> x2a \<Longrightarrow> \<not> x2 < a \<Longrightarrow> \<not> x2a < a \<Longrightarrow>  x2 - (a::enat) \<le> x2a - a"
  apply(cases x2; cases x2a) apply auto apply(cases a) by auto

lemma helper2: "x2b \<le> x2 \<Longrightarrow> \<not> x2a < x2  \<Longrightarrow> \<not> x2a < x2b \<Longrightarrow> x2a - (x2::enat) \<le> x2a - x2b"
  apply(cases x2; cases x2a) apply auto apply(cases x2b) by auto

lemma Sup_finite_enat: "Sup X = Some (enat a) \<Longrightarrow> Some (enat a) \<in> X"
  by (auto simp: Sup_option_def Sup_enat_def these_empty_eq Max_eq_iff in_these_eq split: if_splits)

lemma Sup_enat_less2: " Sup X = \<infinity> \<Longrightarrow> (\<exists>x\<in>X. enat t < x)"
  unfolding  Sup_enat_def using    finite_enat_bounded linear 
  apply(auto split: if_splits)  
   apply (smt Max_in empty_iff enat_ord_code(4))
  by (smt not_less)  


lemma [simp]: "t \<le> Some (\<infinity>::enat)"
  by (cases t, auto)

subsection "Auxiliary (for Sup and Inf)"



lemma aux11: "f`X={y} \<longleftrightarrow> (X\<noteq>{} \<and> (\<forall>x\<in>X. f x = y))" by auto
 
lemma aux2: "(\<lambda>f. f x) ` {[x \<mapsto> t1] |x t1. M x = Some t1} = {None} \<longleftrightarrow> (M x = None \<and> M\<noteq>Map.empty)"
  apply (cases "M x"; auto simp: aux11)
  by force

lemma aux3: "(\<lambda>f. f x) ` {[x \<mapsto> t1] |x t1. M x = Some t1} = {Some t1 | t1. M x = Some t1} \<union> ({None | y. y\<noteq>x \<and> M y \<noteq> None })"
  by (fastforce split: if_splits simp: image_iff) 

lemma Sup_pointwise_eq_fun: "(SUP f:{[x \<mapsto> t1] |x t1. M x = Some t1}. f x) = M x"
  unfolding Sup_option_def  
  apply (simp add: aux2) 
  apply (auto simp: aux3)
  by (metis (mono_tags, lifting) Some_image_these_eq Sup_least in_these_eq mem_Collect_eq sup_absorb1 these_image_Some_eq)


lemma SUP_eq_None_iff: "(SUP f:X. f x) = None \<longleftrightarrow> X={} \<or> (\<forall>f\<in>X. f x = None)"
  by (smt SUP_bot_conv(2) SUP_empty Sup_empty empty_Sup)

lemma SUP_eq_Some_iff: "(SUP f:X. f x) = Some t \<longleftrightarrow> (\<exists>f\<in>X. f x \<noteq> None) \<and> (t=Sup {t' | f t'. f\<in>X \<and> f x = Some t' })"
  apply auto
  subgoal 
    by (smt Sup_bot_conv(1) Sup_empty Sup_option_def Sup_pointwise_eq_fun imageE option.distinct(1))
  subgoal 
    unfolding Sup_option_def
    apply (clarsimp split: if_splits)
    apply (fo_rule arg_cong)
    apply (auto simp: Option.these_def)
    apply (metis (mono_tags, lifting) image_iff mem_Collect_eq option.sel)
    apply (metis (mono_tags, lifting) image_iff mem_Collect_eq option.sel)
    done
  subgoal 
    unfolding Sup_option_def
    apply (clarsimp split: if_splits; safe)
    subgoal by (force simp: image_iff)
    apply (fo_rule arg_cong)
    apply (auto simp: Option.these_def)
    apply (metis (mono_tags, lifting) image_iff mem_Collect_eq option.sel)
    done
  done  



lemma Sup_enat_less: "X \<noteq> {} \<Longrightarrow> enat t \<le> Sup X \<longleftrightarrow> (\<exists>x\<in>X. enat t \<le> x)"
  apply rule
  subgoal 
  by (metis Max_in Sup_enat_def finite_enat_bounded linear) 
  subgoal apply auto
    by (simp add: Sup_upper2)
  done


(* 
  This is how implication can be phrased with an Inf operation.
  Generalization from boolean to enat can be explained this way.
 *)

lemma fixes Q P  shows
    "Inf { P x \<le> Q x |x. True}  \<longleftrightarrow> P \<le> Q" unfolding le_fun_def by simp


section "NREST"

datatype 'a nrest = FAILi | REST "'a \<Rightarrow> enat option"


                   
instantiation nrest :: (type) complete_lattice
begin

fun less_eq_nrest where
  "_ \<le> FAILi \<longleftrightarrow> True" |
  "(REST a) \<le> (REST b) \<longleftrightarrow> a \<le> b" |
  "FAILi \<le> (REST _) \<longleftrightarrow> False"

fun less_nrest where
  "FAILi < _ \<longleftrightarrow> False" |
  "(REST _) < FAILi \<longleftrightarrow> True" |
  "(REST a) < (REST b) \<longleftrightarrow> a < b"

fun sup_nrest where
  "sup _ FAILi = FAILi" |
  "sup FAILi _ = FAILi" |
  "sup (REST a) (REST b) = REST (\<lambda>x. max (a x) (b x))"

fun inf_nrest where 
  "inf x FAILi = x" |
  "inf FAILi x = x" |
  "inf (REST a) (REST b) = REST (\<lambda>x. min (a x) (b x))"

lemma "min (None) (Some (1::enat)) = None" by simp
lemma "max (None) (Some (1::enat)) = Some 1" by eval

definition "Sup X \<equiv> if FAILi\<in>X then FAILi else REST (Sup {f . REST f \<in> X})"
definition "Inf X \<equiv> if \<exists>f. REST f\<in>X then REST (Inf {f . REST f \<in> X}) else FAILi"

definition "bot \<equiv> REST (Map.empty)"
definition "top \<equiv> FAILi"

instance
  apply(intro_classes)
  unfolding Sup_nrest_def  Inf_nrest_def  bot_nrest_def top_nrest_def
  apply (case_tac x, case_tac [!] y, auto) []
  apply (case_tac x, auto) []
  apply (case_tac x, case_tac [!] y, case_tac [!] z, auto) []
  apply (case_tac x, (case_tac [!] y)?, auto) []
  apply (case_tac x, (case_tac [!] y)?, simp_all  add: le_fun_def) []
  apply (case_tac x, (case_tac [!] y)?, auto   simp: le_fun_def) []
  apply (case_tac x, case_tac [!] y, case_tac [!] z, auto   simp: le_fun_def) []
  apply (case_tac x, (case_tac [!] y)?, auto   simp: le_fun_def) []
  apply (case_tac x, (case_tac [!] y)?, auto   simp: le_fun_def) []
  apply (case_tac x, case_tac [!] y, case_tac [!] z, auto   simp: le_fun_def) []
  apply (case_tac x, auto simp add: Inf_lower ) [] 
  apply (case_tac z, fastforce+) [] using le_Inf_iff apply fastforce
  apply (case_tac x, auto simp add: Sup_upper) []
  apply (case_tac z, fastforce+) []  using Sup_le_iff less_eq_nrest.simps(2) apply fastforce
  apply auto []
  apply (auto simp: bot_option_def) []
  done   
end


definition "RETURNT x \<equiv> REST (\<lambda>e. if e=x then Some 0 else None)"
abbreviation "FAILT \<equiv> top::'a nrest"
abbreviation "SUCCEEDT \<equiv> bot::'a nrest"
abbreviation SPECT where "SPECT \<equiv> REST"

lemma RETURNT_alt: "RETURNT x = REST [x\<mapsto>0]"
  unfolding RETURNT_def by auto

lemma nrest_inequalities[simp]: 
  "FAILT \<noteq> REST X"
  "FAILT \<noteq> SUCCEEDT" 
  "FAILT \<noteq> RETURNT x"
  "SUCCEEDT \<noteq> FAILT"
  "SUCCEEDT \<noteq> RETURNT x"
  "REST X \<noteq> FAILT"
  "RETURNT x \<noteq> FAILT"
  "RETURNT x \<noteq> SUCCEEDT"
  unfolding top_nrest_def bot_nrest_def RETURNT_def  
  apply (auto) by (metis option.distinct(1))+


lemma nrest_more_simps[simp]:
  "SUCCEEDT = REST X \<longleftrightarrow> X=Map.empty" 
  "REST X = SUCCEEDT \<longleftrightarrow> X=Map.empty" 
  "REST X = RETURNT x \<longleftrightarrow> X=[x\<mapsto>0]" 
  "REST X = REST Y \<longleftrightarrow> X=Y"
  "RETURNT x = REST X \<longleftrightarrow> X=[x\<mapsto>0]"
  "RETURNT x = RETURNT y \<longleftrightarrow> x=y" 
  unfolding top_nrest_def bot_nrest_def RETURNT_def apply (auto split: if_splits)
  by (metis option.distinct(1)) 


lemma nres_simp_internals: 
  "REST Map.empty = SUCCEEDT"
   "FAILi = FAILT" 
  unfolding top_nrest_def bot_nrest_def by simp_all


lemma nres_order_simps[simp]:
  "\<not> FAILT \<le> REST M" 
  "REST M \<le> REST M' \<longleftrightarrow> (M\<le>M')"
  by (auto simp: nres_simp_internals[symmetric])   

lemma nres_top_unique[simp]:" FAILT \<le> S' \<longleftrightarrow> S' = FAILT"
  by (rule top_unique) 

lemma FAILT_cases[simp]: "(case FAILT of FAILi \<Rightarrow> P | REST x \<Rightarrow> Q x) = P"
  by (auto simp: nres_simp_internals[symmetric])  

lemma nrest_Sup_FAILT: 
  "Sup X = FAILT \<longleftrightarrow> FAILT \<in> X"
  "FAILT = Sup X \<longleftrightarrow> FAILT \<in> X"
  by (auto simp: nres_simp_internals Sup_nrest_def)


lemma nrest_Sup_SPECT_D: "Sup X = SPECT m \<Longrightarrow> m x = Sup {f x | f. REST f \<in> X}"
  unfolding Sup_nrest_def apply(auto split: if_splits) unfolding Sup_fun_def  
  apply(fo_rule arg_cong) by blast

declare nres_simp_internals(2)[simp]

lemma nrest_noREST_FAILT[simp]: "(\<forall>x2. m \<noteq> REST x2) \<longleftrightarrow> m=FAILT"
  apply (cases m) apply auto done

lemma   no_FAILTE:  
  assumes "g xa \<noteq> FAILT" 
  obtains X where "g xa = REST X" using assms by (cases "g xa") auto


lemma case_prod_refine:
  fixes P Q :: "'a \<Rightarrow> 'b \<Rightarrow> 'c nrest"
  assumes
    "\<And>a b. P a b \<le> Q a b"
  shows
 "(case x of (a,b) \<Rightarrow> P a b) \<le> (case x of (a,b) \<Rightarrow> Q a b)"
  using assms 
  by (simp add: split_def)

lemma case_option_refine: (* obsolete ? *)
  fixes P Q :: "'a \<Rightarrow> 'b \<Rightarrow> 'c nrest"
  assumes
    "PN \<le> QN"
    "\<And>a. PS a \<le> QS a"
  shows
 "(case x of None \<Rightarrow> PN | Some a \<Rightarrow> PS a ) \<le> (case x of None \<Rightarrow> QN | Some a \<Rightarrow> QS a )"
  using assms 
  by (auto split: option.splits)


section "pointwise reasoning"

named_theorems refine_pw_simps 
ML \<open>
  structure refine_pw_simps = Named_Thms
    ( val name = @{binding refine_pw_simps}
      val description = "Refinement Framework: " ^
        "Simplifier rules for pointwise reasoning" )
\<close>    
  
definition nofailT :: "'a nrest \<Rightarrow> bool" where "nofailT S \<equiv> S\<noteq>FAILT"


lemma nofailT_simps[simp]:
  "nofailT FAILT \<longleftrightarrow> False"
  "nofailT (REST X) \<longleftrightarrow> True"
  "nofailT (RETURNT x) \<longleftrightarrow> True"
  "nofailT SUCCEEDT \<longleftrightarrow> True"
  unfolding nofailT_def
  by (simp_all add: RETURNT_def)



definition inresT :: "'a nrest \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> bool" where 
  "inresT S x t \<equiv> (case S of FAILi \<Rightarrow> True | REST X \<Rightarrow> (\<exists>t'. X x = Some t' \<and>  enat t\<le>t'))"


lemma inresT_alt: "inresT S x t \<longleftrightarrow> REST ([x\<mapsto>enat t]) \<le> S"
  unfolding inresT_def apply(cases S)  
  by (auto dest!: le_funD[where x=x] simp: le_funI less_eq_option_def split: option.splits )


lemma inresT_mono: "inresT S x t \<Longrightarrow> t' \<le> t \<Longrightarrow> inresT S x t'"
  unfolding inresT_def apply(cases S) apply auto
  using enat_ord_simps(1) order_trans by blast
 

lemma inresT_RETURNT[simp]: "inresT (RETURNT x) y t \<longleftrightarrow> t = 0 \<and> y = x"
  by(auto simp: inresT_def RETURNT_def enat_0_iff split: nrest.splits)


lemma inresT_FAILT[simp]: "inresT FAILT r t"
  by(simp add: inresT_def)


lemma fail_inresT[refine_pw_simps]: "\<not> nofailT M \<Longrightarrow> inresT M x t"
  unfolding nofailT_def by simp




lemma pw_inresT_Sup[refine_pw_simps]: "inresT (Sup X) r t \<longleftrightarrow> (\<exists>M\<in>X. \<exists>t'\<ge>t.  inresT M r t')"
  apply(rule)
  subgoal (* \<rightarrow> *)
    apply(cases "Sup X")
    subgoal by (force simp: nrest_Sup_FAILT)
    subgoal 
      apply(auto simp: inresT_def  Sup_nrest_def split: if_splits)
      apply(auto simp: SUP_eq_Some_iff split: nrest.splits)  
      apply(subst (asm) Sup_enat_less)
       apply auto []  
      apply auto  by blast  
    done
  subgoal (* <- *)
    apply(cases "Sup X")
    subgoal by (auto simp: nrest_Sup_FAILT top_Sup)
    subgoal 
      apply(auto simp: inresT_def  Sup_nrest_def split: if_splits)
      apply(auto simp: SUP_eq_Some_iff split: nrest.splits)  
      apply(subst Sup_enat_less)
       apply auto []
      apply auto
      using dual_order.trans enat_ord_simps(1) by blast 
    done
  done

         
lemma inresT_REST[simp]:
  "inresT (REST X) x t \<longleftrightarrow> (\<exists>t'\<ge>t. X x = Some t')" 
  unfolding inresT_def 
  by (auto )


lemma pw_Sup_nofail[refine_pw_simps]: "nofailT (Sup X) \<longleftrightarrow> (\<forall>x\<in>X. nofailT x)"
  apply (cases "Sup X")  
   apply auto unfolding Sup_nrest_def apply (auto split: if_splits)
  apply force unfolding nofailT_def apply(force simp add: nres_simp_internals)
  done


lemma inres_simps[simp]:
  "inresT FAILT = (\<lambda>_ _. True)" 
  "inresT SUCCEEDT = (\<lambda>_ _ . False)"
  unfolding inresT_def [abs_def]
  by (auto split: nrest.splits simp add: RETURNT_def) 


lemma pw_le_iff: 
  "S \<le> S' \<longleftrightarrow> (nofailT S'\<longrightarrow> (nofailT S \<and> (\<forall>x t. inresT S x t \<longrightarrow> inresT S' x t)))"
  apply (cases S; cases S', simp_all)
  unfolding nofailT_def inresT_def apply (auto split: nrest.splits) 
   apply (metis le_fun_def le_some_optE order.trans) 
  apply(auto intro!: le_funI simp: less_eq_option_def split: option.splits)
  apply (metis option.distinct(1) zero_enat_def zero_le)
  by (smt Suc_ile_eq enat.exhaust linorder_not_le option.simps(1) order_refl) 

lemma pw_eq_iff:
  "S=S' \<longleftrightarrow> (nofailT S = nofailT S' \<and> (\<forall>x t. inresT S x t \<longleftrightarrow> inresT S' x t))"
  apply (rule iffI)
  apply simp
  apply (rule antisym)
  apply (auto simp add: pw_le_iff)
  done

lemma pw_flat_ge_iff: "flat_ge S S' \<longleftrightarrow> 
  (nofailT S) \<longrightarrow> nofailT S' \<and> (\<forall>x t. inresT S x t \<longleftrightarrow> inresT S' x t)"
  apply (simp add: flat_ord_def)
  apply(simp add: pw_eq_iff) apply safe
  by (auto simp add: nofailT_def)   



lemma pw_eqI: 
  assumes "nofailT S = nofailT S'" 
  assumes "\<And>x t. inresT S x t \<longleftrightarrow> inresT S' x t" 
  shows "S=S'"
  using assms by (simp add: pw_eq_iff)


 


section \<open> Monad Operators \<close>

definition bindT :: "'b nrest \<Rightarrow> ('b \<Rightarrow> 'a nrest) \<Rightarrow> 'a nrest" where
  "bindT M f \<equiv> case M of 
  FAILi \<Rightarrow> FAILT |
  REST X \<Rightarrow> Sup { (case f x of FAILi \<Rightarrow> FAILT 
                | REST m2 \<Rightarrow> REST (map_option ((+) t1) o (m2) ))
                    |x t1. X x = Some t1}"

adhoc_overloading
  Monad_Syntax.bind Sepreftime.bindT


lemma bindT_FAIL[simp]: "bindT FAILT g = FAILT"
  by (auto simp: bindT_def)       


lemma "bindT SUCCEEDT f = SUCCEEDT"
  unfolding bindT_def by(auto split: nrest.split simp add: bot_nrest_def) 


lemma pw_inresT_bindT_aux: "inresT (bindT m f) r t \<longleftrightarrow>
     (nofailT m \<longrightarrow> (\<exists>r' t' t''. inresT m r' t' \<and> inresT (f r') r t'' \<and> t \<le> t' + t''))"
  apply(rule)
  subgoal (* \<rightarrow> *)
    apply(cases m)
    subgoal by auto
    subgoal apply(auto simp: bindT_def pw_inresT_Sup split: nrest.splits) 
      subgoal for M x t' t1 
        apply(rule exI[where x=x])
        apply(cases "f x") apply auto  
        subgoal for x2 z apply(cases t1)
           apply auto
          subgoal for n apply(rule exI[where x=n]) apply auto
            by (smt dual_order.trans enat_ile enat_ord_simps(1) le_add2 linear order_mono_setup.refl plus_enat_simps(1)) 
          subgoal
            by (metis le_add1 zero_enat_def zero_le) 
          done
        done
      subgoal for x t' t1
        apply(rule exI[where x=x]) apply auto
        apply(cases t1) apply auto
        subgoal for n apply(rule exI[where x=n]) apply auto
          apply(rule exI[where x=t]) by auto
        subgoal 
          by presburger
        done 
      done
    done
  subgoal (* <- *)
    apply(cases m)
    subgoal by auto
    subgoal for x2
      apply (auto simp: bindT_def  split: nrest.splits)
      apply(auto simp: pw_inresT_Sup )
      subgoal for r' t' t'a t''
        apply(cases "f r'")
        subgoal apply auto apply(force) done
        subgoal for x2a
          apply(rule exI[where x="REST (map_option ((+) t'a) \<circ> x2a)"]) 
          apply auto
           apply(rule exI[where x=r'])
           apply auto
          using add_mono by fastforce
        done
      done
    done
  done

lemma pw_inresT_bindT[refine_pw_simps]: "inresT (bindT m f) r t \<longleftrightarrow>
     (nofailT m \<longrightarrow> (\<exists>r' t' t''. inresT m r' t' \<and> inresT (f r') r t'' \<and> t = t' + t''))"
  apply (auto simp: pw_inresT_bindT_aux) 
  by (metis (full_types) inresT_mono le_iff_add linear nat_add_left_cancel_le) 
     

lemma pw_bindT_nofailT[refine_pw_simps]: "nofailT (bindT M f) \<longleftrightarrow> (nofailT M \<and> (\<forall>x t. inresT M x t \<longrightarrow> nofailT (f x)))"
  unfolding bindT_def   
   apply (auto elim: no_FAILTE simp: refine_pw_simps  split: nrest.splits )  
  apply force+ 
  by (metis enat_ile le_cases nofailT_def)

lemma [simp]: "((+) (0::enat)) = id" by auto

declare map_option.id[simp] 


section \<open>Monad Rules\<close>

lemma nres_bind_left_identity[simp]: "bindT (RETURNT x) f = f x"
  unfolding bindT_def RETURNT_def 
  by(auto split: nrest.split ) 

lemma nres_bind_right_identity[simp]: "bindT M RETURNT = M" 
  by(auto intro!: pw_eqI simp: refine_pw_simps) 

lemma nres_bind_assoc[simp]: "bindT (bindT M (\<lambda>x. f x)) g = bindT M (%x. bindT (f x) g)"
  apply(auto intro!: pw_eqI simp:  refine_pw_simps)  
  using inresT_mono by fastforce+

section \<open>Monotonicity lemmas\<close>

lemma bindT_mono: 
  "m \<le> m' \<Longrightarrow> (\<And>x. (\<exists>t. inresT m x t) \<Longrightarrow> nofailT m' \<Longrightarrow>  f x \<le> f' x)
 \<Longrightarrow> bindT m f \<le> bindT  m' f'"
  apply(auto simp: pw_le_iff refine_pw_simps) 
   by fastforce+                 


lemma bindT_mono'[refine_mono]: 
  "m \<le> m' \<Longrightarrow> (\<And>x.   f x \<le> f' x)
 \<Longrightarrow> bindT m f \<le> bindT  m' f'"
  apply(rule bindT_mono) by auto
 
lemma bindT_flat_mono[refine_mono]:  
  "\<lbrakk> flat_ge M M'; \<And>x. flat_ge (f x) (f' x) \<rbrakk> \<Longrightarrow> flat_ge (bindT M f) (bindT M' f')" 
  apply (auto simp: refine_pw_simps pw_flat_ge_iff) []
   by fastforce+         


subsection {* Derived Program Constructs *}

subsubsection \<open>Assertion\<close> 

definition "iASSERT ret \<Phi> \<equiv> if \<Phi> then ret () else top"

definition ASSERT where "ASSERT \<equiv> iASSERT RETURNT"

lemma ASSERT_True[simp]: "ASSERT True = RETURNT ()" 
  by (auto simp: ASSERT_def iASSERT_def)
lemma ASSERT_False[simp]: "ASSERT False = FAILT" 
  by (auto simp: ASSERT_def iASSERT_def) 

lemma bind_ASSERT_eq_if: "do { ASSERT \<Phi>; m } = (if \<Phi> then m else FAILT)"
  unfolding ASSERT_def iASSERT_def by simp

lemma pw_ASSERT[refine_pw_simps]:
  "nofailT (ASSERT \<Phi>) \<longleftrightarrow> \<Phi>"
  "inresT (ASSERT \<Phi>) x 0"
  by (cases \<Phi>, simp_all)+

lemma ASSERT_refine: "(Q \<Longrightarrow> P) \<Longrightarrow> ASSERT P \<le> ASSERT Q"
  by(auto simp: pw_le_iff refine_pw_simps)

lemma ASSERT_leI: "\<Phi> \<Longrightarrow> (\<Phi> \<Longrightarrow> M \<le> M') \<Longrightarrow> ASSERT \<Phi> \<bind> (\<lambda>_. M) \<le> M'"
  by(auto simp: pw_le_iff refine_pw_simps)

lemma le_ASSERTI: "(\<Phi> \<Longrightarrow> M \<le> M') \<Longrightarrow> M \<le> ASSERT \<Phi> \<bind> (\<lambda>_. M')"
  by(auto simp: pw_le_iff refine_pw_simps)

lemma inresT_ASSERT: "inresT (ASSERT Q \<bind> (\<lambda>_. M)) x ta = (Q \<longrightarrow> inresT M x ta)"
  unfolding ASSERT_def iASSERT_def by auto


lemma nofailT_ASSERT_bind: "nofailT (ASSERT P \<bind> (\<lambda>_. M)) \<longleftrightarrow> (P \<and> nofailT M)"
  by(auto simp: pw_bindT_nofailT pw_ASSERT)

subsection \<open>SELECT\<close>


 
definition emb' where "\<And>Q T. emb' Q (T::'a \<Rightarrow> enat) = (\<lambda>x. if Q x then Some (T x) else None)"

abbreviation "emb Q t \<equiv> emb' Q (\<lambda>_. t)" 

lemma emb_eq_Some_conv: "\<And>T. emb' Q T x = Some t' \<longleftrightarrow> (t'=T x \<and> Q x)"
  by (auto simp: emb'_def)

lemma emb_le_Some_conv: "\<And>T. Some t' \<le> emb' Q T x \<longleftrightarrow> ( t'\<le>T x \<and> Q x)"
  by (auto simp: emb'_def)


text \<open>Select some value with given property, or \<open>None\<close> if there is none.\<close>  
definition SELECT :: "('a \<Rightarrow> bool) \<Rightarrow> enat \<Rightarrow> 'a option nrest"
  where "SELECT P tf \<equiv> if \<exists>x. P x then REST (emb (\<lambda>r. case r of Some p \<Rightarrow> P p | None \<Rightarrow> False) tf)
               else REST [None \<mapsto> tf]"

                    
lemma inresT_SELECT_Some: "inresT (SELECT Q tt) (Some x) t' \<longleftrightarrow> (Q x  \<and> (t' \<le> tt))"
  by(auto simp: inresT_def SELECT_def emb'_def) 

lemma inresT_SELECT_None: "inresT (SELECT Q tt) None t' \<longleftrightarrow> (\<not>(\<exists>x. Q x) \<and> (t' \<le> tt))"
  by(auto simp: inresT_def SELECT_def emb'_def) 

lemma inresT_SELECT[refine_pw_simps]:
 "inresT (SELECT Q tt) x t' \<longleftrightarrow> ((case x of None \<Rightarrow> \<not>(\<exists>x. Q x) | Some x \<Rightarrow> Q x)  \<and> (t' \<le> tt))"
  by(auto simp: inresT_def SELECT_def emb'_def) 


lemma nofailT_SELECT[refine_pw_simps]: "nofailT (SELECT Q tt)"
  by(auto simp: nofailT_def SELECT_def)

lemma s1: "SELECT P T \<le> (SELECT P T') \<longleftrightarrow> T \<le> T'"
  apply(cases "\<exists>x. P x") 
   apply(auto simp: pw_le_iff refine_pw_simps split: option.splits)
  subgoal 
    by (metis (full_types) enat_ord_code(3) enat_ord_simps(1) lessI not_infinity_eq not_le order_mono_setup.refl) 
  subgoal 
    by (metis (full_types) enat_ord_code(3) enat_ord_simps(1) lessI not_enat_eq not_le order_mono_setup.refl) 
  done
     
lemma s2: "SELECT P T \<le> (SELECT P' T) \<longleftrightarrow> (
    (Ex P' \<longrightarrow> Ex P)  \<and> (\<forall>x. P x \<longrightarrow> P' x)) "
  apply(auto simp: pw_le_iff refine_pw_simps split: option.splits)
  subgoal 
    by (metis enat_ile linear)                                          
  subgoal 
    by (metis enat_ile linear) 
  done
 
lemma SELECT_refine:
  assumes "\<And>x'. P' x' \<Longrightarrow> \<exists>x. P x"
  assumes "\<And>x. P x \<Longrightarrow>   P' x"
  assumes "T \<le> T'"
  shows "SELECT P T \<le> (SELECT P' T')"
proof -
  have "SELECT P T \<le> SELECT P T'"
    using s1 assms(3) by auto
  also have "\<dots> \<le> SELECT P' T'"
    unfolding s2 apply safe
    using assms(1,2) by auto  
  finally show ?thesis .
qed


section \<open>RECT\<close>

definition "mono2 B \<equiv> flatf_mono_ge B \<and>  mono B"


lemma trimonoD_flatf_ge: "mono2 B \<Longrightarrow> flatf_mono_ge B"
  unfolding mono2_def by auto

lemma trimonoD_mono: "mono2 B \<Longrightarrow> mono B"
  unfolding mono2_def by auto

definition "RECT B x = 
  (if mono2 B then (gfp B x) else (top::'a::complete_lattice))"


thm gfp_eq_flatf_gfp

lemma RECT_flat_gfp_def: "RECT B x = 
  (if mono2 B then (flatf_gfp B x) else (top::'a::complete_lattice))"
  unfolding RECT_def
  by (auto simp: gfp_eq_flatf_gfp[OF trimonoD_flatf_ge trimonoD_mono])

lemma RECT_unfold: "\<lbrakk>mono2 B\<rbrakk> \<Longrightarrow> RECT B = B (RECT B)"
  unfolding RECT_def [abs_def]  
  by (auto dest: trimonoD_mono simp: gfp_unfold[ symmetric])


definition whileT :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a nrest) \<Rightarrow> 'a \<Rightarrow> 'a nrest" where
  "whileT b c = RECT (\<lambda>whileT s. (if b s then bindT (c s) whileT else RETURNT s))"

lemma trimonoI[refine_mono]: 
  "\<lbrakk>flatf_mono_ge B; mono B\<rbrakk> \<Longrightarrow> mono2 B"
  unfolding mono2_def by auto

lemma [refine_mono]: "(\<And>f g x. (\<And>x. f x \<le> g x) \<Longrightarrow> B f x \<le> B g x) \<Longrightarrow> mono B"
  apply(rule monoI) apply(rule le_funI)
  by (simp add: le_funD)
    
thm refine_mono

lemma whileT_unfold: "whileT b c = (\<lambda>s. (if b s then bindT (c s) (whileT b c) else RETURNT s))"
  unfolding whileT_def
  apply(rule RECT_unfold) 
  by ( refine_mono)   


lemma RECT_mono[refine_mono]:
  assumes [simp]: "mono2 B'"
  assumes LE: "\<And>F x. (B' F x) \<le> (B F x) "
  shows " (RECT B' x) \<le> (RECT B x)"
  unfolding RECT_def
  apply clarsimp  
  by (meson LE gfp_mono le_fun_def)  

lemma whileT_mono: 
  assumes "\<And>x. b x \<Longrightarrow> c x \<le> c' x"
  shows " (whileT b c x) \<le> (whileT b c' x)"
  unfolding whileT_def apply(rule RECT_mono)
    subgoal by(refine_mono)  
  apply auto apply(rule bindT_mono) using assms by auto


find_theorems RECT
lemma wf_fp_induct:
  assumes fp: "\<And>x. f x = B (f) x"
  assumes wf: "wf R"
  assumes "\<And>x D. \<lbrakk>\<And>y. (y,x)\<in>R \<Longrightarrow> P y (D y)\<rbrakk> \<Longrightarrow> P x (B D x)"
  shows "P x (f x)"
  using wf
  apply induction
  apply (subst fp)
  apply fact  
  done

thm wf_fp_induct[where f="RECT B" and B=B] RECT_unfold


lemma RECT_wf_induct_aux:
  assumes wf: "wf R"
  assumes mono: "mono2 B"
  assumes "(\<And>x D. (\<And>y. (y, x) \<in> R \<Longrightarrow> P y (D y)) \<Longrightarrow> P x (B D x))"
  shows "P x (RECT B x)"
  using wf_fp_induct[where f="RECT B" and B=B] RECT_unfold assms 
     by metis 

theorem RECT_wf_induct[consumes 1]:
  assumes "RECT B x = r"
  assumes "wf R"
    and "mono2 B"
    and "\<And>x D r. (\<And>y r. (y, x) \<in> R \<Longrightarrow> D y = r \<Longrightarrow> P y r) \<Longrightarrow> B D x = r \<Longrightarrow> P x r"
  shows "P x r"
 (* using RECT_wf_induct_aux[where P = "\<lambda>x fx. \<forall>r. fx=r \<longrightarrow> P x fx"] assms by metis *)
  using RECT_wf_induct_aux[where P = "\<lambda>x fx.  P x fx"] assms by metis



definition "monadic_WHILEIT I b f s \<equiv> do {
  RECT (\<lambda>D s. do {
    ASSERT (I s);
    bv \<leftarrow> b s;
    if bv then do {
      s \<leftarrow> f s;
      D s
    } else do {RETURNT s}
  }) s
}"


term REST

(*
  flat_ge ?m ?m' \<Longrightarrow> (\<And>x. flat_ge (?f x) (?f' x)) \<Longrightarrow> flat_ge (?m \<bind> ?f) (?m' \<bind> ?f')
*)



section \<open>T - Generalized Weakest Precondition\<close>

subsection "mm"

definition mm :: "( 'a \<Rightarrow> enat option) \<Rightarrow> ( 'a \<Rightarrow> enat option) \<Rightarrow> ( 'a \<Rightarrow> enat option)" where
  "mm R m = (\<lambda>x. (case m x of None \<Rightarrow> Some \<infinity>
                                | Some mt \<Rightarrow>
                                  (case R x of None \<Rightarrow> None | Some rt \<Rightarrow> (if rt < mt then None else Some (rt - mt)))))"

lemma mm_mono: "Q1 x \<le> Q2 x \<Longrightarrow> mm Q1 M x \<le> mm Q2 M x"
  unfolding mm_def apply(cases "M x") apply (auto split: option.splits)
  using le_some_optE apply blast apply(rule helper) by auto


lemma mm_antimono: "M1 x \<ge> M2 x \<Longrightarrow> mm Q M1 x \<le> mm Q M2 x"
  unfolding mm_def   apply (auto split: option.splits)  
  apply(rule helper2) by auto


lemma mm_continous: "mm (\<lambda>x. Inf {u. \<exists>y. u = f y x}) m x = Inf {u. \<exists>y. u = mm (f y) m x}" 
  apply(rule antisym)
  subgoal apply(rule Inf_greatest) apply clarsimp
  proof (cases "Inf {u. \<exists>y. u = f y x}")
    case None
    have f: "m x \<noteq> None \<Longrightarrow> mm (\<lambda>x. Inf {u. \<exists>y. u = f y x}) m x = None" unfolding mm_def None apply(cases "m x") by (auto ) 
    then show "\<And>y. mm (\<lambda>x. Inf {u. \<exists>y. u = f y x}) m x \<le> mm (f y) m x"
      apply(cases "m x") apply(auto simp: f) unfolding mm_def by auto
  next
    case (Some l)
    then show "\<And>y. mm (\<lambda>x. Inf {u. \<exists>y. u = f y x}) m x \<le> mm (f y) m x"
      apply(cases "m x") subgoal unfolding mm_def by auto
    proof -
      fix y a assume I: "Inf {u. \<exists>y. u = f y x} = Some l" " m x = Some a"
      from I have i: "\<And>y. f y x \<ge> Some l"
        by (metis (mono_tags, lifting) Inf_lower mem_Collect_eq) 
      show "mm (\<lambda>x. Inf {u. \<exists>y. u = f y x}) m x \<le> mm (f y) m x"
        apply(rule mm_mono) unfolding I apply(rule i) .
    qed 
  qed
  subgoal   apply(rule Inf_lower) apply clarsimp 
  proof -
    have "\<exists>y. Inf {u. \<exists>y. u = f y x} = f y x"
      unfolding Inf_option_def apply auto unfolding Inf_enat_def apply auto
      apply (metis (mono_tags) empty_iff in_these_eq mem_Collect_eq option.exhaust)
      by (smt LeastI in_these_eq mem_Collect_eq)
    then obtain y where z: "Inf {u. \<exists>y. u = f y x} = f y x" by blast
    show "\<exists>y. mm (\<lambda>x. Inf {u. \<exists>y. u = f y x}) m x = mm (f y) m x"
      apply(rule exI[where x=y]) unfolding mm_def z ..
  qed
  done

definition mm2 :: "(  enat option) \<Rightarrow> (   enat option) \<Rightarrow> (   enat option)" where
  "mm2 r m = (case m  of None \<Rightarrow> Some \<infinity>
                                | Some mt \<Rightarrow>
                                  (case r of None \<Rightarrow> None | Some rt \<Rightarrow> (if rt < mt then None else Some (rt - mt))))"


lemma mm_alt: "mm R m x = mm2 (R x) (m x)" unfolding mm_def mm2_def ..

lemma mm2_None[simp]: "mm2 q None = Some \<infinity>" unfolding mm2_def by auto

lemma mm2_Some0[simp]: "mm2 q (Some 0) = q" unfolding mm2_def by (auto split: option.splits)

lemma mm2_antimono: "x \<le> y \<Longrightarrow> mm2 q x \<ge> mm2 q y"
  unfolding mm2_def apply (auto split: option.splits)
  using helper2 by blast 

lemma mm2_contiuous2: "\<forall>x\<in>X. t \<le> mm2 q x \<Longrightarrow> t \<le> mm2 q (Sup X)"
  unfolding mm2_def apply(auto simp: everywhereNone bot_option_def less_eq_option_None_is_None' split: option.splits if_splits)
  subgoal by (metis (no_types, lifting) Sup_option_def in_these_eq less_Sup_iff option.distinct(1) option.sel) 
  subgoal for tx tq by(cases tq; cases tx; fastforce dest!: Sup_finite_enat)
  done
 
lemma fl: "(a::enat) - b = \<infinity> \<Longrightarrow> a = \<infinity>"
  apply(cases b; cases a) by auto

lemma mm_inf1: "mm R m x = Some \<infinity> \<Longrightarrow> m x = None \<or> R x = Some \<infinity>"
  apply(auto simp: mm_def split: option.splits if_splits) using fl by metis

lemma mm_inf2: "m x = None \<Longrightarrow> mm R m x = Some \<infinity>" 
  by(auto simp: mm_def split: option.splits if_splits)  

lemma mm_inf3: " R x = Some \<infinity> \<Longrightarrow> mm R m x = Some \<infinity>" 
  by(auto simp: mm_def split: option.splits if_splits)  

lemma mm_inf: "mm R m x = Some \<infinity> \<longleftrightarrow> m x = None \<or> R x = Some \<infinity>"
  using mm_inf1 mm_inf2 mm_inf3  by metis

lemma "REST Map.empty \<le> SPECT Q"
  by (auto simp: le_fun_def) 

lemma InfQ_E: "Inf Q = Some t \<Longrightarrow> None \<notin> Q"
  unfolding Inf_option_def by auto

lemma InfQ_iff: "(\<exists>t'\<ge>enat t. Inf Q = Some t') \<longleftrightarrow> None \<notin> Q \<and> Inf (Option.these Q) \<ge> t"
  unfolding Inf_option_def 
  by auto
 

 
subsection "mii"

definition mii :: "('a \<Rightarrow> enat option) \<Rightarrow> 'a nrest \<Rightarrow> 'a \<Rightarrow> enat option" where 
  "mii Qf M x =  (case M of FAILi \<Rightarrow> None 
                                             | REST Mf \<Rightarrow> (mm Qf Mf) x)"


lemma mii_alt: "mii Qf M x = (case M of FAILi \<Rightarrow> None 
                                             | REST Mf \<Rightarrow> (mm2 (Qf x) (Mf x)) )"
  unfolding mii_def mm_alt ..


lemma mii_continuous: "mii (\<lambda>x. Inf {f y x|y. True}) m x = Inf {mii (%x. f y x) m x|y. True}"
  unfolding mii_def apply(cases m) subgoal apply auto done
  subgoal apply auto using mm_continous by metis 
  done

 
lemma mii_continuous2: "(mii Q (Sup {F x t1 |x t1. P x t1}) x \<ge> t) = (\<forall>y t1. P y t1 \<longrightarrow> mii Q (F y t1) x \<ge> t)"
  unfolding mii_alt apply auto apply (auto simp: nrest_Sup_FAILT less_eq_option_None_is_None' split: nrest.splits)
  subgoal by (smt nrest_Sup_FAILT(2) mem_Collect_eq nres_order_simps(1) top_greatest) 
  subgoal for y t1 x2 x2a
    apply(drule nrest_Sup_SPECT_D[where x=x])
    apply(rule order.trans[where b="mm2 (Q x) (x2 x)"]) apply simp
    apply(rule mm2_antimono) by (metis (mono_tags, lifting) Sup_upper mem_Collect_eq)
  subgoal 
    apply(drule nrest_Sup_SPECT_D[where x=x])
    by (auto intro: mm2_contiuous2) 
  done 


lemma mii_inf: "mii Qf M x = Some \<infinity> \<longleftrightarrow> (\<exists>Mf. M = SPECT Mf \<and> (Mf x = None \<or> Qf x = Some \<infinity>))"
  by (auto simp: mii_def mm_inf split: nrest.split )


lemma miiFailt: "mii Q FAILT x = None" unfolding mii_def by auto


subsection "T"

definition T :: "('a \<Rightarrow> enat option) \<Rightarrow> 'a nrest \<Rightarrow> enat option" 
  where "T Qf M =  Inf { mii Qf M x | x. True}"


lemma T_pw: "T Q M \<ge> t \<longleftrightarrow> (\<forall>x. mii Q M x \<ge> t)"
  unfolding T_def mii_def apply(cases M) apply auto
  unfolding Inf_option_def apply (auto split: if_splits)
  using less_eq_option_None_is_None less_option_None not_less apply blast
  apply (smt Inf_lower Inf_option_def dual_order.trans mem_Collect_eq)
  apply metis
  by (smt in_these_eq le_Inf_iff le_cases le_some_optE less_eq_option_Some mem_Collect_eq)  
  


lemma z: "(\<forall>t. T Q M \<ge> t \<longrightarrow> T Q' M' \<ge> t) \<Longrightarrow> T Q M \<le> T Q' M'"
  by simp

(*
section "inres2"

(* first attempt: inres2 used for showing hoare rules involving T, pointwise *)

definition "inres2 S x \<equiv> (case S of FAILi \<Rightarrow> True | REST X \<Rightarrow> (\<exists>t'. X x = Some t'))"

lemma inres2_FAILT[simp]: "inres2 FAILT r" unfolding inres2_def by simp

lemma inres2_SPECT: "inres2 (SPECT Q) x = (\<exists>t'. Q x = Some t')" unfolding inres2_def by auto

lemma pw_inres2_Sup: "inres2 (Sup X) r \<longleftrightarrow> (\<exists>M\<in>X. inres2 M r)"
  apply(rule)
  subgoal (* \<rightarrow> *)
    apply(cases "Sup X")
    subgoal by (force simp: Nrest_Sup_FAILT)
    subgoal 
      apply(auto simp: inres2_def  Sup_nrest_def split: if_splits)
      by(auto simp: SUP_eq_Some_iff split: nrest.splits)   
    done
  subgoal (* <- *)
    apply(cases "Sup X")
    subgoal by (auto simp: Nrest_Sup_FAILT top_Sup)
    subgoal 
      apply(auto simp: inres2_def  Sup_nrest_def split: if_splits)
      by(auto simp: SUP_eq_Some_iff split: nrest.splits)  
    done
  done


lemma pw_inres2_bindT_aux: "inres2 (bindT m f) r \<longleftrightarrow>
     (nofailT m \<longrightarrow> (\<exists>r'. inres2 m r'  \<and> inres2 (f r') r ))"
  apply(rule)
  subgoal (* \<rightarrow> *)
    apply(cases m)
    subgoal by auto
    subgoal apply(auto simp: bindT_def pw_inres2_Sup split: nrest.splits) 
      subgoal for M x t'
        apply(rule exI[where x=x]) 
        apply(cases "f x")     by (auto simp: inres2_def)
      subgoal for x t'
        apply(rule exI[where x=x]) by (auto simp add: inres2_def) 
      done
    done
  subgoal (* <- *)
    apply(cases m)
    subgoal by auto
    subgoal for x2
      apply (auto simp: bindT_def  split: nrest.splits)
      apply(auto simp: pw_inres2_Sup )
      subgoal for r'
        apply(cases "f r'") apply (auto simp add: inres2_def) 
        subgoal   by(force)  
        subgoal for x2a t'
          apply(rule exI[where x="REST (map_option (op + t') \<circ> x2a)"]) 
          apply auto
           apply(rule exI[where x=r'])
          by auto 
        done
      done
    done
  done

lemma pw_bindT_nofailT_2[refine_pw_simps]: "nofailT (bindT M f) \<longleftrightarrow> (nofailT M \<and> (\<forall>x. inres2 M x \<longrightarrow> nofailT (f x)))"
  unfolding bindT_def   
   apply (auto elim: no_FAILTE simp: pw_Sup_nofail inres2_SPECT  split: nrest.splits )  
  by force+ 

lemma kla: "M = SPECT Mff \<Longrightarrow> inres2 M x = (Mff x \<noteq> None)" unfolding inres2_def by (auto split: nrest.splits)

lemma "M = FAILi \<Longrightarrow> T Q M = None" unfolding T_def by (auto simp: mii_def)

lemma fall2: "M = REST Mf \<Longrightarrow> Mf x = Some t \<Longrightarrow> Q x = None \<Longrightarrow> T Q M = None"
  unfolding T_def
  apply(rule None_in_Inf)
  apply (auto simp: mii_def mm_def)
  apply(rule exI[where x=x]) by auto  

lemma fall3: "M = REST Mf \<Longrightarrow> Mf x = Some t \<Longrightarrow> Q x = Some t' \<Longrightarrow> t' < t \<Longrightarrow> T Q M = None"
  unfolding T_def
  apply(rule None_in_Inf)
  apply (auto simp: mii_def mm_def)
  apply(rule exI[where x=x]) by auto 

lemma k: "Inf S = None \<longleftrightarrow> (None \<in> S)"
  by (simp add: Inf_option_def) 
lemma k2: "None = Inf S \<longleftrightarrow> (None \<in> S)"
  by (simp add: Inf_option_def) 

lemma T_None_char: "T Q M = None \<longleftrightarrow> (M = FAILi \<or> (\<exists>Mf t x. M = REST Mf \<and> Mf x = Some t \<and> (Q x = None \<or> (\<exists>t'. Q x = Some t' \<and> t'<t))))"
  apply rule
  subgoal
    unfolding T_def k
    apply auto
    apply(cases M) apply (auto simp: mii_def mm_def split: option.splits) by force
  subgoal
    unfolding T_def
    apply(rule None_in_Inf) 
    apply (auto simp: mii_def mm_def split: option.splits ) apply force+  
    done
  done


lemma kl: "Inf S = Some (t::enat) \<longleftrightarrow> (Inf (Option.these S) = t \<and> None \<notin> S)" 
  unfolding Inf_option_def by auto 


lemma tz: "Inf S = Some (enat t) \<Longrightarrow> Inf S = (LEAST x. x \<in> S)"
  unfolding  Inf_option_def using Inf_enat_def  apply auto
  by (metis Inf_lower Inf_option_def LeastI Least_equality all_not_in_conv enat.distinct(2) in_these_eq option.sel)   


lemma assumes "T Q M = Some (enat t)" 
  shows T_SomeEnat: "(\<exists>Mf. M = REST Mf \<and> (\<exists>x t' t'' . Mf x = Some (enat t') \<and> Q x = Some (enat t'') \<and> t = t''-t' \<and> t''\<ge>t')
                           \<and> (\<forall>x t' t''. Mf x = Some (enat t') \<and> Q x = Some (enat t'') \<and> t''\<ge>t' \<longrightarrow> t \<le> t''-t' ))"
proof -
  from assms have "(LEAST t. t \<in> {mii Q M x |x. True}) = Some (enat t)" unfolding T_def using tz by metis
  then have 1: "Some (enat t)\<in> {mii Q M x |x. True}" and 2: "\<forall>e\<in>{mii Q M x |x. True}. e\<ge> Some (enat t)"
    apply (metis (mono_tags, lifting) LeastI_ex mem_Collect_eq)
    by (metis (mono_tags) Inf_lower T_def \<open>T Q M = Some (enat t)\<close>)  


  from 1 have "\<exists>x. mii Q M x = Some (enat t)" by auto
  then obtain x where "mii Q M x = Some (enat t)" by blast
  then obtain Mf where Mf: "M = SPECT Mf" and "mm Q Mf x = Some (enat t)"  unfolding mii_def
    by(auto split: nrest.splits)
  then obtain t' t'' where [simp]: "Mf x = Some t'" "Q x = Some t''" and t: "t''-t'=enat t" "t''\<ge>t'" unfolding mm_def by (auto split: option.splits if_splits)
  from t obtain t2' t2'' where e: "enat t2' = t'" "enat t2'' = t''"
    apply(cases t'; cases t'') by auto 

  from 2 have 3: "\<And>x. mii Q M x \<ge> Some (enat t)" by auto

  show "(\<exists>Mf. M = REST Mf \<and> (\<exists>x t' t'' . Mf x = Some (enat t') \<and> Q x = Some (enat t'') \<and> t = t''-t' \<and> t''\<ge>t')
                           \<and> (\<forall>x t' t''. Mf x = Some (enat t') \<and> Q x = Some (enat t'') \<and> t''\<ge>t' \<longrightarrow> t \<le> t''-t' ))"
    apply(rule exI[where x=Mf])
    apply safe apply fact
    subgoal 
      apply(rule exI[where x=x]) apply(rule exI[where x=t2']) apply(rule exI[where x=t2''])
      using t e by auto
    subgoal for x t' t''
      using 3[of x] unfolding mii_def apply(cases M) apply auto
      unfolding mm_def using Mf by(auto split: option.splits) 
    done
qed


*)


subsection "pointwise reasoning about T via nres3"


definition nres3 where "nres3 Q M x t \<longleftrightarrow> mii Q M x \<ge> t"


lemma pw_T_le:
  assumes "\<And>t. (\<forall>x. nres3 Q M x t) \<Longrightarrow> (\<forall>x. nres3 Q' M' x t)"
  shows "T Q M \<le> T Q' M'"
  apply(rule z)
  using assms unfolding T_pw nres3_def  by metis 

lemma assumes "\<And>t. (\<forall>x. nres3 Q M x t) = (\<forall>x. nres3 Q' M' x t)" 
  shows pw_T_eq_iff: "T Q M = T Q' M'"
  apply (rule antisym)
  apply(rule pw_T_le) using assms apply metis
  apply(rule pw_T_le) using assms apply metis done 

lemma assumes "\<And>t. (\<forall>x. nres3 Q M x t) \<Longrightarrow> (\<forall>x. nres3 Q' M' x t)"
      "\<And>t. (\<forall>x. nres3 Q' M' x t) \<Longrightarrow> (\<forall>x. nres3 Q M x t)"
  shows pw_T_eqI: "T Q M = T Q' M'"
  apply (rule antisym)
  apply(rule pw_T_le) apply fact
  apply(rule pw_T_le) apply fact done 


lemma t: "(\<forall>y. (t::enat option) \<le> f y) \<longleftrightarrow> (t\<le>Inf {f y|y. True})"  
  using le_Inf_iff by fastforce   

lemma lem: "\<forall>t1. M y = Some t1 \<longrightarrow> t \<le> mii Q (SPECT (map_option ((+) t1) \<circ> x2)) x \<Longrightarrow> f y = SPECT x2 \<Longrightarrow> t \<le> mii (\<lambda>y. mii Q (f y) x) (SPECT M) y"
  unfolding mii_def apply (auto split: nrest.splits)
  unfolding mm_def apply (auto split: nrest.splits)
  apply(cases "M y")
  subgoal by (auto simp: top_option_def[symmetric] top_enat_def[symmetric])
  apply simp apply(cases "x2 x") subgoal by simp
  apply simp apply(cases "Q x") subgoal by simp
  apply simp apply(auto split: if_splits)
  subgoal for a b c apply(cases a; cases b; cases c) by auto
  subgoal for a b c apply(cases a; cases b; cases c) by auto
  subgoal for a b c apply(cases a; cases b; cases c) by auto
  subgoal for a b c apply(cases a; cases b; cases c) by (auto simp add: add.commute) 
  done

lemma lem2: "t \<le> mii (\<lambda>y. mii Q (f y) x) (SPECT M) y \<Longrightarrow> M y = Some t1 \<Longrightarrow> f y = SPECT fF \<Longrightarrow> t \<le> mii Q (SPECT (map_option ((+) t1) \<circ> fF)) x"
  apply (simp add: mii_def mm_def) apply(cases "fF x") apply auto
  apply(cases "Q x") apply (auto split: if_splits)
  subgoal using less_eq_option_None_is_None less_option_None not_less by blast
  subgoal using less_eq_option_None_is_None less_option_None not_less by blast
  subgoal  for a b apply(cases a; cases b; cases t) apply auto
    by (metis add_right_mono leD le_add_diff_inverse2 le_less_linear plus_enat_simps(1))
  subgoal for a b  apply(cases a; cases b; cases t) apply auto
    by (smt add.commute add_diff_cancel_left enat_ile idiff_enat_enat le_add_diff_inverse le_less_linear plus_enat_simps(1))
  done

lemma fixes m :: "'b nrest"
  shows mii_bindT: "(t \<le> mii Q (bindT m f) x) \<longleftrightarrow> (\<forall>y. t \<le> mii (\<lambda>y. mii Q (f y) x) m y)"
proof -
  { fix M
    assume mM: "m = SPECT M"
    let ?P = "%x t1. M x = Some t1"
    let ?F = "%x t1. case f x of FAILi \<Rightarrow> FAILT | REST m2 \<Rightarrow> SPECT (map_option ((+) t1) \<circ> m2)"
    let ?Sup = "(Sup {?F x t1 |x t1. ?P x t1})" 

    { fix y 
      have "(\<forall>t1. ?P y t1 \<longrightarrow> mii Q (?F y t1) x \<ge> t)
              = (t \<le> mii (\<lambda>y. mii Q (f y) x) m y)"
        apply safe
        subgoal apply(cases "f y")
          subgoal apply (auto simp: miiFailt) 
             apply (metis mM mii_inf top_enat_def top_greatest top_option_def) 
            using less_eq_option_None_is_None less_option_None not_less by blast
          subgoal apply (simp add: mM) using lem by metis
          done
        subgoal for t1 apply(cases "f y")
          subgoal by (auto simp: miiFailt mm_def mM mii_def) 
          subgoal for fF apply(simp add: mM)
            using lem2 by metis
          done
        done
    } note blub=this


    from mM have "mii Q (bindT m f) x = mii Q ?Sup x" by (auto simp: bindT_def)
    then have "(t \<le> mii Q (bindT m f) x) = (t \<le> mii Q ?Sup x)" by simp
    also have "\<dots> = (\<forall>y t1. ?P y t1 \<longrightarrow> mii Q (?F y t1) x \<ge> t)" by (rule mii_continuous2)  
    also have "\<dots> = (\<forall>y. t \<le> mii (\<lambda>y. mii Q (f y) x) m y)" by(simp only: blub)
    finally have ?thesis .
  } note bl=this

  show ?thesis apply(cases m)
    subgoal by (simp add: mii_def)
    subgoal apply(rule bl) .
    done
qed


lemma nres3_bindT: "(\<forall>x. nres3 Q (bindT m f) x t) = (\<forall>y. nres3 (\<lambda>y. T Q (f y)) m y t)"
proof -
  have "(\<forall>x. nres3 Q (bindT m f) x t) = (\<forall>x.  t \<le> mii Q (bindT m f) x)" unfolding nres3_def by auto
  also have "\<dots> = (\<forall>x. (\<forall>y. t \<le> mii (\<lambda>y. mii Q (f y) x) m y))" by(simp only: mii_bindT)
  also have "\<dots> = (\<forall>y. (\<forall>x. t \<le> mii (\<lambda>y. mii Q (f y) x) m y))" by blast
  also have "\<dots> = (\<forall>y.  t \<le> mii (\<lambda>y. Inf {mii Q (f y) x|x. True}) m y)" 
    apply(simp only: mii_continuous) using t by fast
  also have "\<dots> = (\<forall>y.  t \<le> mii (\<lambda>y. T Q (f y)) m y)" unfolding T_def by auto
  also have "\<dots> = (\<forall>y. nres3 (\<lambda>y. T Q (f y)) m y t)" unfolding nres3_def by auto
  finally show ?thesis .
  have "(\<forall>y.  t \<le> mii (\<lambda>y. T Q (f y)) m y) = (t \<le> Inf{ mii (\<lambda>y. T Q (f y)) m y|y. True})" using t by metis
qed


subsection "rules for T"

lemma T_bindT: "T Q (bindT M f) = T (\<lambda>y. T Q (f y)) M"
  by (rule pw_T_eq_iff, rule nres3_bindT)


definition "lst c Q = (\<lambda>s. T Q (c s))"
lemma "lst (%x. bindT (M x) f) Q = lst M (lst f Q)"
  unfolding lst_def apply rule by (simp only: T_bindT) 


lemma T_REST: "T Q (REST [x\<mapsto>t]) = mm2 (Q x) (Some t)"
proof- 
  have *: "Inf {uu. \<exists>xa. (xa = x \<longrightarrow> uu= v) \<and> (xa \<noteq> x \<longrightarrow> uu = Some \<infinity>)} = v"  (is "Inf ?S = v") for v :: "enat option"
  proof -
    have "?S \<in> { {v} \<union> {Some \<infinity>}, {v}  }" by auto 
    then show ?thesis apply simp apply safe by (simp_all add: top_enat_def[symmetric] top_option_def[symmetric] ) 
  qed
  then show ?thesis
    unfolding T_def mii_alt by auto
qed


lemma T_RETURNT: "T Q (RETURNT x) = Q x"
  unfolding RETURNT_alt apply(rule trans) apply(rule T_REST) by simp
                
thm T_pw

find_theorems "Inf _ = Some _"  


lemma aux1: "Some t \<le> mm2 Q (Some t') \<longleftrightarrow> Some (t+t') \<le> Q"
  apply (auto simp: mm2_def split: option.splits)
  subgoal for t''
    by (cases t; cases t'; cases t''; auto)
  subgoal for t''
    by (cases t; cases t'; cases t''; auto)
  subgoal for t''
    by (cases t; cases t'; cases t''; auto)
  done

lemma aux1a: "(\<forall>x t''. Q' x = Some t'' \<longrightarrow> (Q x) \<ge> Some (t + t''))
      = (\<forall>x. mm2 (Q x) (Q' x) \<ge> Some t) " 
  apply (auto simp: )
  subgoal for x apply(cases "Q' x") apply simp
    by(simp add: aux1)  
  subgoal for x t'' using aux1 by metis
  done

thm aux1a[where Q="%_. Q" and Q'="%_. Q'" for Q Q', simplified]

lemma aux1a': "(\<forall>t''. Q' = Some t'' \<longrightarrow> (Q) \<ge> Some (t + t''))
      = (mm2 (Q) (Q') \<ge> Some t) " 
  apply (auto simp: )
  subgoal apply(cases "Q'") apply simp
    by(simp add: aux1)  
  subgoal for t'' using aux1 by metis
  done

lemma "T Q (SPECT P) \<ge> Some t \<longleftrightarrow> (\<forall>x t'. P x = Some t' \<longrightarrow> (Q x \<ge> Some (t + t')))"
  apply (auto simp: T_pw mii_alt)
  apply (metis aux1)
  apply (simp add: aux1a'[symmetric])
  done


lemma "T Q (SPECT P) \<ge> Some t \<longleftrightarrow> (\<forall>x t'. P x = Some t' \<longrightarrow> (\<exists>t''. Q x = Some t'' \<and> t'' \<ge> t + t'))"
  apply (auto simp: T_pw mii_alt )
   apply (metis aux1 le_some_optE)
  apply (simp add: aux1a'[symmetric])
  apply auto 
  by fastforce

lemma "T Q (SPECT P) = Some t \<longleftrightarrow> (\<forall>x t'. P x = Some t' \<longrightarrow> (\<exists>t''. Q x = Some t'' \<and> t'' = t + t'))"
  apply (auto simp: T_def ) oops


lemma T_SELECT: 
  assumes  
    "\<forall>x. \<not> P x \<Longrightarrow> Some tt \<le> T Q (SPECT [None \<mapsto> tf])"
  and p: "(\<And>x. P x \<Longrightarrow> Some tt \<le> T Q (SPECT [Some x \<mapsto> tf]))"
   shows "Some tt \<le> T Q (SELECT P tf)"
proof(cases "\<exists>x. P x")
  case True
  from p[unfolded T_pw mii_alt] have
    p': "\<And>y x. P y \<Longrightarrow> Some tt \<le> mm2 (Q x)([Some y \<mapsto> tf] x)"
    by auto

  from True 
  show ?thesis 
    unfolding SELECT_def apply (auto simp: emb'_def split: if_splits)
    apply(auto simp: T_pw) subgoal for x xa apply(cases xa)
      apply (simp add: mii_alt)
      apply (simp add: mii_alt) apply safe subgoal for a
        using p'[of a xa] by auto
      done
    done
next
  case False
  then show ?thesis 
    unfolding SELECT_def apply (auto simp: emb'_def split: if_splits) using assms by auto
qed 


              
section "Experimental Hoare reasoning"


lemma aux1': "Some t \<le> mm2 Q (Some t') \<longleftrightarrow> Some (t+t') \<le> Q"
  apply (auto simp: mm2_def split: option.splits)
  subgoal for t''
    by (cases t; cases t'; cases t''; auto)
  subgoal for t''
    by (cases t; cases t'; cases t''; auto)
  subgoal for t''
    by (cases t; cases t'; cases t''; auto)
  done 

lemma T_conseq4:
  assumes 
    "T Q' f \<ge> Some t'"
    "\<And>x t'' M. Q' x = Some t'' \<Longrightarrow> (Q x) \<ge> Some ((t - t') + t'')" 
  shows "T Q f \<ge> Some t"
proof -
  {
    fix x
    from assms(1)[unfolded T_pw] have i: "Some t' \<le> mii Q' f x" by auto
    from assms(2) have ii: "\<And>t''. Q' x = Some t'' \<Longrightarrow> (Q x) \<ge> Some ((t - t') + t'')" by auto
    from i ii have "Some t \<le> mii Q f x"
      unfolding mii_alt apply(auto split: nrest.splits)
      subgoal for x2 apply(cases "x2 x") apply simp
        apply(simp add: aux1)  
        apply(cases "Q' x") apply simp
        apply auto 
        apply(cases "Q x") apply auto 
        subgoal for a b c apply(cases t; cases t'; cases a; cases b; cases c) apply auto
          using le_add2 by force
        done
      done
  } 
  thus ?thesis
    unfolding T_pw ..
qed
(*
lemma T_conseq44:
  assumes 
    "T Q' f \<ge> Some t'"
    "\<And>x t'' M. Q' x = Some t'' \<Longrightarrow> (Q x) \<ge> Some ((t - t') + t'')" 
  shows "T Q f \<ge> Some t"
proof -
  { assume "T Q f = Some \<infinity>"
    then have "False" unfolding T_def 

  {
    fix x
    from assms(1)[unfolded T_pw] have i: "Some t' \<le> mii Q' f x" by auto
    from assms(2) have ii: "\<And>t''. Q' x = Some t'' \<Longrightarrow> (Q x) \<ge> Some ((t - t') + t'')" by auto
    from i ii have "Some t \<le> mii Q f x"
      unfolding mii_alt apply(auto split: nrest.splits)
      subgoal for x2 apply(cases "x2 x") apply simp
        apply(simp add: aux1)  
        apply(cases "Q' x") apply simp
        apply auto 
        apply(cases "Q x") apply auto 
        subgoal for a b c apply(cases t; cases t'; cases a; cases b; cases c) apply auto
          using le_add2 by force
        done
      done
  } 
  thus ?thesis
    unfolding T_pw ..
qed*)


lemma T_conseq6:
  assumes 
    "T Q' f \<ge> Some t"
    "\<And>x t'' M. f = SPECT M \<Longrightarrow> M x \<noteq> None \<Longrightarrow> Q' x = Some t'' \<Longrightarrow> (Q x) \<ge> Some ( t'')" 
  shows "T Q f \<ge> Some t"
proof -
  {
    fix x
    from assms(1)[unfolded T_pw] have i: "Some t \<le> mii Q' f x" by auto
    from assms(2) have ii: "\<And>t'' M.  f = SPECT M \<Longrightarrow> M x \<noteq> None \<Longrightarrow> Q' x = Some t'' \<Longrightarrow> (Q x) \<ge> Some ( t'')" by auto
    from i ii have "Some t \<le> mii Q f x"
      unfolding mii_alt apply(auto split: nrest.splits)
      subgoal for x2 apply(cases "x2 x") apply simp
        apply(simp add: aux1)  
        apply(cases "Q' x") apply simp
        apply auto 
        apply(cases "Q x") apply auto 
        subgoal for a b c apply(cases t;  cases a; cases b; cases c) apply auto
          using le_add2 by force
        done
      done
  } 
  thus ?thesis
    unfolding T_pw ..
qed

lemma T_conseq5:
  assumes 
    "T Q' f \<ge> Some t'"
    "\<And>x t'' M. f = SPECT M \<Longrightarrow> M x \<noteq> None \<Longrightarrow> Q' x = Some t'' \<Longrightarrow> (Q x) \<ge> Some ((t - t') + t'')" 
  shows "T Q f \<ge> Some t"
proof -
  {
    fix x
    from assms(1)[unfolded T_pw] have i: "Some t' \<le> mii Q' f x" by auto
    from assms(2) have ii: "\<And>t'' M.  f = SPECT M \<Longrightarrow> M x \<noteq> None \<Longrightarrow> Q' x = Some t'' \<Longrightarrow> (Q x) \<ge> Some ((t - t') + t'')" by auto
    from i ii have "Some t \<le> mii Q f x"
      unfolding mii_alt apply(auto split: nrest.splits)
      subgoal for x2 apply(cases "x2 x") apply simp
        apply(simp add: aux1)  
        apply(cases "Q' x") apply simp
        apply auto 
        apply(cases "Q x") apply auto 
        subgoal for a b c apply(cases t; cases t'; cases a; cases b; cases c) apply auto
          using le_add2 by force
        done
      done
  } 
  thus ?thesis
    unfolding T_pw ..
qed


lemma T_conseq3: 
  assumes 
    "T Q' f \<ge> Some t'"
    "\<And>x. mm2 (Q x) (Q' x) \<ge> Some (t - t')" 
  shows "T Q f \<ge> Some t"
  using assms T_conseq4 aux1a by metis



definition P where "P f g = bindT f (\<lambda>x. bindT g (\<lambda>y. RETURNT (x+(y::nat))))"

named_theorems vcg_rules

method vcg uses rls = ((rule rls vcg_rules[THEN T_conseq4] | clarsimp simp: emb_eq_Some_conv emb_le_Some_conv T_bindT T_RETURNT)+)




lemma assumes
  f_spec[vcg_rules]: "T ( emb' (\<lambda>x. x > 2) (enat o (( *) 2)) ) f \<ge> Some 0"
and 
  g_spec[vcg_rules]: "T ( emb' (\<lambda>x. x > 2) (enat) ) g \<ge> Some 0"
shows "T ( emb' (\<lambda>x. x > 5) (enat o ( *) 3) ) (P f g) \<ge> Some 0"
proof -
  have ?thesis
    unfolding P_def
    apply vcg
    done  

  have ?thesis
    unfolding P_def
    apply(simp add: T_bindT )
    apply(simp add:  T_RETURNT)
    apply(rule T_conseq4[OF f_spec])
      apply(clarsimp simp: emb_eq_Some_conv)
    apply(rule T_conseq4[OF g_spec])
    apply (clarsimp simp: emb_eq_Some_conv emb_le_Some_conv)
    done
  thus ?thesis .
qed


hide_const P





find_theorems "T _ _ \<ge> _"

lemma [simp]: "mm2 None q = (case q of None \<Rightarrow> Some \<infinity> | _ \<Rightarrow> None)"
  apply (cases q) apply (auto simp: mm2_def) done

thm mm2_def
term mii

lemma [simp]: "a - enat n = \<infinity> \<longleftrightarrow> a=\<infinity>" by (cases a) auto
lemma [simp]: "a - enat n = enat m \<longleftrightarrow> (\<exists>k. a=enat k \<and> m = k - n)" by (cases a) auto

lemma auxXX1: "Some t \<le> mm2 (Q x) (Some t') \<Longrightarrow> Some t' \<le> mm2 (Q x) (Some t)"
  apply (auto simp: mm2_def split: option.splits if_splits)
  apply (metis helper2 idiff_0_right leD less_le_trans zero_le) 
  apply (auto simp: less_eq_enat_def split: enat.splits)
  done


definition "TSPEC Q m \<equiv> T Q m \<ge> Some 0"

lemma "TSPEC Q m \<longleftrightarrow> (case m of FAILi \<Rightarrow> False | REST M \<Rightarrow> 
  \<forall>x. mm2 (Q x) (M x) \<ge> Some 0
)"
  by (auto simp: T_pw TSPEC_def mii_alt split: option.splits nrest.splits)


lemma fold_TSPEC: "T Q m \<ge> Some t \<longleftrightarrow> TSPEC (\<lambda>x. mm2 (Q x) (Some t)) m"
  apply (auto simp: TSPEC_def T_pw mii_alt split: option.splits nrest.splits simp: aux1a'[where t=0, symmetric, simplified])

  subgoal for x
    apply (drule spec[where x=x])
    apply (auto simp: auxXX1)
    done

  subgoal for x f
    apply (drule spec[where x=x])
    apply (cases "f x")
    apply (auto simp: auxXX1)
    done
  done



lemma enat_minus_mono: "a' \<ge> b \<Longrightarrow> a' \<ge> a \<Longrightarrow> a' - b \<ge> (a::enat) - b"
  apply(cases a; cases b; cases a') by auto

lemma waux1: "(\<forall>s t'. I s = Some t' \<longrightarrow> b s  \<longrightarrow> c s \<noteq> FAILi \<and>  T (Q s) (c s) \<ge> Some t')
    = (T (\<lambda>s. T (Q s) (c s)) (SPECT (\<lambda>x. if b x then I x else None)) \<ge> Some 0)"
  apply(subst (2)T_pw) unfolding mii_alt apply simp
  apply (auto simp: mm2_def split: option.splits)
  subgoal by force  
  subgoal by force
  subgoal by (simp add: T_def miiFailt)
  subgoal by (metis (no_types, lifting) Inf_option_def T_def leI less_option_Some)
  done  


lemma waux2: "(\<forall>s t'. I s = Some t' \<longrightarrow> T (\<lambda>x. if b x then None else I x) (whileT b c s) \<ge> Some t')
      = (T (\<lambda>s. T (\<lambda>x. if b x then None else I x) (whileT b c s)) (SPECT I) \<ge> Some 0)"  
  apply(subst (2) T_pw) unfolding mii_alt apply simp
  by (force simp: mm2_def split: option.splits)  

lemma T_ineq_D: "Some t' \<le> T I (c x) \<Longrightarrow> (\<exists>M. c x = SPECT M \<and> mm2 (I y) (M y)  \<ge> Some t')"
  unfolding T_pw mii_alt apply (auto split: nrest.splits) using nrest_noREST_FAILT by blast 


lemma
  assumes "whileT b c s = r"
  assumes IS: "\<And>s t'. I s = Some t' \<Longrightarrow> b s  \<Longrightarrow> c s \<noteq> FAILi \<and>  T I (c s) \<ge> Some t'"
    (*  "T (\<lambda>x. T I (c x)) (SPECT (\<lambda>x. if b x then I x else None)) \<ge> Some 0" *) 
  assumes "I s = Some t'"
  assumes wf: "wf {(y, x)|x M y. I x \<noteq> None \<and> b x \<and> c x = SPECT M \<and> M y \<noteq> None}"
  shows whileT_rule: "T (\<lambda>x. if b x then None else I x) r \<ge> Some t'"
  using assms(1,3)
  unfolding whileT_def
proof (induction arbitrary: t' rule: RECT_wf_induct[where R="{(y, x)|x M y. I x \<noteq> None \<and> b x \<and> c x = SPECT M \<and> M y \<noteq> None}"])
  case 1
  show ?case by fact
next
  case 2
  then show ?case by refine_mono 
next
  case step: (3 x D r t')

  { assume b:"b x"
    with  IS step(3) have pff: "Some t' \<le> T I (c x)" and cnofail: "c x \<noteq> FAILi" by auto
    from b step(2) have r: "r = bindT (c x) D" by auto
    from cnofail obtain M where cM: "c x = SPECT M" by force

    from step(3) pff have inf: "I x \<le> T I (c x)" by auto

    have k: "\<And>y. M y \<noteq> None \<Longrightarrow> I y \<noteq> None"
      using inf[unfolded T_pw cM mii_alt] by (auto simp: mm2_def step(3) split: option.splits) 

    { fix y t''
      have " None \<noteq> M y \<Longrightarrow> I y = Some t'' \<Longrightarrow> Some t'' \<le> T (\<lambda>x. if b x then None else I x) (D y)"
        apply(rule step(1)[where y=y])
        subgoal apply auto subgoal using step(3) by auto subgoal using b by simp apply(rule exI[where x=M]) using cM  
          using leI by fastforce          
         apply simp   by metis
    } note pf=this

    { fix y

      from step(3) inf have pot_pays: "\<And>y. I x \<le> mm2 (I y) (M y)" unfolding T_pw mii_alt using cM by (auto split: nrest.splits)
      from pot_pays have ineq: "I x \<le> mm2 (I y) (M y)" by auto 

      have " Some t' \<le> mii (\<lambda>y. T (\<lambda>x. if b x then None else I x) (D y)) (c x) y" 
        unfolding mii_alt using cM apply(auto split: nrest.splits) 
        unfolding mm2_def apply (auto split: option.splits)
        subgoal using pf  
          by (metis (no_types, lifting) Inf_option_def RETURNT_alt T_RETURNT T_def k less_eq_option_Some_None option.distinct(1))
      proof - 
        fix th tn  (* time that we have, time that we need *)
        assume  My: "M y = Some tn" and T: "T (\<lambda>x. if b x then None else I x) (D y) = Some th" 

        from ineq obtain tiy where Iy: "I y = Some tiy" using My step(3) by(auto simp: mm2_def split: if_splits option.splits)
        with ineq My step(3) have 2: "tiy \<ge> tn" and a2: "t' \<le> tiy - tn" by (auto simp: mm2_def split: if_splits) 
        from cM My pf have "Some tiy \<le> T (\<lambda>x. if b x then None else I x) (D y)" by (simp add: \<open>I y = Some tiy\<close>)
        with T have 3: "tiy \<le> th" by simp

        { assume less: "th < tn"
          from 3 2 less show False by simp
        } 
        {
          assume notless: "~ th < tn"
          from notless have "tn \<le> th" by auto
          from enat_minus_mono[OF this 3]   have "tiy - tn \<le> th - tn" by auto
          with a2 show "t' \<le> th - tn" by auto 
        } 
      qed 
    }
    then have "Some t' \<le> T (\<lambda>x. if b x then None else I x) (bindT (c x) D)"
      apply(simp add: T_bindT) unfolding T_pw by auto
    then have ?case unfolding r by auto
  }
  moreover
  {
    assume nb: "\<not> b x"
    with  step(2) have "r = RETURNT x" by auto
    then have ?case using nb step(3) by (simp add: T_RETURNT)
  }
  ultimately have i: ?case by auto

  thm step.IH
  note IH = step.IH[OF _ refl]
  note IS' = IS[THEN conjunct2]
  note step.hyps[symmetric, simp]   

  from step.prems
  have ?case 
    apply clarsimp apply safe
    subgoal 
      apply vcg           
      apply (rule T_conseq6)  
        apply (rule IS')
      apply simp_all
      apply (rule T_conseq6)
        apply (rule IH)
      subgoal for y  by simp 
      apply simp
      by (auto split: if_splits) 
    subgoal by vcg
    done 
  from i show ?case .
qed




named_theorems vcg_simp_rules
lemmas [vcg_simp_rules] = (* T_bindT *) T_RETURNT

lemma TbindT_I: "Some t \<le>  T (\<lambda>y. T Q (f y)) M \<Longrightarrow>  Some t \<le> T Q (M \<bind> f)"
  by(simp add: T_bindT)

method vcg' uses rls = ((rule rls TbindT_I vcg_rules[THEN T_conseq6] | clarsimp split: if_splits simp:  vcg_simp_rules)+)

lemma
  assumes "whileT b c s = r"
  assumes IS[vcg_rules]: "\<And>s t'. I s = Some t' \<Longrightarrow> b s 
           \<Longrightarrow>    T (\<lambda>s'. if (s',s)\<in>R then I s' else None) (c s) \<ge> Some t'"
    (*  "T (\<lambda>x. T I (c x)) (SPECT (\<lambda>x. if b x then I x else None)) \<ge> Some 0" *) 
  assumes "I s = Some t"
  assumes wf: "wf R"
  shows whileT_rule'': "T (\<lambda>x. if b x then None else I x) r \<ge> Some t"
  using assms(1,3)
  unfolding whileT_def
proof (induction arbitrary: t rule: RECT_wf_induct[where R="R"])
  case 1  
  show ?case by fact
next
  case 2
  then show ?case by refine_mono
next
  case step: (3 x D r t') 
  note IH[vcg_rules] = step.IH[OF _ refl] 
  note step.hyps[symmetric, simp]   

  from step.prems
  show ?case 
    apply clarsimp
    apply safe 
    by vcg'      
qed


lemma
  assumes "whileT b c s = r"
  assumes IS[vcg_rules]: "\<And>s t'. I s = Some t' \<Longrightarrow> b s 
           \<Longrightarrow>    T (\<lambda>s'. if (s',s)\<in>R then I s' else None) (c s) \<ge> Some t'"
    (*  "T (\<lambda>x. T I (c x)) (SPECT (\<lambda>x. if b x then I x else None)) \<ge> Some 0" *) 
  assumes "I s = Some t"
  assumes wf: "wf R"
  assumes exit: "\<And>s t'. I s = Some t' \<Longrightarrow> \<not>b s \<Longrightarrow> Q s \<ge> Some t'"
  shows whileT_rule''a_: "T Q r \<ge> Some t"
  using assms(1,3)
  unfolding whileT_def
proof (induction arbitrary: t rule: RECT_wf_induct[where R="R"])
  case 1  
  show ?case by fact
next
  case 2
  then show ?case by refine_mono
next
  case step: (3 x D r t') 
  note IH[vcg_rules] = step.IH[OF _ refl] 
  note step.hyps[symmetric, simp]   

  from step.prems
  show ?case 
    apply clarsimp
    apply safe 
    apply vcg'   using exit by simp
qed



lemma mm2_refl: "A < \<infinity> \<Longrightarrow> mm2 (Some A) (Some A) = Some 0"
  unfolding mm2_def by auto
 
definition mm3 where
  "mm3 t A = (case A of None \<Rightarrow> None | Some t' \<Rightarrow> if t'\<le>t then Some (enat (t-t')) else None)"

lemma [simp]: "mm3 t0 (Some t0) = Some 0"  by (auto simp: mm3_def zero_enat_def)

lemma mm3_Some_conv: "(mm3 t0 A = Some t) = (\<exists>t'. A = Some t' \<and> t0 \<ge> t' \<and> t=t0-t')"
  unfolding mm3_def by(auto split: option.splits)

lemma [simp]: "mm3 t0 None = None" unfolding mm3_def by auto

lemma T_FAILT[simp]: "T Q FAILT = None"
  unfolding T_def mii_alt by simp

definition "progress m \<equiv> \<forall>s' M. m = SPECT M \<longrightarrow> M s' \<noteq> None \<longrightarrow> M s' > Some 0"
lemma progressD: "progress m \<Longrightarrow> m=SPECT M \<Longrightarrow> M s' \<noteq> None \<Longrightarrow> M s' > Some 0"
  by (auto simp: progress_def)

lemma [simp]: "progress FAILT" by(auto simp: progress_def)



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
  apply (auto simp: progress_def)
  done


lemma progress_SPECT_emb[progress_rules]: "t > 0 \<Longrightarrow> progress (SPECT (emb P t))" by(auto simp: progress_def emb'_def)


lemma Sup_Some: "Sup (S::enat option set) = Some e \<Longrightarrow> \<exists>x\<in>S. (\<exists>i. x = Some i)"
  unfolding Sup_option_def by (auto split: if_splits)

lemma progress_bind[progress_rules]: assumes "progress m \<or> (\<forall>x. progress (f x))"
  shows "progress (m\<bind>f)"
proof  (cases m)
  case FAILi
  then show ?thesis by (auto simp: progress_def)
next
  case (REST x2)   
  then show ?thesis unfolding  bindT_def progress_def apply safe
  proof (goal_cases)
    case (1 s' M y)
    let ?P = "\<lambda>fa. \<exists>x. f x \<noteq> FAILT \<and>
             (\<exists>t1. \<forall>x2a. f x = SPECT x2a \<longrightarrow> fa = map_option ((+) t1) \<circ> x2a \<and> x2 x = Some t1)"
    from 1 have A: "Sup {fa s' |fa. ?P fa} = Some y" apply simp
      apply(drule nrest_Sup_SPECT_D[where x=s']) by (auto split: nrest.splits)
    from Sup_Some[OF this] obtain fa i where P: "?P fa" and 3: "fa s' = Some i"   by blast 
    then obtain   x t1 x2a  where  a3: "f x = SPECT x2a"
      and "\<forall>x2a. f x = SPECT x2a \<longrightarrow> fa = map_option ((+) t1) \<circ> x2a" and a2: "x2 x = Some t1"  
      by fastforce 
    then have a1: " fa = map_option ((+) t1) \<circ> x2a" by auto
    have "progress m \<Longrightarrow> t1 > 0" apply(drule progressD)
      using 1(1) a2 a1 a3 by auto  
    moreover
    have "progress (f x) \<Longrightarrow> x2a s' > Some 0"  
      using   a1 1(1) a2 3  by (auto dest!: progressD[OF _ a3])   
    ultimately
    have " t1 > 0 \<or> x2a s' > Some 0" using assms by auto

    then have "Some 0 < fa s'" using   a1  3 by auto
    also have "\<dots> \<le> Sup {fa s'|fa. ?P fa}" 
      apply(rule Sup_upper) using P by blast
    also have "\<dots> = M s'" using A 1(3) by simp
    finally show ?case .
  qed 
qed


lemma mm2SomeleSome_conv: "mm2 (Qf) (Some t) \<ge> Some 0 \<longleftrightarrow> Qf \<ge> Some t"
  unfolding mm2_def  by (auto split: option.split)                              
 


lemma
  fixes I :: "'a \<Rightarrow> nat option"
  assumes "whileT b c s0 = r"
  assumes progress: "\<And>s. progress (c s)" 
  assumes IS[vcg_rules]: "\<And>s t t'. I s = Some t \<Longrightarrow>  b s  \<Longrightarrow> 
           T (\<lambda>s'. mm3 t (I s') ) (c s) \<ge> Some 0"
    (*  "T (\<lambda>x. T I (c x)) (SPECT (\<lambda>x. if b x then I x else None)) \<ge> Some 0" *) 
  assumes [simp]: "I s0 = Some t0" 
    (*  assumes wf: "wf R" *)                         
  shows whileT_rule''': "T (\<lambda>x. if b x then None else mm3 t0 (I x)) r \<ge> Some 0"  
  apply(rule T_conseq4)
   apply(rule whileT_rule''[where I="\<lambda>s. mm3 t0 (I s)"
        and R="measure (the_enat o the o I)", OF assms(1)])
     apply auto
  subgoal for s t'
    apply(cases "I s"; simp)
    subgoal for ti
      using IS[of s ti]  
      apply (cases "c s"; simp) 
      subgoal for M
        using progress[of s, THEN progressD, of M]
        apply(auto simp: T_pw) 
        apply(auto simp: mm3_Some_conv mii_alt mm2_def mm3_def split: option.splits if_splits)
            apply fastforce 
        subgoal 
          by (metis enat_ord_simps(1) le_diff_iff le_less_trans option.distinct(1)) 
        subgoal 
          by (metis diff_is_0_eq' leI less_option_Some option.simps(3) zero_enat_def) 
        subgoal 
          by (smt Nat.add_diff_assoc enat_ile enat_ord_code(1) idiff_enat_enat leI le_add_diff_inverse2 nat_le_iff_add option.simps(3)) 
        subgoal 
          using dual_order.trans by blast 
        done
      done
    done
  done


definition  whileIET :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> nat) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a nrest) \<Rightarrow> 'a \<Rightarrow> 'a nrest" where
  "\<And>E c. whileIET I E b c = whileT b c"
 

lemma  whileIET_rule[THEN T_conseq6, vcg_rules]:
  fixes E
  assumes 
    "(\<And>s t t'.
    (if I s then Some (E s) else None) = Some t \<Longrightarrow>
    b s \<Longrightarrow> Some 0 \<le> T (\<lambda>s'. mm3 t (if I s' then Some (E s') else None)) (C s))" 
  "\<And>s. progress (C s)"
  "I s0" 
shows "Some 0 \<le> T (\<lambda>x. if b x then None else mm3 (E s0) (if I x then Some (E x) else None)) (whileIET I E b C s0)"
  unfolding whileIET_def  
  apply(rule whileT_rule'''[OF refl, where I="(\<lambda>e. if I e
                then Some (E e) else None)"])
  using assms by auto 

 

lemma transf:
  assumes "I s \<Longrightarrow>  b s \<Longrightarrow> Some 0 \<le> T (\<lambda>s'. mm3 (E s) (if I s' then Some (E s') else None)) (C s)" 
  shows "
    (if I s then Some (E s) else None) = Some t \<Longrightarrow>
    b s \<Longrightarrow> Some 0 \<le> T (\<lambda>s'. mm3 t (if I s' then Some (E s') else None)) (C s)"
 apply(cases "I s")
  subgoal apply simp
    using assms by auto
    subgoal by simp
    done

  thm mm3_def mm2_def


lemma  whileIET_rule':
  fixes E
  assumes 
    "(\<And>s t t'. I s \<Longrightarrow>  b s \<Longrightarrow> Some 0 \<le> T (\<lambda>s'. mm3 (E s) (if I s' then Some (E s') else None)) (C s))" 
  "\<And>s. progress (C s)"
  "I s0" 
shows "Some 0 \<le> T (\<lambda>x. if b x then None else mm3 (E s0) (if I x then Some (E x) else None)) (whileIET I E b C s0)" 
  apply(rule whileIET_rule) apply(rule transf[where b=b]) using assms by auto  
   

lemma 
  assumes IS: "T (\<lambda>s. T (\<lambda>s'. if (s',s)\<in>R then I s' else None) (c s)) (SPECT (\<lambda>x. if b x then I x else None)) \<ge> Some 0" 
  assumes wf: "wf R"
  shows whileT_rule''_: "T (\<lambda>s. T (\<lambda>x. if b x then None else I x) (whileT b c s)) (SPECT I) \<ge> Some 0"
  using IS   unfolding  waux1[symmetric] unfolding  waux2[symmetric]  using whileT_rule''[OF _ _ _ wf]
  by blast
 

lemma
  assumes "whileT b c s = r"
  assumes IS[vcg_rules]: "\<And>s t'. I s = Some t' \<Longrightarrow> b s  \<Longrightarrow> T I (c s) \<ge> Some t'"
    (*  "T (\<lambda>x. T I (c x)) (SPECT (\<lambda>x. if b x then I x else None)) \<ge> Some 0" *) 
  assumes "I s = Some t'"
  assumes wf: "wf {(y, x)|x M y. I x \<noteq> None \<and> b x \<and> c x = SPECT M \<and> M y \<noteq> None}"
  shows whileT_rule': "T (\<lambda>x. if b x then None else I x) r \<ge> Some t'"
  using assms(1,3)
  unfolding whileT_def
proof (induction arbitrary: t' rule: RECT_wf_induct[where R="{(y, x)|x M y. I x \<noteq> None \<and> b x \<and> c x = SPECT M \<and> M y \<noteq> None}"])
  case 1
  show ?case by fact
next
  case 2
  then show ?case by refine_mono
next
  case step: (3 x D r t')

  note IH[vcg_rules] = step.IH[OF _ refl]
  note step.hyps[symmetric, simp]   

  from step.prems
  show ?case 
    apply clarsimp
    apply safe
     apply vcg'  
    done 
qed


print_statement waux1
lemma 
  assumes IS: "T (\<lambda>s. T I (c s)) (SPECT (\<lambda>x. if b x then I x else None)) \<ge> Some 0" 
  assumes wf: "wf {(y, x)|x M y. I x \<noteq> None \<and> b x \<and> c x = SPECT M \<and> M y \<noteq> None}"
  shows whileT_rule_: "T (\<lambda>s. T (\<lambda>x. if b x then None else I x) (whileT b c s)) (SPECT I) \<ge> Some 0"
  using IS unfolding  waux1[symmetric] waux2[symmetric]  using whileT_rule[OF _ _ _ wf] by blast


print_statement RECT_wf_induct



subsubsection "Examples"




lemma 
  assumes c: "c = (\<lambda>s. SPECT [s-1\<mapsto>1])" 
      and n: "S\<le>n"
  shows ex4: "T (\<lambda>s. if s = 0 then Some (enat n) else None) (whileT (\<lambda>s. s>0) c (S::nat)) \<ge> Some 0"
  apply(rule T_conseq4)
   apply(rule whileT_rule'''[where I="\<lambda>s. if s\<le>n then Some (s) else None" ])
      apply simp
  subgoal unfolding c unfolding progress_def by (auto split: if_splits simp add:  )
  subgoal unfolding c apply(auto simp: T_REST split: if_splits) 
    by(auto simp: mm2_def mm3_def one_enat_def)
  using n by (auto simp: mm3_Some_conv split: if_splits) 

lemma Refinement_by_T: assumes "T Q m \<ge> Some 0"
  shows "m \<le> SPECT Q"
  apply(simp add:  pw_le_iff )
  apply(cases m) 
   subgoal using assms by (simp add: mii_alt)
   subgoal for M apply auto
     subgoal for x t t' using assms[unfolded T_pw, THEN spec, of x]
       by(auto simp: mii_alt mm2_def split: option.splits if_splits)
     done
   done

lemma assumes "c = (\<lambda>s. SPECT [s-1\<mapsto>1])" 
      and n: "S\<le>n"
      shows ex4': "(whileT (\<lambda>s. s>0) c (S::nat)) \<le> SPECT (\<lambda>s. if s = 0 then Some (enat n) else None)"
  apply(rule Refinement_by_T) 
  apply(rule ex4) using assms by auto

lemma 
  assumes c: "c = (\<lambda>s. SPECT [s-1\<mapsto>1])" 
      and n: "S\<le>n"
  shows "T (\<lambda>s. if s = 0 then Some (enat n) else None) (whileT (\<lambda>s. s>0) c (S::nat)) \<ge> Some 0"
  apply(rule T_conseq4)
   apply(rule whileT_rule''[where I="\<lambda>s. if s\<le>n then Some (enat (n - s)) else None"
            and R="measure nat"])
      apply simp
  subgoal unfolding c apply (simp add: T_REST mm2_def) apply (auto split: if_splits)
     apply (simp add: one_eSuc zero_enat_def) 
    by (simp add: one_enat_def)
    using n apply simp 
  subgoal  by blast
  by (auto split: if_splits)

term emb'
lemma 
  assumes c: "c = (\<lambda>s. SPECT [s-1\<mapsto>1])" 
      and n: "S\<le>n"
  shows "T (\<lambda>s. if s = 0 then Some (enat n) else None) (whileT (\<lambda>s. s>0) c (S::nat)) \<ge> Some 0"
  apply(rule T_conseq4)
   apply(rule whileT_rule[where I="\<lambda>s. if s\<le>n then Some (enat (n - s)) else None"])
      apply simp
  subgoal unfolding c apply (simp add: T_REST mm2_def) apply (auto split: if_splits)
     apply (simp add: one_eSuc zero_enat_def) 
    by (simp add: one_enat_def)
    using n apply simp 
  subgoal using c apply auto 
    apply(rule wf_bounded_measure[where ub="\<lambda>_. n" and f="\<lambda>s. n - s"])
    by auto 
  by (auto split: if_splits)

lemma                                       (* hmmm *)
  assumes c: "c = (\<lambda>s. SPECT (\<lambda>s'. if s'<s \<and> even s then Some C else None))"  
  shows "T (\<lambda>s. if s = 0 then Some \<infinity> else None) (whileT (\<lambda>s. s>0) c (S::nat)) \<ge> Some 0"
  apply(rule T_conseq4)
   apply(rule whileT_rule[where I="\<lambda>s. Some \<infinity>"])
      apply simp
  subgoal for s unfolding c by (simp add: T_pw mii_alt mm2_def)
    apply simp 
  subgoal using c apply auto  
    by (smt case_prodI le_less_linear mem_Collect_eq nz_le_conv_less prod.sel(2) wf wf_def)
  by (auto split: if_splits)


lemma T_specifies_I: "T Q m \<ge> Some 0 \<Longrightarrow> (m \<le> SPECT Q)"
  unfolding T_pw apply (cases m) apply (auto simp: miiFailt le_fun_def mii_alt mm2_def split: option.splits)
  subgoal for M x apply(cases "Q x"; cases "M x") apply (auto split: if_splits)
    apply force+ done
  done

lemma T_specifies_rev: "(m \<le> SPECT Q) \<Longrightarrow> T Q m \<ge> Some 0" 
  unfolding T_pw apply (cases m)
  subgoal by auto
   apply (auto simp: miiFailt le_fun_def mii_alt mm2_def split: option.splits)
  subgoal for M x t apply(cases "Q x"; cases "M x") apply (auto split: if_splits)
    by (metis less_eq_option_Some_None)
  subgoal by (metis leD less_option_Some) 
  done

lemma T_specifies: "T Q m \<ge> Some 0 = (m \<le> SPECT Q)"
  using T_specifies_I T_specifies_rev by metis

thm whileT_rule''
lemma                                       (* hmmm *)
  assumes c[vcg_rules]: "\<And>s. c s \<le> SPECT (\<lambda>s'. if s'<s \<and> even s then Some C else None)"  
  shows "T (\<lambda>s. if s \<le> 0 then Some \<infinity> else None) (whileT (\<lambda>s. s>0) c (S::nat)) \<ge> Some 0"
  apply(rule  whileT_rule''[where I="\<lambda>s. Some \<infinity>" and R="{(x, y). x < y}", THEN T_conseq4])
      apply simp 
     apply(rule T_conseq4)
      apply(rule T_specifies_rev[OF c])  
     apply (auto split: if_splits)[1]
  apply simp apply(fact wf) by (auto split: if_splits)  


definition whileTI :: "('a \<Rightarrow> enat option) \<Rightarrow> ( ('a\<times>'a) set) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a nrest) \<Rightarrow> 'a \<Rightarrow> 'a nrest" where
  "whileTI I R b c s = whileT b c s"

print_statement whileT_rule''

lemma  whileTI_rule[vcg_rules]:
  assumes 
      "\<And>s t'. I s = Some t' \<Longrightarrow> b s \<Longrightarrow> Some t' \<le> T (\<lambda>s'. if (s', s) \<in> R then I s' else None) (c s)"
    and "I s = Some t'"
    and "wf R"
  shows "Some t' \<le> T (\<lambda>x. if b x then None else I x) (whileTI I R b c s)"
  unfolding   whileTI_def
  apply(rule whileT_rule''[where I=I and R=R])
  apply simp apply fact+ done
 
thm vcg_rules
lemma                                       (* hmmm *)
  assumes c[vcg_rules]: "\<And>s. Some 0 \<le> T (\<lambda>s'. if s' < s \<and> even s then Some C else None) (c s)"  
  shows "T (\<lambda>s. if s \<le> 0 then Some \<infinity> else None) (whileTI (\<lambda>s. Some \<infinity>) {(x, y). x < y} (\<lambda>s. s>0) c (S::nat)) \<ge> Some 0"
  apply vcg  
     apply (auto split: if_splits)   by(fact wf) 



lemma   fixes n :: nat
  assumes [vcg_rules]: "T (\<lambda>s. if s \<le> n then Some 1 else None) f \<ge> Some 0"
   and  c[vcg_rules]: "\<And>s. Some 0 \<le> T (\<lambda>s'. if s' < s then Some (enat C) else None) (c s)"
   and C: "C>0"
  shows "T (\<lambda>s. if s \<le> 0 then Some (1+C*n) else None) (
        do { n \<leftarrow> f;
             whileT (\<lambda>s. s>0) c n }) \<ge> Some 0"
    (* note that n is bound from the outside ! *)
  apply(subst whileTI_def[symmetric, where I="(\<lambda>s. if s\<le>n then Some (1+C*(enat (n-s))) else None)"
                                    and R="  {(x, y). x < y}"])
  apply vcg 
  apply(auto simp: wf one_enat_def split: if_splits) 
  proof -
    fix x s xa   
    assume "x \<le> n " " s \<le> n " " xa < s"
    then have i: "((n - s) + 1) \<le> (n - xa)" by linarith  
    have "C * (n - s) + C = C * ((n - s) + 1)" by simp
    also have "\<dots> \<le> C * (n - xa)"  apply(rule mult_left_mono) apply fact by simp
    finally  
    show "C * (n - s) + C \<le> C * (n - xa)" .
  qed 


lemma   fixes n :: nat
  assumes [vcg_rules]: "T (\<lambda>s. if s \<le> n then Some 1 else None) f \<ge> Some 0"
   and  c[vcg_rules]: "\<And>s. Some 0 \<le> T (\<lambda>s'. if s' < s then Some (enat C) else None) (c s)"
   and C: "C>0"
  shows "T (\<lambda>s. if s \<le> 0 then Some (1+C*n) else None) (
        do { n \<leftarrow> f;
             whileTI (\<lambda>s. if s\<le>n then Some (1+C*(enat (n-s))) else None)  {(x, y). x < y}  (\<lambda>s. s>0) c n }) \<ge> Some 0" 
    (* note that n in the Invariant is bound from the inside, very much in contrast to the example above! ! *)
  apply vcg 
  apply(auto simp: wf one_enat_def split: if_splits) 
  proof -
    fix x s xa   
    assume "x \<le> n " " s \<le> x " " xa < s"
    then have i: "((x - s) + 1) \<le> (x - xa)" by linarith  
    have "C * (x - s) + C = C * ((x - s) + 1)" by simp
    also have "\<dots> \<le> C * (x - xa)"  apply(rule mult_left_mono) apply fact by simp
    finally  
    show "C * (x - s) + C \<le> C * (x - xa)" .
  qed
  


lemma dont_care_about_runtime_as_long_as_it_terminates: 
    (* here:
        * the cost C of of the loop body (decrementing s) may even be \<infinity>
        * the starting state S is also arbitrary *)
  assumes c: "c = (\<lambda>s. SPECT [s-1\<mapsto>C])"
  shows "T (\<lambda>s. if s = 0 then Some \<infinity> else None) (whileT (\<lambda>s. s>0) c (S::nat)) \<ge> Some 0"
  apply(rule T_conseq4)
   apply(rule whileT_rule[where I="\<lambda>s. Some \<infinity>"])
      apply simp
  subgoal for s unfolding c by (simp add: T_REST mm2_def)  
    apply simp 
  subgoal using c apply auto  
    by (smt case_prodI le_less_linear mem_Collect_eq nz_le_conv_less prod.sel(2) wf wf_def) 
  by (auto split: if_splits)


lemma "RETURNT r \<le> SPECT [f\<mapsto>i] \<longleftrightarrow> (r \<longleftrightarrow> f)"
  unfolding RETURNT_def apply simp unfolding le_fun_def by simp

lemma "SPECT  [r\<mapsto>i] \<le> SPECT [f\<mapsto>j] \<longleftrightarrow> ((r \<longleftrightarrow> f) \<and> i\<le>j)"
   apply simp unfolding le_fun_def by simp


abbreviation "TTT == T"
 

 

  definition le_or_fail :: "'a nrest \<Rightarrow> 'a nrest \<Rightarrow> bool" (infix "\<le>\<^sub>n" 50) where
    "m \<le>\<^sub>n m' \<equiv> nofailT m \<longrightarrow> m \<le> m'"


  subsection "weakest precondition & strongest postcondition"


definition "wp Q c = (\<lambda>s. T Q (c s))"


lemma "FAILT \<le> SPECT Q" apply simp oops

lemma "(\<forall>s. P s \<longrightarrow> (c s) \<le> SPECT Q) \<longleftrightarrow> emb P 0 \<le> wp Q c"
  apply rule
  subgoal unfolding emb'_def wp_def le_fun_def by (auto simp: T_specifies)
  subgoal unfolding emb'_def wp_def le_fun_def apply (auto simp: T_specifies[symmetric]) by metis
  done

  thm T_def

definition "spl P c s s' = None"

fun Someplus where "Someplus None _ _ = Map.empty" |
  "Someplus _ None _ = Map.empty" |
  "Someplus (Some a) (Some b) s = [s\<mapsto>(a+b)]"



thm Sup_option_def


definition "sp P c = Sup {
                          Sup { case P s of None \<Rightarrow> SPECT Map.empty |
                                      Some t \<Rightarrow> (case c s of FAILi \<Rightarrow> FAILi |
                                                    SPECT M \<Rightarrow> SPECT (Someplus (M s') (P s) s') ) 
                             |s. True}| s'. True }"

lemma spI: "(\<And>s' s.
       (case P s of None \<Rightarrow> SPECT Map.empty
        | Some t \<Rightarrow> case c s of FAILi \<Rightarrow> FAILi | REST M \<Rightarrow> SPECT (Someplus (M s') (P s) s'))
       \<le> SPECT Q) \<Longrightarrow> sp P c \<le> SPECT Q"
    apply (auto simp: sp_def)
    apply(rule Sup_least) apply auto
    apply(rule Sup_least) by (auto)

lemma spD: assumes s: "sp P c \<le> SPECT Q"
  shows "(case P s of None \<Rightarrow> SPECT Map.empty
                         | Some t \<Rightarrow>
                             case c s of FAILi \<Rightarrow> FAILi
                             | REST M \<Rightarrow> SPECT (Someplus (M s') (P s) s')) \<le> SPECT Q"
proof -  
   from s have a': "\<And>s'.  
        Sup {uu. \<exists>s. uu =
                       (case P s of None \<Rightarrow> SPECT Map.empty
                        | Some t \<Rightarrow>
                            case c s of FAILi \<Rightarrow> FAILi
                            | REST M \<Rightarrow> SPECT (Someplus (M s') (P s) s'))} \<le> SPECT Q"
    unfolding sp_def apply(subst (asm) Sup_le_iff)
    by (auto simp:  ) 
  show ?thesis
    using a'[unfolded Sup_le_iff]
    by auto   
qed


lemma assumes a: "(\<And>s. P s \<Longrightarrow> (c s) \<le> SPECT Q)"
  shows sp_refines1: "sp (emb P 0) c \<le> SPECT Q" 
  apply(rule spI) 
    apply (auto simp: emb'_def le_fun_def )
    subgoal for s' s using a[of s] apply (auto simp: le_fun_def emb'_def split: nrest.splits)
      subgoal for x2 x apply(cases "x2 s'") apply auto by metis
      done
    done

lemma assumes a: "sp (emb P 0) c \<le> SPECT Q" and P: "P s"
  shows sp_refines2: "(c s) \<le> SPECT Q" 
proof -    
  show ?thesis
    using spD[OF a, where s=s] P    apply (auto simp: emb'_def)
    apply(cases "c s") apply (auto simp add: emb'_def le_fun_def)
  proof (goal_cases)
    case (1 x2 x)
    from 1(1)[of x]
      show ?case apply(cases "x2 x") by (auto split: if_splits)  
    qed
  qed 

lemma sp_refines: "(\<forall>s. P s \<longrightarrow> (c s) \<le> SPECT Q) \<longleftrightarrow>  sp (emb P 0) c \<le> SPECT Q" 
  by(auto intro: sp_refines1 sp_refines2) 

lemma wpI: "(\<And>s s'. P s \<le> mii Q (c s) s' ) \<Longrightarrow> P \<le> wp Q c"
  unfolding wp_def T_def apply(auto simp add: le_fun_def)
  apply(rule Inf_greatest) by auto

lemma f: "a + b \<le> a' \<Longrightarrow> \<not> a' < a \<Longrightarrow> b \<le> a' - (a::enat)"
  apply(cases a; cases b; cases a') by auto

lemma g: "\<not> a < a' \<Longrightarrow> b \<le> a - a' \<Longrightarrow> a' + b \<le> (a::enat)"
  apply(cases a; cases b; cases a') by auto

lemma [simp]: "Someplus t None s' = Map.empty" 
  by (cases t; simp) 

lemma Someplus_mii_conv: "Someplus (M s) t s \<le> Q \<longleftrightarrow> t \<le> mii Q (SPECT M) s"
  apply(cases t) 
    apply(auto simp:   mii_alt mm2_def le_fun_def split: if_splits option.splits )
    subgoal using dual_order.strict_trans2 by fastforce 
    subgoal by(simp add: f)
    subgoal by(simp add: g)
    done

lemma wpD: assumes "P \<le> wp Q c" 
  shows "(\<And>s s'. P s \<le> mii Q (c s) s' )"
  using assms unfolding wp_def T_def by(auto simp add: le_fun_def le_Inf_iff) 
 

lemma sp_wp: "(sp P c \<le> SPECT Q) \<longleftrightarrow> P \<le> wp Q c"
  apply(rule)
  subgoal  apply(rule wpI) subgoal for s s' apply(drule spD[where s=s and s'=s'])
    by(auto simp: Someplus_mii_conv split: option.splits nrest.splits)
  done
  subgoal  apply(rule spI) subgoal for s' s  apply(drule wpD[where s=s and s'=s'])
    apply(auto simp: Someplus_mii_conv split: option.splits nrest.splits)
    by(auto simp: miiFailt  le_fun_def less_eq_option_None_is_None) 
  done
  done

thm T_bindT
term "bindT m c"
term wp

lemma "wp Q (%_. bindT m c) = wp (wp Q c) (\<lambda>_. m)"
  unfolding wp_def T_bindT by simp

thm T_RETURNT

lemma "wp Q RETURNT = Q"
  unfolding wp_def T_RETURNT by simp

lemma "wp Q (\<lambda>_. RETURNT x) = (\<lambda>_. Q x)"
  unfolding wp_def T_RETURNT by simp

lemma "wp Q (\<lambda>s. SPECT (f s))  = foo"
  unfolding wp_def unfolding T_def mii_alt apply(rule)
    apply (simp add:  ) oops
    


text \<open>I think strongest postcondition does not make any sense here,
because the nondeterminism monad does not have a state on which predicates might work.
so there is no real precondition,.
only a post condition: a condition on the result of the computation,
for this one can compute a weakest precondition, meaning, what has to hold
in order to imply that the computation establishes a specified result\<close>

definition "spp PP c = (case PP of FAILi \<Rightarrow> FAILi |
                                SPECT P \<Rightarrow>
                          Sup {
                          Sup {  (case P s of None \<Rightarrow> SPECT Map.empty |
                                      Some t \<Rightarrow> (case c s of FAILi \<Rightarrow> FAILi |
                                                    SPECT M \<Rightarrow> SPECT (Someplus (M s') (P s) s')) ) 
                             |s. True}| s'. True })"

lemma l: "spp (SPECT P) c = sp P c" unfolding spp_def sp_def by simp 

thm sp_refines[no_vars]
lemma "(\<forall>s. P s \<longrightarrow> c s \<le> SPECT Q) = (spp (SPECT (emb P 0)) c \<le> SPECT Q)"
  unfolding l by (rule sp_refines)

lemma spp_wp: "(spp (SPECT P) c \<le> SPECT Q) \<longleftrightarrow> P \<le> wp Q c"
  unfolding l by (rule sp_wp)

lemma [simp]: "SPECT Map.empty \<le> a" apply(cases a) apply auto subgoal for x2 by(auto simp: le_fun_def)
  done

lemma kla: "(FAILT \<in> X) \<Longrightarrow> Sup X = FAILT " by (simp add: nrest_Sup_FAILT)


(*
lemma "spp (SPECT (emb P 0)) (\<lambda>s. RETURNT (f s)) = foo"
  unfolding spp_def apply (auto simp: emb'_def RETURNT_def)
  unfolding Sup_nrest_def apply auto 
  apply(rule ext)apply auto
  unfolding Sup_fun_def
   defer unfolding SUP_eq_None_iff apply auto oops *)


lemma "spp P (%_. bindT m c) = spp (spp P (\<lambda>_. m)) c"
  apply (rule antisym)
  subgoal  unfolding spp_def 
    apply(cases P) apply simp
    apply simp unfolding Sup_le_iff apply auto unfolding Sup_le_iff
    apply auto apply(auto split: option.splits)
    apply(cases m) apply simp
     apply(subst (3) kla) apply auto
    oops



hide_const T
 
end