theory Flatten_Currencies
  imports 
    AbstractSepreftime
    "SeprefTime.Sepref" 
begin


section \<open>Misc\<close>

lemma Sup_absorb_bot: "y = {\<bottom>} \<or> y = {} \<Longrightarrow> Sup (X \<union> y) = Sup (X::('a::complete_lattice) set)"
  by auto

lemma Sup_absorb_bot_fun: "Sup { f x t |x t. X x = Some t}
             = Sup ( (\<lambda>x. case X x of None \<Rightarrow> (\<bottom>::('a::complete_lattice)) 
                                      | Some t \<Rightarrow> f x t) ` UNIV)" (is "Sup ?L = Sup ?R")
proof -
  have *: "?R = { f x t |x t. X x = Some t} \<union> { \<bottom> |x. X x = None}"
    apply rule 
    subgoal by (auto split: option.splits)
    subgoal apply (auto split: option.splits)
      subgoal
        by (metis (mono_tags) option.simps(5) rangeI) 
      subgoal
        by (metis (mono_tags) UNIV_I image_eqI option.case(1)) 
      done
    done
  have **: " { SPECT (\<lambda>_. None) |x. X x = None} =  {\<bottom>} \<or> { SPECT (\<lambda>_. None) |x. X x = None} =  {}  "
    by (auto simp: bot_nrest_def)
  show ?thesis
    apply(simp only: *)
    apply(subst Sup_absorb_bot) 
    using ** by auto
qed  



section \<open>Abbreviations for the abstract NREST\<close>

abbreviation "aSPECT == AbstractSepreftime.SPECT"
abbreviation "aFAILT == AbstractSepreftime.FAILT"
abbreviation "aASSERT == AbstractSepreftime.ASSERT"
abbreviation "aRETURNT == AbstractSepreftime.RETURNT"
abbreviation "aemb' == AbstractSepreftime.emb'"

section \<open>Continuity between NREST and abstract NREST\<close>


lemma "mono f \<Longrightarrow> mono (AbstractSepreftime.case_nrest FAILT (\<lambda>m. SPECT (f m) ))" 
  by (auto simp: mono_def split: AbstractSepreftime.nrest.split) 

thm continuous_nrest
thm continuous_option


lemma continuous_anrest_nrest: (* or generally, adding a top element *)
  assumes *: "continuous f"
  shows "continuous (AbstractSepreftime.case_nrest FAILi (REST o f))"
  apply(rule continuousI)
  unfolding AbstractSepreftime.Sup_nrest_def Sup_nrest_def
  apply (auto split: AbstractSepreftime.nrest.splits nrest.splits)
  apply(subst continuousD[OF *])
  apply(rule arg_cong[where f=Sup]) 
  apply  (auto split: AbstractSepreftime.nrest.splits nrest.splits)    
  using image_iff by fastforce   

lemma continuous_anrest_nrest': (* or generally, adding a top element *)
  assumes *: "continuous f"
  shows "continuous (AbstractSepreftime.case_nrest FAILi (\<lambda>x. REST (f x)))"
  using continuous_anrest_nrest[OF assms] by(simp add: o_def) 


section \<open>flatten Currencies\<close>

definition flatCurrs :: "('a,unit \<Rightarrow> enat) AbstractSepreftime.nrest \<Rightarrow> 'a nrest" where
  "flatCurrs M = (case M of AbstractSepreftime.FAILi \<Rightarrow> FAILi
                        | aSPECT m \<Rightarrow> SPECT (\<lambda>x. case m x of None \<Rightarrow> None 
                                                        | Some f \<Rightarrow> Some (f ()) ))" 

subsection \<open>gg: From (unit \<Rightarrow> 'a) option to 'a option\<close>

definition gg :: "('a \<Rightarrow> (unit \<Rightarrow> 'b::{complete_lattice}) option) \<Rightarrow> 'a \<Rightarrow> 'b option"
  where "gg m = (\<lambda>x. case m x of None \<Rightarrow> None | Some f \<Rightarrow> Some (f ()) )"

lemma flatCurrs_gg: "flatCurrs M = AbstractSepreftime.case_nrest FAILT (\<lambda>m. SPECT (gg m) ) M"
  unfolding gg_def flatCurrs_def by (auto split: AbstractSepreftime.nrest.splits)

lemma continuous_gg: "continuous gg"
  unfolding gg_def
  apply(rule AbstractSepreftime.continuousI)
  apply auto apply(rule ext)
  unfolding Sup_fun_def  
  apply(subst continuousD[OF continuous_option, unfolded o_def])
   apply(rule continuous_app) 
  by(simp only: image_image)
   
  
subsection \<open>Properties of flatCurrs\<close>

subsubsection \<open>continuous flatCurrs\<close>

lemma flatCurrs_Sup': "flatCurrs (Sup X) = Sup (flatCurrs ` X)"
  unfolding flatCurrs_gg  top_nrest_def 
  apply(rule continuousD[OF continuous_anrest_nrest', of gg])
  by(rule continuous_gg) 

lemma flatCurrs_Sup: "continuous flatCurrs"
  apply(rule continuousI)
  by(rule flatCurrs_Sup')
 

lemma case_flatCurrs: 
    "m = aSPECT x2 \<Longrightarrow> (case flatCurrs m of NREST.nrest.FAILi \<Rightarrow> x
           | NREST.nrest.REST X \<Rightarrow> f X) = f (\<lambda>x. case x2 x of None \<Rightarrow> None | Some f \<Rightarrow> Some (f ()))"
  unfolding flatCurrs_def by auto

lemma case_flatCurrs_alt: 
    "m = aSPECT x2 \<Longrightarrow> (case flatCurrs m of NREST.nrest.FAILi \<Rightarrow> x
           | NREST.nrest.REST X \<Rightarrow> f X) = f (gg x2)"
  unfolding flatCurrs_def gg_def by auto


definition "pff f X == { consume (f x) t1 |x t1. X x = Some t1}"

lemma  bindT_1: "bindT M f = case_nrest FAILT (\<lambda>X. Sup (pff f X) ) M"
  unfolding bindT_alt pff_def by simp

lemma FAIL_in_pff: "FAILT \<in> pff f M
                 \<longleftrightarrow> (\<exists>x t. M x = Some t \<and> f x = FAILT )"
  unfolding pff_def consume_def by (auto split: nrest.splits)

lemma Sup_pff: "Sup (pff f X) = Sup ( (\<lambda>x. case X x of None \<Rightarrow> SPECT (\<lambda>_. None) 
                                      | Some t \<Rightarrow> consume (f x) t) ` UNIV)"
  unfolding pff_def Sup_absorb_bot_fun bot_nrest_def by simp 




definition "grr f X =  (\<lambda>x. case X x of None \<Rightarrow> \<bottom> | Some t \<Rightarrow> f x t)"

lemma EE: "Sup (pff f X) = Sup ( (grr (\<lambda>x t. consume (f x) t)  X) ` UNIV)"
  unfolding Sup_pff grr_def bot_nrest_def by simp


lemma "bindT m f = case_nrest FAILT (\<lambda>X. Sup ( (grr (\<lambda>x t. consume (f x) t)  X) ` UNIV) ) m"
  unfolding EE bindT_1 by simp

  
definition "apff f X == { AbstractSepreftime.consume (f x) t1 |x t1. X x = Some t1}"

lemma abindT_1: "AbstractSepreftime.bindT M f = AbstractSepreftime.case_nrest AbstractSepreftime.FAILT (\<lambda>X. Sup (apff f X) ) M"
  unfolding AbstractSepreftime.bindT_alt apff_def by simp

lemma FAIL_in_apff: "AbstractSepreftime.FAILT \<in> apff f M
                 \<longleftrightarrow> (\<exists>x t. M x = Some t \<and> f x = AbstractSepreftime.FAILT )"
  unfolding apff_def AbstractSepreftime.consume_def  by (auto split: AbstractSepreftime.nrest.splits)


lemma Sup_apff: "Sup (apff f X) = Sup ( (\<lambda>x. case X x of None \<Rightarrow> aSPECT (\<lambda>_. None) 
                                      | Some t \<Rightarrow> AbstractSepreftime.consume (f x) t) ` UNIV)"
  unfolding apff_def Sup_absorb_bot_fun AbstractSepreftime.bot_nrest_def by simp 

lemma gg_some: "x2 x = Some t' \<Longrightarrow> (gg x2 x = Some t) \<longleftrightarrow> t = t' ()"
  unfolding gg_def by(auto split: option.splits)

lemma pff_gg: "pff X (gg x) = {NREST.consume (X xa) (t1 ()) |xa t1. x xa  = Some t1}"
  unfolding pff_def gg_def by (auto split: option.splits) 


subsubsection \<open>FlatCurrs of combinators\<close>

lemma flatCurrs_SPECT_emb': "flatCurrs (aSPECT (aemb' P f)) = SPECT (emb' P (f ()))"
  by(auto simp: flatCurrs_def AbstractSepreftime.emb'_def emb'_def)

lemma flatCurrs_SPECT: "flatCurrs (aSPECT [x \<mapsto> t]) = SPECT [x \<mapsto> t ()]"
  by(auto simp: flatCurrs_def)

lemma flatCurrs_RETURNT: "flatCurrs (aRETURNT x) = RETURNT x"
  by(auto simp: flatCurrs_def AbstractSepreftime.RETURNT_def)

lemma flatCurrs_RETURNT_le: "flatCurrs (aRETURNT x) \<le> RETURNT x"
  by (auto intro: le_funI simp: flatCurrs_def AbstractSepreftime.RETURNT_def RETURNT_def) 

lemma flatCurrs_RETURNT_ge: "flatCurrs (aRETURNT x) \<ge> RETURNT x"
  by (auto intro: le_funI simp: flatCurrs_def AbstractSepreftime.RETURNT_def RETURNT_def) 

lemma flatCurrs_FAILT_conv: "flatCurrs x = NREST.FAILT \<longleftrightarrow> (x=aFAILT)"
  unfolding flatCurrs_def by (auto split: AbstractSepreftime.nrest.splits)

lemma flatCurrs_FAILT: "flatCurrs AbstractSepreftime.FAILT = NREST.FAILT"
  unfolding flatCurrs_def by simp

lemma flatCurrs_FAILTn: "flatCurrs (AbstractSepreftime.SPECT m) \<noteq> NREST.FAILT"
  unfolding flatCurrs_def by simp

lemma flatCurrs_consume: "flatCurrs (AbstractSepreftime.consume x t) = consume (flatCurrs x) (t ())"
  unfolding flatCurrs_def AbstractSepreftime.consume_def
        consume_def by (auto split: AbstractSepreftime.nrest.splits option.splits)  

lemma flatCurrs_If:
  "(b  \<Longrightarrow> flatCurrs (c1) = c1') \<Longrightarrow> (\<not>b  \<Longrightarrow> flatCurrs (c2) = c2') \<Longrightarrow> flatCurrs (If b c1 c2) = If b c1' c2'"
  by simp  

lemma flatCurrs_If_le:
  "(b  \<Longrightarrow> flatCurrs (c1) \<le> c1') \<Longrightarrow> (\<not>b  \<Longrightarrow> flatCurrs (c2) \<le> c2') \<Longrightarrow> flatCurrs (If b c1 c2) \<le> If b c1' c2'"
  by simp  

lemma flatCurrs_If_ge:
  "(b  \<Longrightarrow> flatCurrs (c1) \<ge> c1') \<Longrightarrow> (\<not>b  \<Longrightarrow> flatCurrs (c2) \<ge> c2') \<Longrightarrow> flatCurrs (If b c1 c2) \<ge> If b c1' c2'"
  by simp 


subsubsection \<open>flatCurrs with bind\<close>

theorem flatCurrs_bindT: "flatCurrs (m \<bind> f) = (flatCurrs m) \<bind> (\<lambda>x. flatCurrs (f x))" 
  unfolding abindT_1 bindT_1
  apply(cases m)
  subgoal
    by (simp add: flatCurrs_FAILT) 
  subgoal apply(simp only: case_flatCurrs_alt)
    apply(auto simp: flatCurrs_FAILTn)
    apply(simp only: flatCurrs_Sup')
    apply(rule arg_cong[where f=Sup])
    unfolding apff_def pff_gg setcompr_eq_image[symmetric]
    using flatCurrs_consume Collect_cong
    by smt
  done


lemma flatCurrs_mono: "m \<le> m' \<Longrightarrow> flatCurrs m \<le> flatCurrs m'"
  unfolding flatCurrs_def apply(cases m; cases m') apply (auto intro!: le_funI split: option.splits)
  subgoal  
    by (metis le_fun_def le_some_optE)  
  subgoal  
    by (metis le_funD less_eq_option_Some)  
  done

lemma flatCurrs_bindTI: 
  "flatCurrs m = m' \<Longrightarrow> (\<And>x. flatCurrs (f x) = f' x) \<Longrightarrow> flatCurrs (m \<bind> f) = (m' \<bind> f')"
  unfolding flatCurrs_bindT by simp  

lemma flatCurrs_bindT_le: 
  "flatCurrs m \<le> m' \<Longrightarrow> (\<And>x. flatCurrs (f x) \<le> f' x) \<Longrightarrow> flatCurrs (m \<bind> f) \<le> (m' \<bind> f')"
  unfolding flatCurrs_bindT apply(subst bindT_mono) by simp_all  

lemma flatCurrs_bindT_ge: 
  "flatCurrs m \<ge> m' \<Longrightarrow> (\<And>x. flatCurrs (f x) \<ge> f' x) \<Longrightarrow> flatCurrs (m \<bind> f) \<ge> (m' \<bind> f')"
  unfolding flatCurrs_bindT apply(subst bindT_mono) by simp_all  

lemma flatCurrs_prod:
  "(\<And>a b. flatCurrs (c a b) = c' a b) \<Longrightarrow> flatCurrs (case_prod c x) = case_prod c' x"   
  by (simp add: case_prod_beta)


subsubsection \<open>flatCurrs with ASSERT\<close>


lemma flatCurrs_ASSERT: 
  "flatCurrs (aASSERT \<Phi>) = ASSERT \<Phi>"
  unfolding flatCurrs_def AbstractSepreftime.ASSERT_def AbstractSepreftime.iASSERT_def ASSERT_def
  by (auto simp: AbstractSepreftime.RETURNT_def iASSERT_def)


subsubsection \<open>flatCurrs with whileT\<close>

lemma flatCurrs_whileT:
  assumes "AbstractSepreftime.mono2 (\<lambda>whileT s. if b s then c s \<bind> whileT else aRETURNT s)"
    and  "mono2 (\<lambda>whileT s. if b s then c' s \<bind> whileT else RETURNT s)"
  shows 
    "(\<And>y. b y \<Longrightarrow> flatCurrs (c y) = (c' y) ) \<Longrightarrow> flatCurrs( AbstractSepreftime.whileT b c x) = whileT b c' x"
  unfolding whileT_def AbstractSepreftime.whileT_def AbstractSepreftime.RECT_flat_gfp_def RECT_flat_gfp_def
  apply(simp only: assms)
  apply (auto simp: flatCurrs_FAILT)
  subgoal    
    apply(rule antisym) 
    subgoal
      apply(rule flatf_gfp_transfer[where P="(=)"  ]) 
      subgoal by simp
      subgoal using assms unfolding AbstractSepreftime.mono2_def by simp
      subgoal using assms unfolding mono2_def by simp
      subgoal by simp
      subgoal 
        apply (simp only: )
        apply(rule flatCurrs_If_le)
         apply(rule flatCurrs_bindT_le) apply simp 
         apply simp
        by(rule flatCurrs_RETURNT_le)
      done
    subgoal 
      apply(rule flatf_gfp_transfer[where P="(=)"  ]) 
      subgoal unfolding flatCurrs_def by simp
      subgoal using assms unfolding mono2_def by simp
      subgoal using assms unfolding AbstractSepreftime.mono2_def by simp
      subgoal by simp
      subgoal 
        apply (simp only: )
        apply(rule flatCurrs_If_ge)
         apply(rule flatCurrs_bindT_ge) apply simp 
         apply simp
        by(rule flatCurrs_RETURNT_ge)
      done
    done
  done


end