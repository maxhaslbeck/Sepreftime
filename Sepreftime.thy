theory Sepreftime
  imports   Refine_Monadic.Refine_Misc  
  "HOL-Library.Monad_Syntax"  "HOL-Library.Extended_Nat"
begin



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


  
definition "nofailT S \<equiv> S\<noteq>FAILT"
definition inresT :: "'a nrest \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> bool" where 
  "inresT S x t \<equiv> (case S of FAILi \<Rightarrow> True | REST X \<Rightarrow> (\<exists>t'. X x = Some t' \<and>  enat t\<le>t'))"


lemma inresT_alt: "inresT S x t \<longleftrightarrow> REST ([x\<mapsto>enat t]) \<le> S"
  unfolding inresT_def apply(cases S)  
  by (auto dest!: le_funD[where x=x] simp: le_funI less_eq_option_def split: option.splits )


lemma inresT_mono: "inresT S x t \<Longrightarrow> t' \<le> t \<Longrightarrow> inresT S x t'"
  unfolding inresT_def apply(cases S) apply auto
  using enat_ord_simps(1) order_trans by blast
 
  

lemma [simp]: "inresT (RETURNT x) y t \<longleftrightarrow> t = 0 \<and> y = x"
  by(auto simp: inresT_def RETURNT_def enat_0_iff split: nrest.splits)

named_theorems refine_pw_simps


lemma nofailT_simps[simp]:
  "nofailT FAILT \<longleftrightarrow> False"
  "nofailT (REST X) \<longleftrightarrow> True"
  "nofailT (RETURNT x) \<longleftrightarrow> True"
  "nofailT SUCCEEDT \<longleftrightarrow> True"
  unfolding nofailT_def
  by (simp_all add: RETURNT_def)


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

lemma inresT_FAILT[simp]: "inresT FAILT r t"
  by(simp add: inresT_def)

lemma fail_inresT[refine_pw_simps]: "\<not> nofailT M \<Longrightarrow> inresT M x t"
unfolding nofailT_def by simp

declare nres_simp_internals(2)[simp]

lemma ll: 
  "Sup X = FAILT \<longleftrightarrow> FAILT \<in> X"
  "FAILT = Sup X \<longleftrightarrow> FAILT \<in> X"
  by (auto simp: nres_simp_internals Sup_nrest_def)
 



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
 

lemma pw_inresT_Sup[refine_pw_simps]: "inresT (Sup X) r t \<longleftrightarrow> (\<exists>M\<in>X. \<exists>t'\<ge>t.  inresT M r t')"
  apply(rule)
  subgoal (* \<rightarrow> *)
    apply(cases "Sup X")
    subgoal by (force simp: ll)
    subgoal 
      apply(auto simp: inresT_def  Sup_nrest_def split: if_splits)
      apply(auto simp: SUP_eq_Some_iff split: nrest.splits)  
      apply(subst (asm) Sup_enat_less)
       apply auto []  
      apply auto  by blast  
    done
  subgoal (* <- *)
    apply(cases "Sup X")
    subgoal by (auto simp: ll top_Sup)
    subgoal 
      apply(auto simp: inresT_def  Sup_nrest_def split: if_splits)
      apply(auto simp: SUP_eq_Some_iff split: nrest.splits)  
      apply(subst Sup_enat_less)
       apply auto []
      apply auto
      using dual_order.trans enat_ord_simps(1) by blast 
    done
  done

         
lemma [simp]:
  "inresT (REST X) x t \<longleftrightarrow> (\<exists>t'\<ge>t. X x = Some t')" 
  unfolding inresT_def 
  by (auto )


lemma [simp]: "(\<forall>x2. m \<noteq> REST x2) \<longleftrightarrow> m=FAILT"
  apply (cases m) apply auto done

 
 
lemma pw_Sup_nofail[refine_pw_simps]: "nofailT (Sup X) \<longleftrightarrow> (\<forall>x\<in>X. nofailT x)"
  apply (cases "Sup X")  
   apply auto unfolding Sup_nrest_def apply (auto split: if_splits)
  apply force unfolding nofailT_def apply(force simp add: nres_simp_internals)
  done


lemma   no_FAILTE:  
  assumes "g xa \<noteq> FAILT" 
  obtains X where "g xa = REST X" using assms by (cases "g xa") auto

thm refine_pw_simps

 

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

lemma pw_T_eqI: 
  assumes "nofailT S = nofailT S'" 
  assumes "\<And>x t. inresT S x t \<longleftrightarrow> inresT S' x t" 
  shows "S=S'"
  using assms by (simp add: pw_eq_iff)
  
 
(*
lemma infinite_chara: "\<infinity>\<notin>X \<Longrightarrow> infinite (X::enat set) = (\<forall>t. t \<noteq>\<infinity> \<longrightarrow> (\<exists>t'\<in>X. t\<le>t'))"
  apply auto
  subgoal for t apply(rule ccontr) apply (auto simp: not_le) 
    using finite_enat_bounded less_imp_le by blast  
     
  subgoal
    by (metis Collect_empty_eq Collect_mem_eq Max_ge Max_in eSuc_enat enat.exhaust iless_Suc_eq not_le) 
  done

lemma Sup_enat': "X \<noteq> {} \<Longrightarrow> (Sup X = (t::enat)) =
                       ((t \<in> X  \<and> (\<forall>t'. t' \<in> X\<longrightarrow> t'\<le>t ) )
                          \<or> (t=\<infinity> \<and> \<infinity>\<notin>X \<and> infinite X))"
  apply(cases "t\<in>X") 
  subgoal 
    unfolding Sup_enat_def apply auto
    using Max_eqI apply auto[1]
    by (metis finite_enat_bounded not_infinity_eq)
  subgoal
    unfolding Sup_enat_def apply auto
    using Max_in by blast  
  done

lemma Sup_enat:  "X \<noteq> {} \<Longrightarrow> (Sup X = (t::enat)) =
                       ((t \<in> X  \<and> (\<forall>t'. t' \<in> X\<longrightarrow> t'\<le>t ) )
                          \<or> (t=\<infinity>\<and> (\<forall>t. t \<noteq>\<infinity> \<longrightarrow> (\<exists>t'\<in>X. t\<le>t'))))"
  apply(cases "\<infinity>\<notin>X")
  subgoal using infinite_chara Sup_enat' by metis
  subgoal using Sup_upper by fastforce+ 
  done


lemma Sup_enat_option: "Sup X = Some (t::enat) \<longleftrightarrow> (Some t \<in> X \<and> (\<forall>t'. Some t' \<in> X\<longrightarrow> t'\<le>t ) )
                          \<or> (t=\<infinity> \<and> (\<forall>t'.  t' \<noteq>\<infinity> \<longrightarrow> (\<exists>t''. t''\<ge>t' \<and> Some t'' \<in>X)))"
  apply(cases "X = {} \<or> X = {None}")
  subgoal unfolding Sup_option_def by auto
  subgoal unfolding Sup_option_def apply simp
    apply(subst Sup_enat) subgoal unfolding Option.these_def by auto
    apply(simp add: in_these_eq Bex_def) by auto 
  done

lemma inresT_Sup[refine_pw_simps]: "inresT (Sup X) r t \<longleftrightarrow> 
  FAILT \<in> X 
  \<or> ((\<exists>M\<in>X. inresT M r t) \<and> (\<forall>t'.\<forall>M'\<in>X. (inresT M' r t' \<longrightarrow> t'\<le>t)) )
  \<or> (t=\<infinity> \<and> (\<forall>t'. t' \<noteq>\<infinity> \<longrightarrow>  (\<exists>M\<in>X. \<exists>t''\<ge>t'. inresT M r t'')) )"
  apply (rule)
  subgoal (* \<longrightarrow> *)
    apply (cases "Sup X")
    subgoal 
      unfolding Ball_def
      apply (simp add: nres_simp_internals)
      by (simp add: ll) 
    subgoal
      unfolding Sup_nrest_def
      apply (auto split: if_splits simp: l) 
        subgoal unfolding inresT_def apply (auto simp: Sup_enat_option nres_simp_internals split: nrest.splits)
            by fastforce
        subgoal unfolding inresT_def apply (auto simp: Sup_enat_option nres_simp_internals split: nrest.splits)
          by metis
        subgoal unfolding inresT_def apply (auto simp: Sup_enat_option nres_simp_internals split: nrest.splits) 
          apply blast by metis
        subgoal unfolding inresT_def apply (auto simp: Sup_enat_option nres_simp_internals split: nrest.splits)
          by metis
        done
    done
  subgoal (* <-- *)
    apply (cases "Sup X")
    subgoal 
      unfolding Ball_def
      by (simp add: nres_simp_internals) 
    subgoal
      unfolding Sup_nrest_def
      apply (auto split: if_splits simp: l)  
        subgoal unfolding inresT_def apply (auto simp: Sup_enat_option nres_simp_internals split: nrest.splits)
                    apply metis 
          apply force          by force 
        subgoal unfolding inresT_def apply (auto simp: Sup_enat_option nres_simp_internals split: nrest.splits)
          by (metis (full_types) nres_simp_internals(2) nrest.exhaust)
        done
    done
  done

lemma "(\<lambda>y. case m2 y of None \<Rightarrow> None | Some t2 \<Rightarrow> Some (t2 + (t1::enat))) = (map_option ((op +) t1) o (m2))"
  by (auto intro!: ext split: option.splits)
 *)


subsubsection {* Monad Operators *}


definition bindT :: "'b nrest \<Rightarrow> ('b \<Rightarrow> 'a nrest) \<Rightarrow> 'a nrest" where
  "bindT M f \<equiv> case M of 
  FAILi \<Rightarrow> FAILT |
  REST X \<Rightarrow> Sup { (case f x of FAILi \<Rightarrow> FAILT 
                | REST m2 \<Rightarrow> REST (map_option ((op +) t1) o (m2) ))
                    |x t1. X x = Some t1}"



lemma bindT_FAIL[simp]: "bindT FAILT g = FAILT"
  by (auto simp: bindT_def)



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
          apply(rule exI[where x="REST (map_option (op + t'a) \<circ> x2a)"]) 
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




lemma bindT_FAILT[simp]: "bindT FAILT f = FAILT"
  unfolding bindT_def by auto

lemma "bindT SUCCEEDT f = SUCCEEDT"
  unfolding bindT_def by(auto split: nrest.split simp add: bot_nrest_def) 

lemma [simp]: "(op + (0::enat)) = id" by auto

declare map_option.id[simp] 


(* Monad Rules *)

lemma nres_bind_left_identity[simp]: "bindT (RETURNT x) f = f x"
  unfolding bindT_def RETURNT_def 
  by(auto split: nrest.split ) 

lemma nres_bind_right_identity[simp]: "bindT M RETURNT = M" 
  by(auto intro!: pw_T_eqI simp: refine_pw_simps) 

lemma nres_bind_assoc[simp]: "bindT (bindT M (\<lambda>x. f x)) g = bindT M (%x. bindT (f x) g)"
  apply(auto intro!: pw_T_eqI simp:  refine_pw_simps)  
  using inresT_mono by fastforce+




lemma bindT_mono: 
  "m \<le> m' \<Longrightarrow> (\<And>x. (\<exists>t. inresT m x t) \<Longrightarrow> nofailT m' \<Longrightarrow>  f x \<le> f' x)
 \<Longrightarrow> bindT m f \<le> bindT  m' f'"
  apply(auto simp: pw_le_iff refine_pw_simps) 
   by fastforce+



definition "RECT B x = 
  (if (mono B) then (gfp B x) else (top::'a::complete_lattice))"


lemma RECT_unfold: "\<lbrakk>mono B\<rbrakk> \<Longrightarrow> RECT B = B (RECT B)"
  unfolding RECT_def [abs_def]
  by (simp add: gfp_unfold[ symmetric])


lemma RECT_mono[refine_mono]:
  assumes [simp]: "mono B'"
  assumes LE: "\<And>F x. (B' F x) \<le> (B F x) "
  shows " (RECT B' x) \<le> (RECT B x)"
  unfolding RECT_def
  apply clarsimp
  by (meson LE gfp_mono le_fun_def) 



term REST

(*
  flat_ge ?m ?m' \<Longrightarrow> (\<And>x. flat_ge (?f x) (?f' x)) \<Longrightarrow> flat_ge (?m \<bind> ?f) (?m' \<bind> ?f')
*)



 
end