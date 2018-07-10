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

         
lemma inresT_REST[simp]:
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


abbreviation SPECT where "SPECT \<equiv> REST"

term "SPECT Q"
term "(x::enat) - \<infinity>"

definition mm :: "( 'a \<Rightarrow> enat option) \<Rightarrow> ( 'a \<Rightarrow> enat option) \<Rightarrow> ( 'a \<Rightarrow> enat option)" where
  "mm R m = (\<lambda>x. (case m x of None \<Rightarrow> Some \<infinity>
                                | Some mt \<Rightarrow>
                                  (case R x of None \<Rightarrow> None | Some rt \<Rightarrow> (if rt < mt then None else Some (rt - mt)))))"

definition mm2 :: "(  enat option) \<Rightarrow> (   enat option) \<Rightarrow> (   enat option)" where
  "mm2 r m = (case m  of None \<Rightarrow> Some \<infinity>
                                | Some mt \<Rightarrow>
                                  (case r of None \<Rightarrow> None | Some rt \<Rightarrow> (if rt < mt then None else Some (rt - mt))))"


lemma mm_alt: "mm R m x = mm2 (R x) (m x)" unfolding mm_def mm2_def ..


lemma "\<infinity> -\<infinity> = (\<infinity>::enat)"  by simp



lemma "(a::enat) - b = \<infinity> \<Longrightarrow> a = \<infinity>"
  by (metis enat.distinct(2) enat_ord_simps(4) idiff_enat_enat idiff_infinity_right infinity_ne_i0 less_infinityE)
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

value "min None (Some t)"

term "REST (\<lambda>y. Inf { case f y of FAILi \<Rightarrow> None
                              | REST F \<Rightarrow> (mm (Q::'a \<Rightarrow> enat option) F) x |x. True})"
term "bindT m f \<le> SPECT Q"

lemma "REST Map.empty \<le> SPECT Q"
  by (auto simp: le_fun_def) 

lemma InfQ_E: "Inf Q = Some t \<Longrightarrow> None \<notin> Q"
  unfolding Inf_option_def by auto

lemma InfQ_iff: "(\<exists>t'\<ge>enat t. Inf Q = Some t') \<longleftrightarrow> None \<notin> Q \<and> Inf (Option.these Q) \<ge> t"
  unfolding Inf_option_def 
  by auto

 

definition mmm where "mmm f Q x y = (case f y of FAILi \<Rightarrow> None
                              | REST F \<Rightarrow> (mm (Q::'a \<Rightarrow> enat option) F) x)"

lemma None_mmm: "None \<notin> {mmm f Q x y |x. True} \<longleftrightarrow> (nofailT (f y) \<and> (\<forall>F x. f y = REST F \<longrightarrow> mm Q F x \<noteq> None))"
  unfolding mmm_def apply (auto simp: nofailT_def split: nrest.splits)
  apply (metis option.exhaust_sel)
  by (metis option.distinct(1))
    
lemma None_mmm': "(\<forall>xa. None \<noteq> mmm f Q xa y) \<longleftrightarrow> (nofailT (f y) \<and> (\<forall>F x. f y = REST F \<longrightarrow> mm Q F x \<noteq> None))"
  unfolding mmm_def apply (auto simp: nofailT_def split: nrest.splits)
  apply (metis option.exhaust_sel)
  by (metis option.distinct(1))
  
lemma mpaaD: "inresT m x t \<Longrightarrow> \<forall>x t. inresT m x t \<longrightarrow> Q x t \<Longrightarrow> Q x t"
  by auto


lemma fixes Q P  shows
    "Inf { P x \<le> Q x |x. True}  \<longleftrightarrow> P \<le> Q" unfolding le_fun_def by simp

  

definition mmmi where "mmmi Q f x  = (case f of FAILi \<Rightarrow> None
                              | REST F \<Rightarrow> (mm (Q::'a \<Rightarrow> enat option) F) x)"

definition mi :: "'a nrest \<Rightarrow> 'a nrest \<Rightarrow> 'a \<Rightarrow> enat option" where 
  "mi Q M x = (case Q of FAILi \<Rightarrow> Some \<infinity>
                       | REST Qf \<Rightarrow> (case M of FAILi \<Rightarrow> None 
                                             | REST Mf \<Rightarrow> (mm Qf Mf) x))"


definition T :: "'a nrest \<Rightarrow> 'a nrest \<Rightarrow> enat option" 
   where "T Q M = Inf { mi Q M x | x. True}"


definition mii :: "('a \<Rightarrow> enat option) \<Rightarrow> 'a nrest \<Rightarrow> 'a \<Rightarrow> enat option" where 
  "mii Qf M x =  (case M of FAILi \<Rightarrow> None 
                                             | REST Mf \<Rightarrow> (mm Qf Mf) x)"


lemma mii_alt: "mii Qf M x = (case M of FAILi \<Rightarrow> None 
                                             | REST Mf \<Rightarrow> (mm2 (Qf x) (Mf x)) )"
  unfolding mii_def mm_alt ..




thm mm_inf
lemma mii_inf: "mii Qf M x = Some \<infinity> \<longleftrightarrow> (\<exists>Mf. M = SPECT Mf \<and> (Mf x = None \<or> Qf x = Some \<infinity>))"
  by (auto simp: mii_def mm_inf split: nrest.split )

definition T' :: "('a \<Rightarrow> enat option) \<Rightarrow> 'a nrest \<Rightarrow> enat option" 
  where "T' Qf M =  Inf { mii Qf M x | x. True}"


thm Inf_top_conv 
lemma T'_char1: "T' Qf M = Some \<infinity> \<longleftrightarrow> (\<forall>x. mii Qf M x = Some \<infinity>)"
  unfolding T'_def top_enat_def[symmetric] top_option_def[symmetric]
  apply(simp only: Inf_top_conv(1)) by auto


lemma T'_char: "T' Qf M = Some \<infinity> \<longleftrightarrow> (\<exists>Mf. M = SPECT Mf \<and> (\<forall>x.(Mf x = None \<or> Qf x = Some \<infinity>)))"
  unfolding T'_char1 mii_inf
  by (metis (mono_tags, hide_lams) nrest_more_simps(4))  


lemma "X\<noteq>{} \<Longrightarrow> Sup (SPECT ` X) = SPECT (Sup X)" unfolding Sup_nrest_def apply auto oops

  term inresT
definition "inres2 S x \<equiv> (case S of FAILi \<Rightarrow> True | REST X \<Rightarrow> (\<exists>t'. X x = Some t'))"

lemma inres2_FAILT[simp]: "inres2 FAILT r" unfolding inres2_def by simp
lemma pw_inres2_Sup: "inres2 (Sup X) r \<longleftrightarrow> (\<exists>M\<in>X. inres2 M r)"
  apply(rule)
  subgoal (* \<rightarrow> *)
    apply(cases "Sup X")
    subgoal by (force simp: ll)
    subgoal 
      apply(auto simp: inres2_def  Sup_nrest_def split: if_splits)
      by(auto simp: SUP_eq_Some_iff split: nrest.splits)   
    done
  subgoal (* <- *)
    apply(cases "Sup X")
    subgoal by (auto simp: ll top_Sup)
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

lemma inres2_SPECT: "inres2 (SPECT Q) x = (\<exists>t'. Q x = Some t')" unfolding inres2_def by auto

lemma pw_bindT_nofailT_2[refine_pw_simps]: "nofailT (bindT M f) \<longleftrightarrow> (nofailT M \<and> (\<forall>x. inres2 M x \<longrightarrow> nofailT (f x)))"
  unfolding bindT_def   
   apply (auto elim: no_FAILTE simp: pw_Sup_nofail inres2_SPECT  split: nrest.splits )  
  by force+ 

lemma kla: "M = SPECT Mff \<Longrightarrow> inres2 M x = (Mff x \<noteq> None)" unfolding inres2_def by (auto split: nrest.splits)

lemma fixes Ff :: "'b \<Rightarrow> enat option"
  assumes "M = SPECT Mf" "Mf y \<noteq> None" "f y = SPECT Ff"
     "(bindT M f) = SPECT Mff "
  shows  result_implies_compoundresult: "Ff x \<noteq> None \<Longrightarrow> Mff x \<noteq> None"
proof -
  assume i: "Ff x \<noteq> None"
  have "inres2 (bindT M f) x"
    apply(auto simp: pw_inres2_bindT_aux)
    apply(rule exI[where x=y]) unfolding inres2_def using i assms by auto
  with assms(4) show "Mff x \<noteq> None" using kla by metis
qed

lemma assumes "M = SPECT Mf" "Mf y \<noteq> None" "f y = SPECT Ff"
     "(bindT M f) = SPECT Mff "   
   shows  no_compoundresult_implies_no_partialresult:
      "Mff x = None \<Longrightarrow> Ff x = None"
  using result_implies_compoundresult[OF assms] by blast

lemma T'_inf2: "T' Q (bindT M f) = Some \<infinity> \<Longrightarrow> T' (\<lambda>y. T' Q (f y)) M = Some \<infinity>"
proof -
  assume "T' Q (bindT M f) = Some \<infinity>"
  then have "(\<exists>Mf. (bindT M f) = SPECT Mf \<and> (\<forall>x. (Mf x = None \<or> Q x = Some \<infinity>)))"
    unfolding T'_char .
  then obtain Mff where Mff: "(bindT M f) = SPECT Mff" and pf: " (\<forall>x. (Mff x = None \<or> Q x = Some \<infinity>))" by blast
  from Mff obtain Mf where Mf: "M = SPECT Mf" by fastforce

  { fix y assume "Mf y\<noteq>None" 
    then obtain t where z: "Mf y = Some t" by blast
    have "\<exists>Ff. f y = SPECT Ff"
      by (metis (full_types) Mf Mff inresT_REST nofailT_simps(1) nofailT_simps(2) nrest.exhaust pw_bindT_nofailT z zero_enat_def zero_le)
    then obtain Ff where "f y = SPECT Ff" by blast
    { fix x   
      assume t: "Mff x = None"  
      thm no_compoundresult_implies_no_partialresult[of M Mf y f Ff Mff x]
      have "Ff x = None"  apply(rule no_compoundresult_implies_no_partialresult[of M Mf y f Ff Mff x]) apply fact+ done
    } note kl=this
    have "T' Q (f y) = Some \<infinity>"
      apply(subst T'_char)  apply(rule exI[where x=Ff])
      apply rule apply fact
      using pf kl by metis
  } note pl=this

  show "T' (\<lambda>y. T' Q (f y)) M = Some \<infinity>"
    apply(subst T'_char)  
    apply(rule exI[where x=Mf])
    apply rule apply fact  
      
    using   pl by metis
qed

lemma fixes  f :: "'a \<Rightarrow> 'b nrest"
  shows T'_inf1:  "T' (\<lambda>y. T' Q (f y)) M = Some \<infinity> \<Longrightarrow> T' Q (bindT M f) = Some \<infinity>"
proof - 
  assume "T' (\<lambda>y. T' Q (f y)) M = Some \<infinity>"
  then have "\<exists>Mf. M = SPECT Mf \<and> (\<forall>x. Mf x = None \<or> T' Q (f x) = Some \<infinity>)"
    apply(subst (asm) T'_char) .
  then obtain Mf where Mf: "M = SPECT Mf" and pf: "(\<And>x. Mf x = None \<or> T' Q (f x) = Some \<infinity>)" by blast
  then have pff: "(\<And>y. Mf y = None \<or> (\<exists>Mf. f y = SPECT Mf \<and> (\<forall>x. Mf x = None \<or> Q x = Some \<infinity>)))"
    unfolding T'_char by simp
  from Mf have nfM: "nofailT M" unfolding nofailT_def by auto
  thm pw_bindT_nofailT_2
  have "nofailT (bindT M f)" apply(simp only: pw_bindT_nofailT_2)
    apply(rule)
    subgoal using Mf unfolding nofailT_def by simp
  proof (safe)
    fix x assume "inres2 M x"
    with kla[OF Mf] pf[of x] have "T' Q (f x) = Some \<infinity>" by auto
    then show "nofailT (f x)"
      unfolding nofailT_def T'_def mii_def by auto
  qed
  then obtain Mff where bMf: "bindT M f = SPECT Mff" unfolding nofailT_def by force

  show "T' Q (bindT M f) = Some \<infinity>"
    unfolding T'_char apply(rule exI[where x=Mff]) apply rule apply fact
  proof  safe
    fix x assume Qx: "Q x \<noteq> Some \<infinity>"
    have "\<not> inres2 (bindT M f) x"
      apply(simp only: pw_inres2_bindT_aux) using nfM apply auto
    proof -
      fix y assume "nofailT M" and i: "inres2 M y" and i2: "inres2 (f y) x"
      from pff[of y] consider "Mf y = None" | "Mf y \<noteq> None" "(\<exists>Ff. f y = SPECT Ff \<and> (\<forall>x. Ff x = None \<or> Q x = Some \<infinity>))" by auto
      then show "False"
      proof cases
        case 1
        with kla[OF Mf, of y] i  show ?thesis by auto
      next
        case 2
        then obtain Ff :: "'b \<Rightarrow> enat option"  where f: "f y = SPECT Ff" and p: "(\<forall>x. Ff x = None \<or> Q x = Some \<infinity>) " by blast
        from p have "Ff x = None" using Qx by auto
        with f kla have "\<not> inres2 (f y) x" by force
        with i2 show ?thesis by safe
      qed 
    qed
    with kla[OF bMf, of x] show "Mff x = None" by auto
  qed
qed

lemma T'_inf: "T' (\<lambda>y. T' Q (f y)) M = Some \<infinity> \<longleftrightarrow> T' Q (bindT M f) = Some \<infinity>"
  using T'_inf1 T'_inf2 by metis





      
  

value "Some (1::enat) \<le> None"

term "(\<lambda>y. T Q (f y))"
term "\<infinity>" 



lemma "M = FAILi \<Longrightarrow> T' Q M = None" unfolding T'_def by (auto simp: mii_def)

lemma fall2: "M = REST Mf \<Longrightarrow> Mf x = Some t \<Longrightarrow> Q x = None \<Longrightarrow> T' Q M = None"
  unfolding T'_def
  apply(rule None_in_Inf)
  apply (auto simp: mii_def mm_def)
  apply(rule exI[where x=x]) by auto  

lemma fall3: "M = REST Mf \<Longrightarrow> Mf x = Some t \<Longrightarrow> Q x = Some t' \<Longrightarrow> t' < t \<Longrightarrow> T' Q M = None"
  unfolding T'_def
  apply(rule None_in_Inf)
  apply (auto simp: mii_def mm_def)
  apply(rule exI[where x=x]) by auto 

lemma "Inf ({}::enat option set) = Some \<infinity>" apply auto
  by (simp add: top_enat_def top_option_def) 

lemma k: "Inf S = None \<longleftrightarrow> (None \<in> S)"
  by (simp add: Inf_option_def) 
lemma k2: "None = Inf S \<longleftrightarrow> (None \<in> S)"
  by (simp add: Inf_option_def) 

lemma T'_None_char: "T' Q M = None \<longleftrightarrow> (M = FAILi \<or> (\<exists>Mf t x. M = REST Mf \<and> Mf x = Some t \<and> (Q x = None \<or> (\<exists>t'. Q x = Some t' \<and> t'<t))))"
  apply rule
  subgoal
    unfolding T'_def k
    apply auto
    apply(cases M) apply (auto simp: mii_def mm_def split: option.splits) by force
  subgoal
    unfolding T'_def
    apply(rule None_in_Inf) 
    apply (auto simp: mii_def mm_def split: option.splits ) apply force+  
    done
  done

lemma assumes "bindT M f = SPECT Mff" and "Mff x = Some t" 
  shows "\<exists>Mf y t1 Fxf t2. M = SPECT Mf \<and> Mf y = Some t1 \<and> f y = SPECT Fxf \<and> Fxf x = Some t2 \<and> t = t1 + t2"
  using assms  
  apply(auto simp: pw_eq_iff simp:  refine_pw_simps) 
  oops

lemma kl: "Inf S = Some (t::enat) \<longleftrightarrow> (Inf (Option.these S) = t \<and> None \<notin> S)" 
  unfolding Inf_option_def by auto 


lemma tz: "Inf S = Some (enat t) \<Longrightarrow> Inf S = (LEAST x. x \<in> S)"
  unfolding  Inf_option_def using Inf_enat_def  apply auto
  by (metis Inf_lower Inf_option_def LeastI Least_equality all_not_in_conv enat.distinct(2) in_these_eq option.sel)   


lemma assumes "T' Q M = Some (enat t)" 
  shows T'_SomeEnat: "(\<exists>Mf. M = REST Mf \<and> (\<exists>x t' t'' . Mf x = Some (enat t') \<and> Q x = Some (enat t'') \<and> t = t''-t' \<and> t''\<ge>t')
                           \<and> (\<forall>x t' t''. Mf x = Some (enat t') \<and> Q x = Some (enat t'') \<and> t''\<ge>t' \<longrightarrow> t \<le> t''-t' ))"
proof -
  from assms have "(LEAST t. t \<in> {mii Q M x |x. True}) = Some (enat t)" unfolding T'_def using tz by metis
  then have 1: "Some (enat t)\<in> {mii Q M x |x. True}" and 2: "\<forall>e\<in>{mii Q M x |x. True}. e\<ge> Some (enat t)"
    apply (metis (mono_tags, lifting) LeastI_ex mem_Collect_eq)
    by (metis (mono_tags) Inf_lower T'_def \<open>T' Q M = Some (enat t)\<close>)  


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






lemma T'_pw: "T' Q M \<ge> t \<longleftrightarrow> (\<forall>x. mii Q M x \<ge> t)"
  unfolding T'_def mii_def apply(cases M) apply auto
  unfolding Inf_option_def apply (auto split: if_splits)
  using less_eq_option_None_is_None less_option_None not_less apply blast
  apply (smt Inf_lower Inf_option_def dual_order.trans mem_Collect_eq)
  apply metis
  by (smt in_these_eq le_Inf_iff le_cases le_some_optE less_eq_option_Some mem_Collect_eq)  
  
lemma z: "(\<forall>t. T' Q M \<ge> t \<longrightarrow> T' Q' M' \<ge> t) \<Longrightarrow> T' Q M \<le> T' Q' M'"
  by simp

definition nres3 where "nres3 Q M x t \<longleftrightarrow> mii Q M x \<ge> t"
 
lemma assumes "\<And>t. (\<forall>x. nres3 Q M x t) \<Longrightarrow> (\<forall>x. nres3 Q' M' x t)"
  shows T'_au: "T' Q M \<le> T' Q' M'" apply(rule z)
  using assms unfolding T'_pw nres3_def  by metis 


fun po where "po None t = None" |
      "po (Some t1) t2 = Some (t1+t2)"
 

lemma t: "(\<forall>y. (t::enat option) \<le> f y) \<longleftrightarrow> (t\<le>Inf {f y|y. True})"  
  using le_Inf_iff by fastforce  

lemma LeastD: "(LEAST n. n \<in> N) = X \<Longrightarrow> X\<in>N \<and> (\<forall>x\<in>N. X\<le>x)"  oops

lemma helper: "x2 \<le> x2a \<Longrightarrow> \<not> x2 < a \<Longrightarrow> \<not> x2a < a \<Longrightarrow>  x2 - (a::enat) \<le> x2a - a"
  apply(cases x2; cases x2a) apply auto apply(cases a) by auto



lemma mm_mono: "Q1 x \<le> Q2 x \<Longrightarrow> mm Q1 M x \<le> mm Q2 M x"
  unfolding mm_def apply(cases "M x") apply (auto split: option.splits)
  using le_some_optE apply blast apply(rule helper) by auto

lemma helper2: "x2b \<le> x2 \<Longrightarrow> \<not> x2a < x2  \<Longrightarrow> \<not> x2a < x2b \<Longrightarrow> x2a - (x2::enat) \<le> x2a - x2b"
    apply(cases x2; cases x2a) apply auto apply(cases x2b) by auto

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
  

lemma mii_continuous: "mii (\<lambda>x. Inf {f y x|y. True}) m x = Inf {mii (%x. f y x) m x|y. True}"
  unfolding mii_def apply(cases m) subgoal apply auto done
  subgoal apply auto using mm_continous by metis 
  done


lemma miiFailt: "mii Q FAILT x = None" unfolding mii_def by auto

lemma Sup_enat_less2: "X \<noteq> {} \<Longrightarrow>   Sup X = \<infinity> \<Longrightarrow> (\<exists>x\<in>X. enat t < x)"
   
  subgoal unfolding  Sup_enat_def using    finite_enat_bounded linear 
    apply(auto split: if_splits)  
    apply (smt Max_in empty_iff enat_ord_code(4))
    by (smt not_less)   
  done

lemma "Max {} = (bot::enat)" oops


lemma less_eq_option_None_is_None': "x \<le> None \<longleftrightarrow> x = None" by(auto simp: less_eq_option_None_is_None)

 
lemma [simp]: "t \<le> Some (\<infinity>::enat)"
  by (cases t, auto)

lemma everywhereNone: "(\<forall>x\<in>X. x = None) \<longleftrightarrow> X = {} \<or> X = {None}"
  by auto

lemma Sup_finite_enat: "Sup X = Some (enat a) \<Longrightarrow> Some (enat a) \<in> X"
  by (auto simp: Sup_option_def Sup_enat_def these_empty_eq Max_eq_iff in_these_eq split: if_splits)

lemma mm2_contiuous2: "\<forall>x\<in>X. t \<le> mm2 q x \<Longrightarrow> t \<le> mm2 q (Sup X)"
  unfolding mm2_def apply(auto simp: everywhereNone bot_option_def less_eq_option_None_is_None' split: option.splits if_splits)
  subgoal by (metis (no_types, lifting) Sup_option_def in_these_eq less_Sup_iff option.distinct(1) option.sel) 
  subgoal for tx tq by(cases tq; cases tx; fastforce dest!: Sup_finite_enat)
  done
  
lemma Sup_SPECT_D: "Sup X = SPECT m \<Longrightarrow> m x = Sup {f x | f. REST f \<in> X}"
  unfolding Sup_nrest_def apply(auto split: if_splits) unfolding Sup_fun_def  
  apply(fo_rule arg_cong) by blast

lemma mm2_antimono: "x \<le> y \<Longrightarrow> mm2 q x \<ge> mm2 q y"
  unfolding mm2_def apply (auto split: option.splits)
  using helper2 by blast 
 
lemma mii_cont: "(mii Q (Sup {F x t1 |x t1. P x t1}) x \<ge> t) = (\<forall>y t1. P y t1 \<longrightarrow> mii Q (F y t1) x \<ge> t)"
  unfolding mii_alt apply auto apply (auto simp: ll less_eq_option_None_is_None' split: nrest.splits)
  subgoal by (smt ll(2) mem_Collect_eq nres_order_simps(1) top_greatest) 
  subgoal for y t1 x2 x2a
    apply(drule Sup_SPECT_D[where x=x])
    apply(rule order.trans[where b="mm2 (Q x) (x2 x)"]) apply simp
    apply(rule mm2_antimono) by (metis (mono_tags, lifting) Sup_upper mem_Collect_eq)
  subgoal 
    apply(drule Sup_SPECT_D[where x=x])
    by (auto intro: mm2_contiuous2) 
  done
(*

lemma mii_cont': "(mii Q (Sup {F x t1 |x t1. P x t1}) x \<ge> t)
            = (\<forall>y t1. P y t1 \<longrightarrow> mii Q (F y t1) x \<ge> t)"
  apply safe
  subgoal for y t1
    unfolding mii_def apply (auto split: nrest.splits)
    subgoal using less_eq_option_None_is_None less_option_None not_less by blast
     apply (smt ll(2) mem_Collect_eq nres_order_simps(1) top_greatest) 
  proof -
    fix Sf Ff
    assume i: "P y t1" "F y t1 = SPECT Ff" and iii:"Sup {F x t1 |x t1. P x t1} = SPECT Sf" and ii: "t \<le> mm Q Sf x"
    from i have i1: "SPECT Ff \<in> {F x t1 |x t1. P x t1}" by force
    then have "SPECT Ff \<le> Sup {F x t1 |x t1. P x t1}" by (simp add: Sup_upper)
    with iii have i2: "Sf \<ge> Ff" by auto
    have "mm Q Sf x \<le> mm Q Ff x" apply(rule mm_antimono) using i2 by(auto simp: le_fun_def)
    with ii show "t \<le> mm Q Ff x" by simp
  qed 
proof -
  assume a: " \<forall>y t1. P y t1 \<longrightarrow> t \<le> mii Q (F y t1) x"
  show "t \<le> mii Q (Sup {F x t1 |x t1. P x t1}) x"
  proof (cases "(Sup {F x t1 |x t1. P x t1}) = FAILT")
    case True
    then obtain fx ft1 where i: "F fx ft1 = FAILT" and p: "P fx ft1" unfolding ll 
      by (smt mem_Collect_eq) 
    from p a have "t \<le> mii Q (F fx ft1) x" by force
    with i have "t \<le> None" by(simp add: miiFailt)
    then show ?thesis using True by(simp add: miiFailt)
  next
    case False
    then have "\<forall>y t1. P y t1 \<longrightarrow> F y t1 \<noteq> FAILT" unfolding ll by force
    then have t: "\<forall>y t1. P y t1 \<longrightarrow> (\<exists>Ff. F y t1 = SPECT Ff)"
      by (metis nrest.exhaust top_nrest_def)  
    then obtain Ff where k: "\<forall>y t1. P y t1 \<longrightarrow> F y t1 = SPECT (Ff y t1)"
      by metis
    from k a have "\<forall>y t1. P y t1 \<longrightarrow> t \<le> mii Q (SPECT (Ff y t1)) x" by auto
    then have klae: "\<forall>y t1. P y t1 \<longrightarrow> t \<le> mm Q (Ff y t1) x" unfolding mii_def by auto

    from k have zz: "\<forall>y t1. P y t1 \<longrightarrow> SPECT (Ff y t1) \<le> Sup {F x t1 |x t1. P x t1}"
      by (metis (mono_tags, lifting) Sup_upper mem_Collect_eq) 
    thm setcompr_eq_image
    have pe: "{F x t1 |x t1. P x t1} = {SPECT (Ff x t1)|x t1. P x t1}" 
      using k by force  

    

    from False obtain Sf where k: "Sup {F x t1 |x t1. P x t1} = SPECT Sf" by fastforce 
    have mimm: "mii Q (Sup {F x t1 |x t1. P x t1}) x = mm Q Sf x" 
      unfolding mii_def k by auto

    from k[unfolded pe] have SfS: "Sf = Sup {(Ff x t1) |x t1. P x t1}" unfolding Sup_nrest_def by auto
    



    from zz k have "\<forall>y t1. P y t1 \<longrightarrow> SPECT (Ff y t1) \<le> SPECT Sf" by auto
    then have "\<forall>y t1. P y t1 \<longrightarrow> (Ff y t1) \<le> Sf" by auto
    then have pl: "\<forall>y t1. P y t1 \<longrightarrow> mm Q (Ff y t1) x \<ge> mm Q Sf x" apply auto
      apply(rule mm_antimono) unfolding le_fun_def by blast

    have pr: "\<And>y. {(Ff x t1) y |x t1. P x t1} = (\<lambda>f. f y) `{(Ff x t1) |x t1. P x t1}"
      apply rule  by auto

    have o: "\<And>y. (Sup {(Ff x t1) |x t1. P x t1}) y = (Sup {(Ff x t1) y |x t1. P x t1})"
      unfolding Sup_fun_def pr ..


    { assume "Sf x = None"
      then have "mm Q Sf x = Some \<infinity>" unfolding mm_def by auto
    } note 1=this
    {
      assume nN: "Sf x \<noteq> None"
      have th: "\<forall>y t1. P y t1 \<longrightarrow> (Ff y t1) x = None \<Longrightarrow> (Sup {(Ff x t1) |x t1. P x t1}) x = None"
        unfolding o
        by (smt Sup_bot_conv(2) Sup_empty empty_Sup mem_Collect_eq) 
       
      have "\<exists>ex et1. P ex et1 \<and> Ff ex et1 x \<noteq> None"  
        apply(rule ccontr)
        using th nN SfS by auto
      then obtain ex et1 where p: "P ex et1" and enN: "Ff ex et1 x \<noteq> None" by blast 

      from klae p have tt: "t \<le> mm Q (Ff ex et1) x" by force 

      from p have "Ff ex et1 \<le> Sup {Ff x t1 |x t1. P x t1}"
        by (metis (mono_tags, lifting) Sup_upper mem_Collect_eq) 
      then have i: "(Ff ex et1) x \<le> Sf x" using k SfS by (auto simp: le_fun_def) 
      then have pl: "mm Q (Ff ex et1) x \<ge> mm Q Sf x"  
        by(rule mm_antimono)

      have  "Q x = None \<Longrightarrow> mm Q (Ff ex et1) x = None" unfolding mm_def using enN by auto
      then have tNone: "Q x = None \<Longrightarrow> t = None" using tt less_eq_option_None_is_None by auto
      from nN obtain a where Sfa: "Sf x = Some a" by blast

      { assume "a=\<infinity>"
        then have "(Sup {(Ff x t1) |x t1. P x t1}) x = Some \<infinity>"
          using Sfa SfS by auto
        then have "(Sup {(Ff y t1) x |y t1. P y t1}) = Some \<infinity>" unfolding Sup_fun_def
          unfolding pr .
        then have inf: "Sup (Option.these {Ff y t1 x |y t1. P y t1}) = \<infinity>" 
          unfolding Sup_option_def by(auto split: if_splits)
        then have ne: "(Option.these {Ff y t1 x |y t1. P y t1}) \<noteq> {}"           
          using Sup_enat_def by auto 
        from Sup_enat_less2[OF ne, unfolded inf] have "\<forall>e::nat. (\<exists>x\<in>Option.these {Ff y t1 x |y t1. P y t1}. enat e < x)" by auto
        then have "\<forall>e::nat. (\<exists>y t1. Ff y t1 x > Some (enat e) \<and> P y t1)"
          by (smt in_these_eq less_option_Some mem_Collect_eq) (* 
          by (smt in_these_eq less_eq_option_Some mem_Collect_eq) *)
      } note kaa=this
            
      { fix e 
        assume "a= enat e"
        then have "(Sup {(Ff x t1) |x t1. P x t1}) x = Some (enat e)"
          using Sfa SfS by auto
        then have gl: "(Sup {(Ff y t1) x |y t1. P y t1}) = Some (enat e)" unfolding Sup_fun_def
          unfolding pr .
        then have inf: "Sup (Option.these {Ff y t1 x |y t1. P y t1}) = (enat e)" 
          unfolding Sup_option_def by(auto split: if_splits)
        have "(Option.these {Ff y t1 x |y t1. P y t1}) \<noteq> {}" using gl
          unfolding Sup_option_def apply(auto split: if_splits)  
          apply (smt Some_image_these_eq Sup_apply Sup_empty Sup_le_iff Sup_upper \<open>Sup {Ff x t1 |x t1. P x t1} x = Some (enat e)\<close> ccSUP_empty empty_Sup less_eq_option_Some_None mem_Collect_eq pr)
          sorry
        from inf have "Max (Option.these {Ff y t1 x |y t1. P y t1}) = (enat e)" unfolding Sup_enat_def
          apply(auto split: if_splits)
          by (smt Some_image_these_eq Sup_apply Sup_empty Sup_le_iff \<open>Sup {Ff x t1 |x t1. P x t1} x = Some (enat e)\<close> ccSUP_empty empty_Sup less_eq_option_Some_None mem_Collect_eq order_mono_setup.refl pr) 
        then have "\<exists>y t1. Ff y t1 x = Some (enat e) \<and> P y t1"
          unfolding Sup_enat_def sorry
      }

      have "t \<le> mm Q Sf x"
      proof (cases "Q x")
        case None
        then show ?thesis  using   tNone  by (auto ) 
      next
        case (Some qa)
        show ?thesis
        proof (cases qa)
          case qa: (enat qaa)
          then show ?thesis
          proof (cases "a")
            case (enat aa)
            then show ?thesis sorry
          next
            case infinity
            with kaa obtain ay at1 where absch: "Ff ay at1 x > Some (enat qaa)" and pa: "P ay at1" by blast
            from pa klae have t1: "t \<le> mm Q (Ff ay at1) x" by auto
            from absch Some qa have t2: "mm Q (Ff ay at1) x = None" unfolding mm_def  
              apply(auto split: option.splits)
              using not_None_eq by fastforce 
            from t1 t2 have "t=None"
              by (simp add: less_eq_option_None_is_None) 
            then show ?thesis by auto
          qed
        next
          case infinity
          with Some show ?thesis unfolding mm_def using nN apply auto by(auto simp: top_option_def[symmetric] top_enat_def[symmetric])
        qed 
      qed   
    } note 2=this 

    show ?thesis unfolding mimm apply(cases "Sf x = None")
      subgoal using 1 by(auto simp: top_option_def[symmetric] top_enat_def[symmetric])
      subgoal apply(rule 2) .
      done
  qed 
qed
(*
  subgoal 
    unfolding mii_def apply (auto split: nrest.splits)
    subgoal unfolding Sup_nrest_def by(auto split: if_splits) 
    unfolding mm_def subgoal for x2
      apply(cases "x2 x") subgoal by (auto simp: top_option_def[symmetric] top_enat_def[symmetric])
      apply simp apply(cases "Q x")
      subgoal for a apply (auto split: option.splits)   
        unfolding Sup_nrest_def apply (auto split: if_splits) 
        apply(cases t) apply auto
        by (smt SUP_least eq_iff less_eq_option_Some_None mem_Collect_eq)
      subgoal for a aa apply auto
        unfolding Sup_nrest_def apply (auto split: if_splits option.splits) 
        subgoal apply(cases t) apply auto
          by (smt SUP_least leD le_less_linear le_some_optE less_option_Some linear mem_Collect_eq) 
        subgoal apply(cases t) apply auto 
  
    sorry
  done
*)
*)

lemma mm_contracontinuous: "mm Q (\<lambda>x. Sup {f y x|y. True}) x = Inf {mm Q (%x. f y x) x|y. True}" 
  oops

lemma "nres3 Q (bindT m f) x t \<longleftrightarrow> (\<forall>y. nres3 (\<lambda>y. mii Q (f y) x) m y t)"
  oops

(*
lemma "nres3 Q (\<lambda>x. Sup {f y x|y. P x y}) x t \<longleftrightarrow> (\<forall>y. P x y \<longrightarrow> nres3 Q (f y) x t)"
*)
(*
lemma "t \<le> mm Q (\<lambda>x. Sup {fa. \<exists>y. P x y  \<and> fa = f x y}) x
 \<longleftrightarrow> (\<forall>y. P x y \<longrightarrow> t \<le> mm Q (\<lambda>x. f x y)  x)" (is "?L \<longleftrightarrow> ?R")
proof (cases "Sup {fa. \<exists>y. P x y \<and> fa = f x y}")
  case None
  then have "\<forall>y. P x y \<longrightarrow> f x y = None" unfolding Sup_option_def sorry
  then have "?R"
    unfolding mm_def by (auto simp: top_option_def[symmetric] top_enat_def[symmetric]) 
  moreover
  from None have "?L" unfolding mm_def by (auto simp: top_option_def[symmetric] top_enat_def[symmetric]) 
  ultimately show ?thesis by simp
next
  case (Some a)
  then show ?thesis  oops

lemma "t \<le> mii Q (bindT m f) x \<Longrightarrow> (\<forall>y. t \<le> mii (\<lambda>y. mii Q (f y) x) m y)"
  unfolding mii_def bindT_def apply(cases m) subgoal apply auto done
  subgoal apply auto apply (auto   split: nrest.splits)
    subgoal using less_eq_option_None_is_None by fastforce  
    apply(auto simp: Sup_nrest_def split: if_splits)
    oops
*)

lemma mii_cont: "(mii Q (Sup {case f y of FAILi \<Rightarrow> FAILT | REST m2 \<Rightarrow> SPECT (map_option (op + t1) \<circ> m2) |y t1. M y = Some t1}) x \<ge> t)
            = (\<forall>y t1. M x = Some t1 \<longrightarrow> mii Q (case f x of FAILi \<Rightarrow> FAILT | REST m2 \<Rightarrow> SPECT (map_option (op + t1) \<circ> m2)) x \<ge> t)"
  oops



lemma Inf_r: "(\<forall>y t1. P y t1 \<longrightarrow> f (F y t1) \<ge> (t::enat option)) = (Inf {f (F y t1)|y t1. P y t1} \<ge> t)"
  oops


lemma lem: "\<forall>t1. M y = Some t1 \<longrightarrow> t \<le> mii Q (SPECT (map_option (op + t1) \<circ> x2)) x \<Longrightarrow> f y = SPECT x2 \<Longrightarrow> t \<le> mii (\<lambda>y. mii Q (f y) x) (SPECT M) y"
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

lemma lem2: "t \<le> mii (\<lambda>y. mii Q (f y) x) (SPECT M) y \<Longrightarrow> M y = Some t1 \<Longrightarrow> f y = SPECT fF \<Longrightarrow> t \<le> mii Q (SPECT (map_option (op + t1) \<circ> fF)) x"
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
    let ?F = "%x t1. case f x of FAILi \<Rightarrow> FAILT | REST m2 \<Rightarrow> SPECT (map_option (op + t1) \<circ> m2)"
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
    also have "\<dots> = (\<forall>y t1. ?P y t1 \<longrightarrow> mii Q (?F y t1) x \<ge> t)" by (rule mii_cont)  
    also have "\<dots> = (\<forall>y. t \<le> mii (\<lambda>y. mii Q (f y) x) m y)" by(simp only: blub)
    finally have ?thesis .
  } note bl=this

  show ?thesis apply(cases m)
    subgoal by (simp add: mii_def)
    subgoal apply(rule bl) .
    done
qed


lemma nres3_bindT: "(\<forall>x. nres3 Q (bindT m f) x t) = (\<forall>y. nres3 (\<lambda>y. T' Q (f y)) m y t)"
proof -
  have "(\<forall>x. nres3 Q (bindT m f) x t) = (\<forall>x.  t \<le> mii Q (bindT m f) x)" unfolding nres3_def by auto
  also have "\<dots> = (\<forall>x. (\<forall>y. t \<le> mii (\<lambda>y. mii Q (f y) x) m y))" by(simp only: mii_bindT)
  also have "\<dots> = (\<forall>y. (\<forall>x. t \<le> mii (\<lambda>y. mii Q (f y) x) m y))" by blast
  also have "\<dots> = (\<forall>y.  t \<le> mii (\<lambda>y. Inf {mii Q (f y) x|x. True}) m y)" 
    apply(simp only: mii_continuous) using t by fast
  also have "\<dots> = (\<forall>y.  t \<le> mii (\<lambda>y. T' Q (f y)) m y)" unfolding T'_def by auto
  also have "\<dots> = (\<forall>y. nres3 (\<lambda>y. T' Q (f y)) m y t)" unfolding nres3_def by auto
  finally show ?thesis .
  have "(\<forall>y.  t \<le> mii (\<lambda>y. T' Q (f y)) m y) = (t \<le> Inf{ mii (\<lambda>y. T' Q (f y)) m y|y. True})" using t by metis
qed


lemma assumes "\<And>t. (\<forall>x. nres3 Q M x t) = (\<forall>x. nres3 Q' M' x t)" 
  shows T'_eq_iff: "T' Q M = T' Q' M'"
  apply (rule antisym)
  apply(rule T'_au) using assms apply metis
  apply(rule T'_au) using assms apply metis done 

lemma assumes "\<And>t. (\<forall>x. nres3 Q M x t) \<Longrightarrow> (\<forall>x. nres3 Q' M' x t)"
      "\<And>t. (\<forall>x. nres3 Q' M' x t) \<Longrightarrow> (\<forall>x. nres3 Q M x t)"
  shows T'_eqI: "T' Q M = T' Q' M'"
  apply (rule antisym)
  apply(rule T'_au) apply fact
  apply(rule T'_au) apply fact done 
  

lemma T'_bindT: "T' Q (bindT M f) = T' (\<lambda>y. T' Q (f y)) M"
  by (rule T'_eq_iff, rule nres3_bindT)


lemma [simp]: "mm2 q None = Some \<infinity>" unfolding mm2_def by auto



lemma T'_REST: "T' Q (REST [x\<mapsto>t]) = mm2 (Q x) (Some t)"
proof- 
  have *: "Inf {uu. \<exists>xa. (xa = x \<longrightarrow> uu= v) \<and> (xa \<noteq> x \<longrightarrow> uu = Some \<infinity>)} = v"  (is "Inf ?S = v") for v :: "enat option"
  proof -
    have "?S \<in> { {v} \<union> {Some \<infinity>}, {v}  }" by auto 
    then show ?thesis apply simp apply safe by (simp_all add: top_enat_def[symmetric] top_option_def[symmetric] ) 
  qed
  then show ?thesis
    unfolding T'_def mii_alt by auto
qed

lemma RETURNT_alt: "RETURNT x = REST [x\<mapsto>0]"
  unfolding RETURNT_def by auto

lemma mm2_0[simp]: "mm2 q (Some 0) = q" unfolding mm2_def by (auto split: option.splits)

lemma T'_RETURNT: "T' Q (RETURNT x) = Q x"
  unfolding RETURNT_alt apply(rule trans) apply(rule T'_REST) by simp


lemma assumes 
      "T' Q' f \<ge> Some 0"
      "T' Q (SPECT Q') \<ge> Some 0"
    shows T'_conseq: "T' Q f \<ge> Some 0"
  sorry

lemma "T' Q M \<ge> t \<longleftrightarrow> (\<forall>x. nres3 Q M x t)"
  unfolding T'_def nres3_def
  by (metis T'_def T'_pw) 

lemma assumes 
      "T' Q' f \<ge> Some 0"
      "\<And>x. mm2 (Q x) (Q' x) \<ge> Some 0"
    shows T'_conseq2: "T' Q f \<ge> Some 0"
  sorry

lemma assumes 
      "T' Q' f \<ge> Some t'"
      "\<And>x. mm2 (Q x) (Q' x) \<ge> Some (t - t')" 
    shows T'_conseq3: "T' Q f \<ge> Some t"
  sorry


definition "P f g = bindT f (\<lambda>x. bindT g (\<lambda>y. RETURNT (x+(y::nat))))"

lemma "T' (\<lambda>x. Q x) (P f g) \<ge> Some 0"
  unfolding P_def apply(simp add: T'_bindT T'_RETURNT ) sorry

definition emb where "emb Q (t::enat) = (\<lambda>x. if Q x then Some t else None)"

definition emb' where "\<And>Q T. emb' Q (T::'a \<Rightarrow> enat) = (\<lambda>x. if Q x then Some (T x) else None)"


lemma aux1: "Some t \<le> mm2 Q (Some t') \<longleftrightarrow> Some (t+t') \<le> Q"
  apply (auto simp: mm2_def split: option.splits)
  subgoal for t''
    by (cases t; cases t'; cases t''; auto)
  subgoal for t''
    by (cases t; cases t'; cases t''; auto)
  subgoal for t''
    by (cases t; cases t'; cases t''; auto)
  done

lemma [simp]: "Some (t::enat) \<le> mm2 Q (emb Q' t' x) \<longleftrightarrow> (Q' x \<longrightarrow> Some (t+t') \<le> Q)"
  by (auto simp: emb_def aux1)

lemma [simp]: "Some t' \<le> emb Q t x \<longleftrightarrow> ( t'\<le>t \<and> Q x)"
  by (auto simp: emb_def)

lemma [simp]: "emb' Q T x = emb Q (T x) x" for T
  by (auto simp: emb_def emb'_def)
  


lemma assumes
  f_spec: "T' ( emb' (\<lambda>x. x > 2) (enat o op * 2) ) f \<ge> Some 0"
and 
  g_spec: "T' ( emb' (\<lambda>x. x > 2) (enat) ) g \<ge> Some 0"
shows "T' ( emb' (\<lambda>x. x > 5) (enat o op * 3) ) (P f g) \<ge> Some 0"
  unfolding P_def apply(simp add: T'_bindT )
  apply(simp add:  T'_RETURNT)
  apply(rule T'_conseq3[OF f_spec])
    apply(clarsimp)
  apply(rule T'_conseq3[OF g_spec])
  apply clarsimp 
  done



   



(*
lemma "nres3 Q (bindT M f) x t \<longleftrightarrow> (\<forall>r. nres3 (\<lambda>x. mii Q (f r) x) M r t)"
  apply rule
  subgoal (* \<rightarrow> *)
    unfolding nres3_def mii_def apply(cases M) 
     apply(auto split: nrest.splits)                           
    subgoal
      using less_eq_option_None_code less_eq_option_None_is_None by blast          
    subgoal for x2 x2a r apply(cases "f r")
      apply(auto split: nrest.splits) 
      subgoal by (metis kla mm_inf2 nofailT_simps(1) nofailT_simps(2) pw_bindT_nofailT_2 top_enat_def top_greatest top_option_def)
      subgoal    unfolding mm_def  bindT_def apply (auto split: option.splits) sorry
      done
    done
  subgoal (* <- *)
    oops
*)

lemma pf_minus_enat: "t \<le> F - M \<Longrightarrow> \<forall>t'\<ge>F. t \<le> t' - (M::enat)" apply auto
  apply(cases F) apply auto 
  subgoal for t' apply (cases t') apply auto
    apply(cases M) apply auto apply(cases t) by auto
  done

lemma pf_minus_enat_iff: "t \<le> F - M \<longleftrightarrow> (\<forall>t'\<ge>F. t \<le> t' - (M::enat))" apply auto 
  apply(cases F) apply auto 
  subgoal for t' apply (cases t') apply auto
    apply(cases M) apply auto apply(cases t) by auto
  done


lemma pf_minus_enatoption : "t \<le> mm F M x \<Longrightarrow> (\<forall>t'\<ge>F x. t \<le> mm (\<lambda>_. t') M x)"
  unfolding mm_def apply(cases "M x")
   apply auto apply(cases "F x") apply auto
  subgoal
    using less_eq_option_None_is_None by fastforce  
  subgoal apply(auto split: if_splits)
    subgoal
      using less_eq_option_None_is_None by fastforce  
    subgoal
      by (smt le_less_trans le_some_optE less_eq_option_Some less_eq_option_Some_None linear option.case_eq_if option.sel pf_minus_enat)
    done
  done

lemma pf_minus_enatoption_iff: "t \<le> mm F M x \<longleftrightarrow> (\<forall>t'\<ge>F x. t \<le> mm (\<lambda>_. t') M x)"
  unfolding mm_def apply(cases "M x")
   apply auto apply(cases "F x") apply auto
  subgoal
    using less_eq_option_None_is_None by fastforce  
  subgoal apply(auto split: if_splits)
    subgoal
      using less_eq_option_None_is_None by fastforce  
    subgoal
      by (smt le_less_trans le_some_optE less_eq_option_Some less_eq_option_Some_None linear option.case_eq_if option.sel pf_minus_enat)
    done
  done


lemma pf_minus_nrest: "t \<le> mii F M x \<Longrightarrow> \<forall>t'\<ge>F x. t \<le> mii (\<lambda>_. t') M x"
  unfolding mii_def apply(cases M) subgoal by auto
  apply auto using pf_minus_enatoption by metis

lemma mii_onx: "F x=F' x \<Longrightarrow> mii F M x = mii F' M x "
  unfolding mii_def mm_def by metis

lemma pf_minus_nrest': "\<forall>t'\<ge>F x. t \<le> mii (\<lambda>_. t') M x \<Longrightarrow> t \<le> mii F M x"
  using mii_onx[of F x "(\<lambda>_. F x)"] by simp 


lemma pf_minus_nrest_iff: "t \<le> mii F M x \<longleftrightarrow> (\<forall>t'\<ge>F x. t \<le> mii (\<lambda>_. t') M x)"
  using pf_minus_nrest pf_minus_nrest' by metis

                                                
lemma G: "nres3 F M x t \<longleftrightarrow> (\<forall>t'. F x \<le> t' \<longrightarrow> nres3 (\<lambda>_. t') M x t)"
  unfolding nres3_def using pf_minus_nrest_iff by metis   




lemma pw_nres3_bindT': "nres3 Q (bindT M f) x t \<longleftrightarrow> (\<forall>r. nres3 (\<lambda>r. mii Q (f r) x) M r t)"
  apply(subst (2) G) unfolding bindT_def nres3_def  oops

(*
lemma pw_nres3_bindT: "nres3 Q (bindT M f) x t \<longleftrightarrow> (\<forall>r t'. nres3 Q (f r) x t' \<longrightarrow> nres3 (\<lambda>_. t') M r t)"
  apply rule
  subgoal (* \<rightarrow> *)
    unfolding nres3_def mii_def apply(cases M) 
     apply(auto split: nrest.splits)                           
    subgoal
      using less_eq_option_None_code less_eq_option_None_is_None by blast        
    subgoal
      using less_eq_option_None_code less_eq_option_None_is_None by blast    
    subgoal 
      by (metis kla mm_inf2 nofailT_simps(1) nofailT_simps(2) pw_bindT_nofailT_2 top_enat_def top_greatest top_option_def) 
    subgoal for x2 x2a r x2b t'
      unfolding mm_def  
      sorry
    done
  subgoal (* <- *)
    sorry
  done 
*)

(*
lemma  T'_SomeEnat_iff:  "T' Q M = Some (enat t) \<longleftrightarrow> (\<exists>Mf. M = REST Mf \<and> (\<exists>x t' t'' . Mf x = Some (enat t') \<and> Q x = Some (enat t'') \<and> t = t''-t' \<and> t''\<ge>t')
                           \<and> (\<forall>x t' t''. Mf x = Some (enat t') \<and> Q x = Some (enat t'') \<and> t''\<ge>t' \<longrightarrow> t \<le> t''-t' ))"
  sorry
*)

term inresT
thm inresT_def

lemma assumes "T' Q M = Some (enat t)" 
  shows "(\<exists>x t' t'' Mf. M = REST Mf \<and> Mf x = Some (enat t') \<and> Q x = Some (enat t'') \<and> t = t''-t' \<and> t''\<ge>t')"
proof -
  from assms have "(LEAST t. t \<in> {mii Q M x |x. True}) = Some (enat t)" unfolding T'_def using tz by metis
  then have 1: "Some (enat t)\<in> {mii Q M x |x. True}" and "\<forall>e\<in>{mii Q M x |x. True}. e\<ge> Some (enat t)"
    apply (metis (mono_tags, lifting) LeastI_ex mem_Collect_eq)
    by (metis (mono_tags) Inf_lower T'_def \<open>T' Q M = Some (enat t)\<close>)  

  from 1 have "\<exists>x. mii Q M x = Some (enat t)" by auto
  then obtain x where "mii Q M x = Some (enat t)" by blast
  then obtain Mf where Mf: "M = SPECT Mf" and "mm Q Mf x = Some (enat t)"  unfolding mii_def
    by(auto split: nrest.splits)
  then obtain t' t'' where [simp]: "Mf x = Some t'" "Q x = Some t''" and t: "t''-t'=enat t" "t''\<ge>t'" unfolding mm_def by (auto split: option.splits if_splits)
  from t obtain t2' t2'' where e: "enat t2' = t'" "enat t2'' = t''"
    apply(cases t'; cases t'') by auto 
  
  show "(\<exists>x t' t'' Mf. M = REST Mf \<and> Mf x = Some (enat t') \<and> Q x = Some (enat t'') \<and> t = t''-t' \<and> t''\<ge>t')"
    apply(rule exI[where x=x])
    apply(rule exI[where x=t2'])
    apply(rule exI[where x=t2''])
    apply(rule exI[where x=Mf]) using t Mf e by auto 
qed

(*
lemma "T' Q M = Some t \<Longrightarrow> (\<exists>x t' t'' Mf. M = REST Mf \<and> Mf x = Some t' \<and> Q x = Some t'' \<and> t = t''-t' \<and> t''\<ge>t')"
proof -
  assume "T' Q M = Some t"
  then have "Inf (Option.these {mii Q M x |x. True}) = t" and ii: "None \<notin> {mii Q M x |x. True}" 
    unfolding T'_def unfolding kl by (auto )

  from ii have "M\<noteq>FAILi" by (auto simp: mii_def)
  then obtain Mf where "M= REST Mf" using nrest.exhaust by auto 
  

  unfolding mii_def apply (auto split: nrest.splits)
  unfolding mm_def apply (auto split: option.splits)
  oops
*)

(*
lemma "T' Q (bindT M f) = T' (\<lambda>y. T' Q (f y)) M"
proof (cases "T' Q (bindT M f)")
  case None  
  with T'_None_char have 
      "((bindT M f) = FAILi \<or> (\<exists>Mf t x. (bindT M f) = SPECT Mf \<and> Mf x = Some t \<and> (Q x = None \<or> (\<exists>t'. Q x = Some t' \<and> t' < t))))" by auto
  then consider (FAIL) "(bindT M f) = FAILi" | 
               (NOFAIL) "(bindT M f) \<noteq> FAILi" and "(\<exists>Mf t x. (bindT M f) = SPECT Mf \<and> Mf x = Some t \<and> (Q x = None \<or> (\<exists>t'. Q x = Some t' \<and> t' < t)))"
    by auto 
  then show ?thesis
  proof cases
    case FAIL
    with pw_bindT_nofailT have "M = FAILi \<or> (\<exists>x t. inresT M x t \<and> (f x) = FAILi)"
      unfolding nofailT_def by auto
    then consider (failM) "M = FAILi" | (failF) "M \<noteq> FAILi" and "(\<exists>x t. inresT M x t \<and> (f x) = FAILi)" by auto
    then show ?thesis 
    proof cases
      case failM
      then have "T' (\<lambda>y. T' Q (f y)) M = None" unfolding T'_def by(auto simp: mii_def)
      with None show ?thesis by simp
    next
      case failF
      then obtain y t where i: " inresT M y t" and e: "f y = FAILi" by blast
      from i obtain Mf t' where "M = SPECT Mf" "Mf y= Some t'" "enat t \<le> t'" unfolding inresT_def using failF(1) 
        by (auto split: nrest.splits)
      from e have ii: "T' Q (f y) = None" by (auto simp: T'_def mii_def)
      have "T' (\<lambda>y. T' Q (f y)) M = None" 
        apply(rule fall2) by fact+ 
      with None show ?thesis by simp
    qed
  next
    case NOFAIL
    then obtain Mff t x where i: "bindT M f = SPECT Mff" and a: "Mff x = Some t" and
                   z: "(Q x = None \<or> (\<exists>t'. Q x = Some t' \<and> t' < t))" by blast

    {assume "t < \<infinity>"
    then obtain te where te: "t = enat te" using less_infinityE by blast

    have inr: "inresT (bindT M f) x te" unfolding inresT_def using i a te by(auto)
    from i have o: "nofailT (bindT M f)" by auto 
    with pw_bindT_nofailT have iii: "nofailT M \<and> (\<forall>x t. inresT M x t \<longrightarrow> nofailT (f x))" unfolding nofailT_def by auto
    from iii have noM: "nofailT M" by auto
    with  inr have 
        "(\<exists>r' t' t''. inresT M r' t' \<and> inresT (f r') x t'' \<and> te = t' + t'')" by(simp only: pw_inresT_bindT)
    then obtain r' t' t'' where i1: "inresT M r' t'" and i2: "inresT (f r') x t''" and t: "te = t' + t''" 
      by blast
    from iii have "(\<forall>x t. inresT M x t \<longrightarrow> (\<exists>Fxf.  f x = SPECT Fxf) )"   unfolding nofailT_def
      by (metis nrest.exhaust top_nrest_def) 

    from iii i1 have noFf: "nofailT (f r')" by auto
    
    from i1 obtain Mf1 t1' where "M = SPECT Mf1" "Mf1 r'= Some t1'" "enat t' \<le> t1'" unfolding inresT_def  using noM[unfolded nofailT_def]
      by (auto split: nrest.splits)
    from i2 obtain Mf2 t2' where "(f r') = SPECT Mf2" "Mf2 x= Some t2'" and pf: "enat t'' \<le> t2'" unfolding inresT_def  using noFf
      by (auto split: nrest.splits)

    from z consider (Qnone) "Q x = None" | (Qsome) " (\<exists>t'. Q x = Some t' \<and> t' < t)" by auto
    then have "T' (\<lambda>y. T' Q (f y)) M = None"
    proof cases
      case Qnone
      show ?thesis
        apply(rule fall2) apply fact+
        apply(rule fall2) by fact+
    next
      case Qsome
      then obtain tq where "Q x = Some tq" and p: "tq < t " by blast
      have "tq < t2'" using p te t pf   sorry
      have "tq < t" by fact
      also have "\<dots> = enat te" by fact
      also have "\<dots> = enat (t' + t'')" using t by auto
      also have "\<dots> = enat t' + enat t''" by auto
      also have "\<dots> \<le> enat t' +  t2'" using pf
        using add_mono_thms_linordered_semiring(2) by blast 
      
      show ?thesis 
        apply(rule fall3) apply fact+

          (* here a T' Q (f r') = Some ?t' occurs! *)

        apply(rule fall3) apply fact apply fact apply fact   sorry
    qed
  }
        show ?thesis sorry
  qed
next
  case (Some a)
  show ?thesis
  proof (cases a)
    case (enat t)
    with Some have L: "T' Q (bindT M f) = Some (enat t)" by simp
    then  obtain Mff x t' t'' where "bindT M f = SPECT Mff"
            "Mff x = Some (enat t')" "Q x = Some (enat t'')" "t = t'' - t'" "t' \<le> t''"
            "(\<forall>x t' t''. Mff x = Some (enat t') \<and> Q x = Some (enat t'') \<and> t' \<le> t'' \<longrightarrow> t \<le> t'' - t')"
        unfolding T'_SomeEnat_iff by auto

    

    then have "True" unfolding T'_def
      sorry
    have R: "T' (\<lambda>y. T' Q (f y)) M = Some (enat t)" sorry
    from L R show ?thesis by metis
  next
    case infinity
    with Some have "T' Q (bindT M f) = Some \<infinity>" by simp
    moreover
    with T'_inf have "T' (\<lambda>y. T' Q (f y)) M = Some \<infinity>" by blast
    ultimately show ?thesis by simp
  qed
qed 
term "Least S" 
 

lemma "T' Q (bindT M f) = T' (\<lambda>y. T' Q (f y)) M"
  unfolding T'_def apply auto
    apply (fo_rule arg_cong)
  apply (fo_rule arg_cong) apply (rule ext)
  apply(cases "M")
  subgoal unfolding mii_def by auto
  subgoal apply auto
   unfolding mii_def apply(auto)

  unfolding mii_def apply(cases "nofailT (bindT M f)") apply (auto simp: refine_pw_simps)
  unfolding nofailT_def apply (auto split: option.split nrest.split)
  oops


lemma "(SPECT [x\<mapsto>t] \<le> SPECT Q) \<longleftrightarrow> (\<exists>t'\<ge>t. Q x = Some t')"
  apply (auto simp: pw_le_iff refine_pw_simps)
  by (metis Suc_ile_eq le_less_linear less_irrefl not_infinity_eq option.sel zero_enat_def zero_le)  

lemma "(SPECT [x\<mapsto>t] \<le> SPECT Q) \<longleftrightarrow> Some t \<le> T' Q (RETURNT x)"
  unfolding T'_def RETURNT_def mii_def mm_def by (auto simp: le_fun_def le_Inf_iff split: option.splits)  
 

lemma "(SPECT [x\<mapsto>t] \<le> SPECT Q) \<longleftrightarrow> Some t \<le> T' Q (RETURNT x)"
  apply safe
  subgoal
    unfolding T'_def RETURNT_def
    unfolding mii_def mm_def
    by (auto simp: le_fun_def le_Inf_iff split: if_splits option.splits) 
  subgoal
    unfolding T'_def RETURNT_def mii_def mm_def
    by (auto simp: le_fun_def le_Inf_iff split: if_splits option.splits)
  done

lemma g: "(\<forall>x. (\<exists>xa. x = mm Q x2 xa) \<longrightarrow> Some 0 \<le> x)
        = (\<forall>x. Some 0 \<le> mm Q x2 x)" by auto

lemma "m \<le> SPECT Q \<longleftrightarrow> Some 0 \<le> T' Q m"
  apply safe
  subgoal unfolding T'_def
    apply(cases m) 
    subgoal by auto
    subgoal for mf 
      unfolding le_Inf_iff apply safe
      apply (auto simp: le_fun_def)
      subgoal for x
        apply(cases "mf x = None")
        subgoal 
          unfolding mii_def apply (auto split: option.split nrest.split)
          unfolding mm_def by (auto split: option.split nrest.split)
        subgoal 
          unfolding mii_def mm_def apply (auto split: option.split nrest.split)
          subgoal by (metis less_eq_option_Some_None)   
          subgoal by (metis leD less_eq_option_Some) 
          done
        done
      done
    done
  subgoal unfolding T'_def
    unfolding mii_def apply (auto simp: le_Inf_iff split: nrest.split if_splits option.splits )
    apply (cases m) apply auto unfolding g
    unfolding  mm_def apply (auto split:  if_splits option.splits ) 
    apply (simp only: le_fun_def) apply (auto split: option.splits if_splits)
    subgoal for mf x 
      apply(cases "Q x")
      subgoal apply(cases "mf x") apply auto by force  
      subgoal apply(cases "mf x") apply auto by force   
      done
    done
  done 
*)
lemma "T' Q (SPECT [x\<mapsto>t]) = G"
  unfolding T'_def mii_def mm_def apply(auto split: option.split nrest.split)
  oops




lemma bindT_complete:
  "m \<le> REST (\<lambda>y. Inf {mmm f Q x y |x. True})
     \<longleftrightarrow> bindT m f \<le> SPECT Q"
  apply (simp only: pw_le_iff) apply safe
  subgoal by auto
  subgoal by auto
  subgoal by (auto simp: refine_pw_simps None_mmm'  InfQ_iff )
  subgoal 
    apply (auto simp: refine_pw_simps   ) 
    sorry
  subgoal by auto
  subgoal by auto
  subgoal by (auto simp: refine_pw_simps None_mmm'  InfQ_iff ) 
  subgoal apply (auto simp: refine_pw_simps) sorry
  oops
(*
lemma bindT_refine:
  "m \<le> REST (\<lambda>y. Inf { case f y of FAILi \<Rightarrow> None
                              | REST F \<Rightarrow> (mm (Q::'a \<Rightarrow> enat option) F) x |x. True})
     \<Longrightarrow> bindT m f \<le> SPECT Q"
  apply(auto simp: pw_le_iff refine_pw_simps)  
  subgoal unfolding InfQ_iff nofailT_def by (auto split: option.split nrest.splits)
  subgoal for x r' t' t''  unfolding InfQ_iff apply(auto split: nrest.splits)
    
  proof(goal_cases)
    case 1
    from 1(1) have i: "\<And>x t. inresT m x t \<Longrightarrow>
          f x \<noteq> FAILT \<and>
          (\<forall>xa x2. f x = SPECT x2 \<longrightarrow> None \<noteq> mm Q x2 xa) \<and>
          enat t \<le> Inf (Option.these {uu. (f x = FAILT \<longrightarrow> uu = None) \<and> (\<exists>xa. \<forall>x2. f x = SPECT x2 \<longrightarrow> uu = mm Q x2 xa)})" by blast
    have q: "f r' \<noteq> FAILT" and
         r: " (\<forall>xa x2. f r' = SPECT x2 \<longrightarrow> None \<noteq> mm Q x2 xa)"
          and s: "enat t' \<le> Inf (Option.these {uu. (f r' = FAILT \<longrightarrow> uu = None) \<and> (\<exists>xa. \<forall>x2. f r' = SPECT x2 \<longrightarrow> uu = mm Q x2 xa)})"
      using i[OF 1(2)] by auto
    from q obtain R where fr: "f r' = SPECT R" by force
    with r have r':"\<And>x. mm Q R x \<noteq> None" by metis
    with r' have "\<And>x. Q x \<noteq> None \<and> R x \<noteq> None \<and> (\<exists>t1 t2. R x = Some t1 \<and> Q x = Some t2 \<and> mm Q R x = Some (t2-t1) \<and> t2\<ge>t1)" by auto
    let ?S = "(Option.these {uu. (f r' = FAILT \<longrightarrow> uu = None) \<and> (\<exists>xa. \<forall>x2. f r' = SPECT x2 \<longrightarrow> uu = mm Q x2 xa)})"
    
    have kl: "\<And>x. mm Q R x \<noteq> None \<Longrightarrow> Q x \<noteq> None \<and> R x \<noteq> None \<and> (\<exists>t1 t2. R x = Some t1 \<and> Q x = Some t2 \<and> mm Q R x = Some (t2-t1) \<and> t2\<ge>t1)"
      unfolding mm_def apply (auto split: option.splits )
    have k: "(Option.these {uu. (f r' = FAILT \<longrightarrow> uu = None) \<and> (\<exists>xa. \<forall>x2. f r' = SPECT x2 \<longrightarrow> uu = mm Q x2 xa)})
          = Option.these {mm Q R xa | xa. True}"
      using q fr by simp

    from s[unfolded k] have "\<And>q. q\<in>Option.these {mm Q R xa | xa. True} \<Longrightarrow> enat t' \<le> q"
      by (simp add: le_Inf_iff) 

    then have pff: "\<And>x t. mm Q R x = Some t \<Longrightarrow> enat t' \<le> t" apply (auto split: option.splits)
      by (metis (mono_tags) in_these_eq mem_Collect_eq) 

    from kl have "mm Q R x \<noteq> None \<Longrightarrow> Q x \<noteq> None \<and> R x \<noteq> None \<and> (\<exists>t1 t2. R x = Some t1 \<and> Q x = Some t2 \<and> mm Q R x = Some (t2-t1) \<and> t2\<ge>t1)"
      by auto  
    with r' obtain t1 t2 where "R x = Some t1" "Q x = Some t2" "mm Q R x = Some (t2-t1)" and leq: "t2\<ge>t1"
       by meson
    with pff have "enat t' \<le> (t2-t1)" by auto
    then have i: "enat t' + t1 \<le> t2" using leq apply(cases t2) apply auto apply(cases t1) by auto
    have ii: "t'' \<le> t1" using `R x = Some t1` fr 1(3) unfolding inresT_def by simp
    from i ii have "enat (t' + t'') \<le> t2"
      using add_mono by fastforce 

    show ?case apply(rule exI[where x=t2]) apply safe by fact+
  qed 
  done
*)



 
end