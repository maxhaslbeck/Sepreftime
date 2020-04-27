theory Remdups
  imports
    MoreCurrAutomation
 (* "../Refine_Imperative_HOL/Sepref"
    "../Refine_Imperative_HOL/IICF/Impl/IICF_Rbt_Set"  
    "../Refine_Imperative_HOL/IICF/Impl/IICF_DArray_List" 
    "NREST.RefineMonadicVCG"
    "../Refine_Foreach" *)
(*    "Imperative_HOL_Time.SLTC" *)
  "Automatic_Refinement.Autoref_Tagging"
    "Imperative_HOL_Time.IHT_Red_Black_Tree"
begin        


hide_const R B

term Autoref_Tagging.APP

definition "mop_empty_list t = SPECT [ [] \<mapsto> t ()]"
definition mop_set_empty where "mop_set_empty t = SPECT [ {} \<mapsto> t ()]"
definition mop_set_member where "mop_set_member t x S = SPECT [ x \<in> S \<mapsto> t (x,S)]"
definition mop_set_insert where "mop_set_insert t x S = SPECT [ insert x S \<mapsto> t (x,S)]"
definition "mop_push_list t x xs = SPECT [ xs @ [x] \<mapsto> t (x,xs)]"

definition "rd_inv as \<equiv> (\<lambda>(xs,ys,S). (\<exists>zs. as = zs@xs \<and> S = set ys \<and> distinct ys \<and> set zs = set ys))"

datatype RD_curr = RBT_search | RBT_insert | REST


instantiation RD_curr :: enum
begin
definition "enum_RD_curr = [RBT_search, RBT_insert, REST]"
definition "enum_all_RD_curr P = (P RBT_search \<and> P RBT_insert \<and> P REST)"
definition "enum_ex_RD_curr P = (P RBT_search \<or> P RBT_insert \<or> P REST)"
instance apply standard apply (auto simp: enum_RD_curr_def enum_ex_RD_curr_def enum_all_RD_curr_def)
  subgoal for x apply (cases x) by auto
  subgoal for P x apply (cases x) by auto  
  subgoal for P x apply (cases x) by auto  
  done
end


definition body_time :: "nat \<Rightarrow> (RD_curr \<Rightarrow> nat)" where                                           
  "body_time n = (\<lambda>_.0)(REST := 60, RBT_search := 1+rbt_search_time_logN (n+1), RBT_insert := rbt_insert_logN (n+1))"
definition body_time_abs :: "(RD_curr \<Rightarrow> nat)" where 
  "body_time_abs = (\<lambda>_.0)(REST := 60, RBT_search := 1, RBT_insert := 1)"

definition "rd_ta as = (\<lambda>(xs,ys,S). (\<lambda>x. length xs * body_time (length as) x) )"
definition "rd_ta_abs = (\<lambda>(xs,ys,S). (\<lambda>x. length xs * body_time_abs x) )"

definition rd_impl1 :: "('a::{linorder}) list \<Rightarrow> ('a list, _ ) nrest" where
"rd_impl1 as = do {
  ys \<leftarrow> mop_empty_list (\<lambda>_. (\<lambda>_.0)(REST:=enat 12));
  S \<leftarrow> mop_set_empty (\<lambda>_. (\<lambda>_.0)(REST:=1));
  zs \<leftarrow> RETURNT as;
  (zs,ys,S) \<leftarrow> whileIET (rd_inv as) (rd_ta_abs) (\<lambda>(xs,ys,S). length xs > 0) (\<lambda>(xs,ys,S). do {                          
    ASSERT (length xs > 0);
    ASSERT (length xs + length ys \<le> length as);
    ASSERT (card S \<le> length ys);
    x \<leftarrow> RETURNT (hd xs);
    xs \<leftarrow> RETURNT (tl xs);
    b \<leftarrow> mop_set_member (\<lambda>_. (\<lambda>_.0)(RBT_search:=1) ) x S;
    if b then
      RETURNT (xs,ys,S)
    else do {
      S \<leftarrow> mop_set_insert (\<lambda>_. (\<lambda>_.0)(RBT_insert:=1) ) x S;
      ys \<leftarrow> mop_push_list (\<lambda>_. (\<lambda>_.0)(REST:=  23) ) x ys;  
      RETURNT (xs,ys,S)
    } 
  }) (zs,ys,S);
  RETURNT ys
  }"
 
definition "remdups_time (n::nat) = (\<lambda>x. n * body_time n x ) + (\<lambda>_.0)(REST:=20)"
definition "remdups_time_abs (n::nat) = (\<lambda>x. n * body_time_abs x ) + (\<lambda>_.0)(REST:=20)"

definition "remdups_spec_abs as = SPECT (emb (\<lambda>ys. set as = set ys \<and> distinct ys)
                   ( remdups_time_abs (length as) ))"
definition "remdups_spec as = SPECT (emb (\<lambda>ys. set as = set ys \<and> distinct ys)
                   ( remdups_time (length as) ))"

fun RR where
  "RR n REST REST = 1"
| "RR n RBT_search RBT_search = 1+rbt_search_time_logN (n+1)"
| "RR n RBT_insert RBT_insert = rbt_insert_logN (n+1)"
| "RR n _ _  = 0" 


lemma timerefine_SPECT_conv: 
  "timerefine R (SPECT M) = SPECT (\<lambda>r. case M r of None \<Rightarrow> None |
                  Some cm \<Rightarrow> Some (\<lambda>cc. Sum_any (\<lambda>ac. cm ac * R ac cc)))"
  unfolding timerefine_def  by auto 

lemma timerefine_SPECT_emb': 
  "timerefine F (SPECT (emb' P TT)) = SPECT (emb' P (\<lambda>r cc. Sum_any (\<lambda>ac. TT r ac * F ac cc)))"
  unfolding timerefine_def  apply auto
  unfolding emb'_def apply(rule ext) by simp

lemma emb'_eqI: "P=P' \<Longrightarrow> X=X' \<Longrightarrow> emb' P X = emb' P' X'" unfolding emb'_def by auto
lemma "remdups_spec as = timerefine (RR (length as)) (remdups_spec_abs as)"
  unfolding remdups_spec_abs_def apply(simp only: timerefine_SPECT_emb')
  unfolding remdups_spec_def apply simp
  apply(rule emb'_eqI) apply simp
  apply(rule ext)+
  apply(auto simp: remdups_time_def remdups_time_abs_def body_time_def body_time_abs_def)
     apply (simp_all add: Sum_any_to_foldr enum_RD_curr_def)
  apply (auto split: RD_curr.splits)
  subgoal for x apply (cases x) by auto
  subgoal for x apply (cases x) by auto
  subgoal for x apply (cases x) by auto
  done
  

lemma finer: "remdups_spec as = timerefine (RR (length as)) (remdups_spec_abs as)"
  unfolding remdups_spec_def remdups_spec_abs_def timerefine_def
      remdups_time_def remdups_time_abs_def body_time_def body_time_abs_def
  apply auto apply(rule ext)
  unfolding emb'_def apply auto
  apply(rule ext) apply auto
  apply (simp only: Sum_any_to_foldr enum_RD_curr_def) apply simp
  apply (simp only: Sum_any_to_foldr enum_RD_curr_def) apply simp
  apply (simp only: Sum_any_to_foldr enum_RD_curr_def) apply simp
  apply (simp only: Sum_any_to_foldr enum_RD_curr_def) apply auto
  subgoal for r x apply (cases x) by auto
  subgoal for r x apply (cases x) by auto
  subgoal for r x apply (cases x) by auto
  done

lemma enat_neq_Z_iff[simp]: "enat x \<noteq> 0 \<longleftrightarrow> x\<noteq>0"
  by (auto simp: zero_enat_def)

lemma rd_impl1_correct: "rd_impl1 as \<le> remdups_spec_abs as"
  unfolding remdups_spec_abs_def
  unfolding rd_impl1_def mop_empty_list_def mop_set_empty_def
      mop_set_member_def mop_set_insert_def mop_push_list_def
      rd_ta_abs_def rd_inv_def
  apply(rule T_g_specifies_I)
  apply (vcg' \<open>simp\<close> )  
    unfolding Some_le_emb'_conv  
  supply [simp] = neq_Nil_conv distinct_length_le card_length
        apply (auto simp:
              Some_le_mm3_Some_conv numeral_eq_enat
          body_time_abs_def one_enat_def remdups_time_abs_def plus_enat_simps intro!: le_funI)
    subgoal  
      by (meson list.set_cases)  
    done




subsection \<open>do the overapproximation in the code, prove it during synthesis\<close>

definition rd_impl2 :: "('a::{linorder}) list \<Rightarrow> ('a list, _ ) nrest" where
"rd_impl2 as = do {
  ys \<leftarrow> mop_empty_list (\<lambda>_. (\<lambda>_.0)(REST:=enat 12));
  S \<leftarrow> mop_set_empty (\<lambda>_. (\<lambda>_.0)(REST:=1));
  zs \<leftarrow> RETURNT as;
  (zs,ys,S) \<leftarrow> whileIET (rd_inv as) (rd_ta_abs) (\<lambda>(xs,ys,S). length xs > 0) (\<lambda>(xs,ys,S). do {                          
    ASSERT (length xs > 0);
    ASSERT (length xs + length ys \<le> length as);
    ASSERT (card S \<le> length ys);
    x \<leftarrow> RETURNT (hd xs);
    xs \<leftarrow> RETURNT (tl xs);
    b \<leftarrow> mop_set_member (\<lambda>_. (\<lambda>_.0)(RBT_search:=1+rbt_search_time_logN (length as + 1)) ) x S;
    if b then
      RETURNT (xs,ys,S)
    else do {
      S \<leftarrow> mop_set_insert (\<lambda>_. (\<lambda>_.0)(RBT_insert:=rbt_insert_logN (length as + 1)) ) x S;
      ys \<leftarrow> mop_push_list (\<lambda>_. (\<lambda>_.0)(REST:=  23) ) x ys;  
      RETURNT (xs,ys,S)
    } 
  }) (zs,ys,S);
  RETURNT ys
  }"

lemma timerefine_RETURNT_conv: "timerefine R (RETURNT x) = RETURNT x"
  unfolding timerefine_def RETURNT_def apply auto apply(rule ext) by auto

lemma AA: "rd_impl2 as \<le> \<Down>Id (timerefine (RR (length as)) (rd_impl1 as))"
  unfolding rd_impl2_def rd_impl1_def
  apply(rule bindT_refine_g[where R'=Id])
  subgoal unfolding mop_empty_list_def timerefine_SPECT_conv
    by (auto intro!: le_funI simp: Sum_any_to_foldr enum_RD_curr_def) 
  subgoal
    apply(rule bindT_refine_g[where R'=Id])
    subgoal unfolding mop_set_empty_def timerefine_SPECT_conv
      by (auto intro!: le_funI simp: one_enat_def Sum_any_to_foldr enum_RD_curr_def) 
    subgoal 
      apply(rule bindT_refine_g[where R'=Id])
      subgoal by (simp add: timerefine_RETURNT_conv)
      subgoal 
        apply(rule bindT_refine_g[where R'=Id])
        subgoal 
          unfolding whileIET_def  
          apply(rule WHILET_refine)
          subgoal by simp
          subgoal by simp
          subgoal  
            apply(rule Case_prod_refine[of _ _ Id Id]) apply simp
            apply(rule Case_prod_refine[of _ _ Id Id]) apply simp
            apply(rule le_ASSERTI_g2)+ 
            apply(rule ASSERT_leI2) apply simp
            apply(rule ASSERT_leI2) apply simp
            apply(rule ASSERT_leI2) apply simp
            apply(rule bindT_refine_g[where R'=Id]) 
            subgoal by (simp add: timerefine_RETURNT_conv)
            subgoal 
              apply(rule bindT_refine_g[where R'=Id]) 
              subgoal by (simp add: timerefine_RETURNT_conv)
              subgoal 
                apply(rule bindT_refine_g[where R'=Id]) 
                subgoal unfolding mop_set_member_def timerefine_SPECT_conv
                  by (auto intro!: le_funI simp: Sum_any_to_foldr enum_RD_curr_def) 
                subgoal 
                  apply(rule If_refine)
                  subgoal by simp
                  subgoal by (simp add: timerefine_RETURNT_conv)
                  subgoal 
                    apply(rule bindT_refine_g[where R'=Id]) 
                    subgoal  unfolding mop_set_insert_def timerefine_SPECT_conv
                      by (auto intro!: le_funI simp: Sum_any_to_foldr enum_RD_curr_def) 
                    subgoal 
                      apply(rule bindT_refine_g[where R'=Id]) 
                      subgoal unfolding mop_push_list_def timerefine_SPECT_conv
                        by (auto intro!: le_funI simp: Sum_any_to_foldr numeral_eq_enat enum_RD_curr_def) 
                      subgoal  by (simp add: timerefine_RETURNT_conv)
                      done
                    done
                  done
                done
              done
            done
          done
        subgoal 
          apply simp apply(rule case_prod_refine_g)
           apply(rule case_prod_refine_g)
          by (simp add: timerefine_RETURNT_conv)
        done
      done
    done
  done


thm rd_impl1_correct AA finer

lemma "rd_impl2 as \<le> remdups_spec as"
proof -   
  have "rd_impl2 as \<le> \<Down>Id (timerefine (RR (length as)) (rd_impl1 as))"
    by (fact AA)
  also have "\<dots> \<le> \<Down>Id (timerefine (RR (length as)) (remdups_spec_abs as))"
    apply(rule nrest_Rel_mono)
    apply(rule timerefine_mono)
    subgoal sorry
    subgoal by(fact rd_impl1_correct)
    done
  also have "\<dots> = remdups_spec as"
    apply(fold finer) apply simp done
  finally show ?thesis .
qed



subsection \<open>dont to the overapproximation in the code, do it in the proof\<close>


definition rd_impl3 :: "('a::{linorder}) list \<Rightarrow> ('a list, _ ) nrest" where
"rd_impl3 as = do {
  ys \<leftarrow> mop_empty_list (\<lambda>_. (\<lambda>_.0)(():=enat 12));
  S \<leftarrow> mop_set_empty (\<lambda>_. (\<lambda>_.0)(():=1));
  zs \<leftarrow> RETURNT as;
  (zs,ys,S) \<leftarrow> whileT (\<lambda>(xs,ys,S). length xs > 0) (\<lambda>(xs,ys,S). do {        
    ASSERT (length xs > 0);
    x \<leftarrow> RETURNT (hd xs);
    xs \<leftarrow> RETURNT (tl xs);
    ASSERT (card S \<le> length as);
    b \<leftarrow> mop_set_member (\<lambda>(x,S). (\<lambda>_.0)(():= 1 + rbt_search_time_logN (card S + 1)) ) x S;
    if b then
      RETURNT (xs,ys,S)    
    else do {
      ASSERT (card S \<le> length as);
      S \<leftarrow> mop_set_insert (\<lambda>(x,S). (\<lambda>_.0)(() := rbt_insert_logN (card S + 1)) ) x S;
      ys \<leftarrow> mop_push_list (\<lambda>_. (\<lambda>_.0)(():=  23) ) x ys;  
      RETURNT (xs,ys,S)
    } 
  }) (zs,ys,S);
  RETURNT ys
  }"


fun RR2 where
  "RR2 n REST () = 1"
| "RR2 n RBT_search () = 1+rbt_search_time_logN (n+1)"
| "RR2 n RBT_insert () = rbt_insert_logN (n+1)" 



lemma BB: "rd_impl3 as \<le> \<Down>Id (timerefine (RR2 (length as)) (rd_impl1 as))"
  unfolding rd_impl3_def rd_impl1_def
  apply(rule bindT_refine_g[where R'=Id])
  subgoal unfolding mop_empty_list_def timerefine_SPECT_conv
    by (auto intro!: le_funI simp: Sum_any_to_foldr enum_RD_curr_def) 
  subgoal
    apply(rule bindT_refine_g[where R'=Id])
    subgoal unfolding mop_set_empty_def timerefine_SPECT_conv
      by (auto intro!: le_funI simp: one_enat_def Sum_any_to_foldr enum_RD_curr_def) 
    subgoal 
      apply(rule bindT_refine_g[where R'=Id])
      subgoal by (simp add: timerefine_RETURNT_conv)
      subgoal 
        apply(rule bindT_refine_g[where R'=Id])
        subgoal 
          unfolding whileIET_def  
          apply(rule WHILET_refine)
          subgoal by simp
          subgoal by simp
          subgoal  
            apply(rule Case_prod_refine[of _ _ Id Id]) apply simp
            apply(rule Case_prod_refine[of _ _ Id Id]) apply simp
            apply(rule le_ASSERTI_g2)+ 
            apply(rule ASSERT_leI2) apply simp
            apply(rule bindT_refine_g[where R'=Id]) 
            subgoal by (simp add: timerefine_RETURNT_conv)
            subgoal 
              apply(rule bindT_refine_g[where R'=Id]) 
              subgoal by (simp add: timerefine_RETURNT_conv)
              subgoal 
                apply(rule ASSERT_leI2) apply simp
                apply(rule bindT_refine_g[where R'=Id]) 
                subgoal unfolding mop_set_member_def timerefine_SPECT_conv 
                  by (auto intro!: le_funI  rbt_search_time_logN_mono simp:  Sum_any_to_foldr enum_RD_curr_def)
                subgoal 
                  apply(rule If_refine)
                  subgoal by simp
                  subgoal by (simp add: timerefine_RETURNT_conv)
                  subgoal 
                    apply(rule ASSERT_leI2) apply simp
                    apply(rule bindT_refine_g[where R'=Id]) 
                    subgoal  unfolding mop_set_insert_def timerefine_SPECT_conv
                      by (auto intro!: le_funI rbt_insert_logN_mono  simp: Sum_any_to_foldr enum_RD_curr_def) 
                    subgoal 
                      apply(rule bindT_refine_g[where R'=Id]) 
                      subgoal unfolding mop_push_list_def timerefine_SPECT_conv
                        by (auto intro!: le_funI simp: Sum_any_to_foldr numeral_eq_enat enum_RD_curr_def) 
                      subgoal  by (simp add: timerefine_RETURNT_conv)
                      done
                    done
                  done
                done
              done
            done
          done
        subgoal 
          apply simp apply(rule case_prod_refine_g)
           apply(rule case_prod_refine_g)
          by (simp add: timerefine_RETURNT_conv)
        done
      done
    done
  done

definition "TT_time n = 61 * n +
               (20 + (n * rbt_insert_logN (Suc (n))
                   + n * rbt_search_time_logN (Suc n)))"

lemma TT: "timerefine (RR2 (length as)) (remdups_spec_abs as) =
    SPECT
     (emb (\<lambda>ys. set as = set ys \<and> distinct ys)
       (\<lambda>cc. enat
              (TT_time (length as))))"
  unfolding remdups_spec_abs_def remdups_time_abs_def body_time_abs_def
  apply(subst timerefine_SPECT_emb')
  by(simp add: TT_time_def Sum_any_to_foldr numeral_eq_enat enum_RD_curr_def) 
  
lemma rd_impl3_correct: "rd_impl3 as \<le> SPECT (emb (\<lambda>ys. set as = set ys \<and> distinct ys)
                   ( \<lambda>_. TT_time (length as) ))" (is "?L \<le> ?R")
proof -   
  term ?R
  have "rd_impl3 as \<le> \<Down>Id (timerefine (RR2 (length as)) (rd_impl1 as))"
    by (fact BB)
  also have "\<dots> \<le> \<Down>Id (timerefine (RR2 (length as)) (remdups_spec_abs as))"
    apply(rule nrest_Rel_mono)
    apply(rule timerefine_mono)
    subgoal sorry
    subgoal by(fact rd_impl1_correct)
    done
  also have "\<dots> = SPECT (emb (\<lambda>ys. set as = set ys \<and> distinct ys)
                   ( \<lambda>_. TT_time (length as) ))"
     unfolding TT by simp 
  finally show ?thesis .
qed

(*
lemma remdups_time_nln[asym_bound]: "remdups_time \<in> \<Theta>(\<lambda>n. n * ln n)"
  unfolding remdups_time_def body_time_def
  by auto2 
*)


(*
section \<open>HNR\<close>

type_synonym IHT_curr = unit

definition hn_refine :: "assn \<Rightarrow> 'a Heap \<Rightarrow> assn \<Rightarrow> ('b \<Rightarrow> 'a \<Rightarrow> assn) \<Rightarrow> ('b, _) nrest \<Rightarrow> bool"
  where  "hn_refine \<Gamma> c \<Gamma>' R m \<equiv> nofailT m \<longrightarrow> 
    (\<forall>h as  n   M. pHeap h as n \<Turnstile> \<Gamma>  \<longrightarrow> m = SPECT M \<longrightarrow>
    (\<exists>h' t r. execute c h = Some (r, h', t) \<and>    
       (\<exists>ra (Ca::nat). M ra \<ge> Some (\<lambda>_. enat Ca)  \<and> n+Ca\<ge>t
           \<and> pHeap h' (new_addrs h as h') ((n+Ca)-t) \<Turnstile> \<Gamma>' * R ra r * true
          )
       \<and> relH {a . a < Heap.lim h \<and> a \<notin> as} h h' \<and> Heap.lim h \<le> Heap.lim h'))" 


lemma extract_cost_ub:
  assumes "hn_refine \<Gamma> c \<Gamma>' R (SPECT M)" "(\<And>c. c\<in>ran M \<Longrightarrow> c () \<le> Cost_ub)"
  shows "<\<Gamma> * timeCredit_assn Cost_ub> c <\<lambda>r. \<Gamma>' * (\<exists>\<^sub>Ara. R ra r * \<up>(ra \<in> dom M)) >\<^sub>t"
  using assms(1)  unfolding hn_refine_def
  unfolding hoare_triple_def 
  apply clarify
proof (goal_cases)
  case (1 h as \<sigma> r n t)
  from 1(2) have 2: "pHeap h as (n-Cost_ub) \<Turnstile> \<Gamma>" and  nf: "n\<ge>Cost_ub"
    using mod_timeCredit_dest by auto

  from 1(1) have 3: "\<And>h as n Ma.
       pHeap h as n \<Turnstile> \<Gamma> \<Longrightarrow> 
      SPECT M = SPECT Ma \<Longrightarrow> (\<exists>h' t r. execute c h = Some (r, h', t) \<and>      
       (\<exists>ra Ca. Ma ra \<ge> Some (\<lambda>_. enat Ca) \<and> t \<le> n + Ca \<and> pHeap h' (new_addrs h as h') ((n + Ca) - t) \<Turnstile> \<Gamma>' * R ra r * true) \<and>
      relH {a. a < heap.lim h \<and> a \<notin> as} h h' \<and> heap.lim h \<le> heap.lim h')" 
    by auto

  thm effect_deterministic

  from 3[OF 2 ] obtain h' t' r' where E: "execute c h = Some (r', h', t') " and
    R:  "(\<exists>ra Ca. M ra \<ge> Some (\<lambda>_. enat Ca) \<and>
                    pHeap h' (new_addrs h as h') (n - Cost_ub + Ca - t') \<Turnstile> \<Gamma>' * R ra r' * true \<and> t' \<le> n - Cost_ub + Ca) \<and>
           relH {a. a < heap.lim h \<and> a \<notin> as} h h' \<and> heap.lim h \<le> heap.lim h'" by blast

  have F: "\<sigma> = Some h'" and prime: "r' = r" "t' = t"  
    using E 1(3) run.cases apply force
    using E 1(3) run.cases apply force
    using E 1(3) run.cases by force 
  then have sig: "the \<sigma> = h'" by auto
  from R  have
    B: "(\<exists>ra Ca. M ra \<ge> Some (\<lambda>_. enat Ca) \<and>
     pHeap (the \<sigma>) (new_addrs h as (the \<sigma>)) (n - Cost_ub + Ca - t) \<Turnstile> \<Gamma>' * R ra r * true \<and>
        t \<le> n - Cost_ub + Ca )" and C:
    "relH {a. a < heap.lim h \<and> a \<notin> as} h (the \<sigma>)" "heap.lim h \<le> heap.lim (the \<sigma>) " 
    unfolding prime sig by auto



  from B obtain ra Ca where i: "pHeap (the \<sigma>) (new_addrs h as (the \<sigma>)) (n - Cost_ub + Ca - t) \<Turnstile> \<Gamma>' * R ra r * true"
    and ii:  "t \<le> n - Cost_ub + Ca"  and ineq: "M ra \<ge> Some (\<lambda>_. enat Ca)"
    using B by auto

  from ineq have radom: "ra \<in> dom M" using domIff by fastforce  
  then obtain Mra where Mra: "M ra = Some Mra" by blast
  with assms(2) have *: "Mra () \<le> enat Cost_ub" by (meson ranI)
  {
    have " Some (\<lambda>_. enat Ca) \<le> M ra" by (fact ineq)
    also have "\<dots> = Some Mra" using Mra by simp
    also have "\<dots> \<le> Some (\<lambda>_. enat Cost_ub)" apply simp apply(rule le_funI) using * by simp
    finally have "Some (\<lambda>_::unit. enat Ca) \<le> Some (\<lambda>_. enat Cost_ub)" .
    then have "Ca \<le> Cost_ub" by (auto simp: le_fun_def)
  } note ie=this

  have pr: "(n - Cost_ub + Ca - t) = (n - t) - (Cost_ub - Ca)" using ie ii nf by auto
  have pl: "(n - (t + (Cost_ub - Ca)) + (Cost_ub - Ca)) = n-t" using ii nf by auto

  have "pHeap (the \<sigma>) (new_addrs h as (the \<sigma>) \<union> {}) ((n - t) - (Cost_ub - Ca) + (Cost_ub - Ca)) \<Turnstile> \<Gamma>' * R ra r * true * true"
    apply(rule mod_star_convI)  apply simp
     apply(rule i[unfolded pr])  by (simp add: top_assn_rule)

  then have H: "pHeap (the \<sigma>) (new_addrs h as (the \<sigma>)) (n - t) \<Turnstile> \<Gamma>' * R ra r * true * true"
    by (simp add: pl)   

  have "pHeap (the \<sigma>) (new_addrs h as (the \<sigma>)) (n - t) \<Turnstile> \<Gamma>' * R ra r * \<up> (ra \<in> dom M) * true"
    apply(rule entailsD[OF _ H]) using radom by auto2  
  then have "\<exists>ra. pHeap (the \<sigma>) (new_addrs h as (the \<sigma>)) (n - t) \<Turnstile> \<Gamma>' * R ra r * \<up> (ra \<in> dom M) * true"
    by blast
  then have H': "pHeap (the \<sigma>) (new_addrs h as (the \<sigma>)) (n - t) \<Turnstile> (\<exists>\<^sub>Ara. \<Gamma>' *  R ra r * \<up> (ra \<in> dom M) * true)"
    using mod_ex_dist by blast
  have H: "pHeap (the \<sigma>) (new_addrs h as (the \<sigma>)) (n - t) \<Turnstile> \<Gamma>' * (\<exists>\<^sub>Ara. R ra r * \<up> (ra \<in> dom M)) * true" 
    apply(rule entailsD[OF _ H']) by auto2

  from ii ie nf have T: "t \<le> n " by auto

  show ?case
    apply safe
    subgoal using F by auto
    subgoal using H by simp  
    subgoal by fact
     apply fact apply fact done
qed 

*)

end