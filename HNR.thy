theory HNR                    
imports Sepreftime "SepLogicTime_RBTreeBasic.SepAuto" (* Refine_Monadic.RefineG_Recursion *)
  SepLogic_Misc  
  "Refine_Imperative_HOL/Lib/Structured_Apply"
begin


section "hn_refine"

definition "\<And>T. hn_refine \<Gamma> c \<Gamma>' R m \<equiv> nofailT m \<longrightarrow> 
    (\<forall>h as  n   M. pHeap h as n \<Turnstile> \<Gamma>  \<longrightarrow> m = REST M \<longrightarrow>
    (\<exists>h' t r. execute c h = Some (r, h', t) \<and>
       (\<exists>ra Ca. M ra \<ge> Some Ca  \<and> n+Ca\<ge>t
           \<and> pHeap h' (new_addrs h as h') ((n+Ca)-t) \<Turnstile> \<Gamma>' * R ra r * true
          )
       \<and> relH {a . a < lim h \<and> a \<notin> as} h h' \<and> lim h \<le> lim h'))"    

subsection "easy rules"

lemma hnr_FAILT[simp]: "hn_refine \<Gamma> c \<Gamma>' R FAILT"
  by(simp add: hn_refine_def)

subsection "Refine hnr"


lemma assumes "m \<le> m'" 
    "hn_refine \<Gamma> c \<Gamma>' R m"  
shows hnr_refine: "hn_refine \<Gamma> c \<Gamma>' R m'"
proof (cases m)
  case FAILi
  then show ?thesis using assms(1) by (auto simp:  hn_refine_def)
next
  case (REST x2)
  with assms(2)[unfolded hn_refine_def] have
      E: "(\<And>h as n M. pHeap h as n \<Turnstile> \<Gamma> \<Longrightarrow>
                m = SPECT M \<Longrightarrow>
                (\<exists>h' t r. execute c h = Some (r, h', t) \<and>
                          (\<exists>ra Ca. Some (enat Ca) \<le> M ra \<and> t \<le> n + Ca \<and> pHeap h' (new_addrs h as h') (n + Ca - t) \<Turnstile> \<Gamma>' * R ra r * true) \<and>
                          relH {a. a < heap.lim h \<and> a \<notin> as} h h' \<and> heap.lim h \<le> heap.lim h'))"
    by auto
  show ?thesis unfolding hn_refine_def 
  proof (clarsimp)
    fix h as n M'
    assume M': "m' = SPECT M'"
    with assms(1) obtain M where M: "m = SPECT M"
      by fastforce
  
    assume 2:  "pHeap h as n \<Turnstile> \<Gamma>"
    from E[OF 2 M] obtain h' t r ra Ca where 
          ineq:  "Some (enat Ca) \<le> M ra"  and 
          r: "execute c h = Some (r, h', t)" "t \<le> n + Ca"
             "pHeap h' (new_addrs h as h') (n + Ca - t) \<Turnstile> \<Gamma>' * R ra r * true " 
             "relH {a. a < heap.lim h \<and> a \<notin> as} h h'" "heap.lim h \<le> heap.lim h'"
      by blast

    from assms(1) M' M have  "M \<le> M'" by simp
    with ineq have ineq': "Some (enat Ca) \<le> M' ra" 
      using dual_order.trans by(auto simp: le_fun_def) 

    from r ineq'
    show "\<exists>h' t r. execute c h = Some (r, h', t) \<and>
                         (\<exists>ra Ca. Some (enat Ca) \<le> M' ra \<and> t \<le> n + Ca \<and> pHeap h' (new_addrs h as h') (n + Ca - t) \<Turnstile> \<Gamma>' * R ra r * true) \<and> relH {a. a < heap.lim h \<and> a \<notin> as} h h' \<and> heap.lim h \<le> heap.lim h'"
      by blast
  qed
qed 

subsection "Frame rule"

lemma hnr_frame:
  assumes "hn_refine P' c Q' R m"
  assumes "P \<Longrightarrow>\<^sub>t F * P'"
  shows "hn_refine P c (F * Q') R m"
  using assms(2)
  unfolding hn_refine_def entailst_def
proof clarsimp
  fix h as n M
  assume "P \<Longrightarrow>\<^sub>A F * P' * true" "pHeap h as n \<Turnstile> P"
  then have "pHeap h as n \<Turnstile> F * P' * true" by(rule entailsD)
  then have H: "pHeap h as n \<Turnstile> P' * (F * true)" 
    by (simp add: mult.assoc mult.left_commute)


  with assms(1)[unfolded hn_refine_def] have D1: "(\<And>h as n M. pHeap h as n \<Turnstile> P' \<Longrightarrow>
                m = SPECT M \<Longrightarrow>
                (\<exists>h' t r. execute c h = Some (r, h', t) \<and>
                          (\<exists>ra Ca. Some (enat Ca) \<le> M ra \<and> t \<le> n + Ca \<and> pHeap h' (new_addrs h as h') (n + Ca - t) \<Turnstile> Q' * R ra r * true) \<and>
                          relH {a. a < heap.lim h \<and> a \<notin> as} h h' \<and> heap.lim h \<le> heap.lim h'))"
    by auto 

  from mod_star_convE[OF H]   obtain as1 as2 n1 n2 where  uni: "as = as1 \<union> as2"
    and a: "as1 \<inter> as2 = {}" and  n: "n = n1 + n2"
    and pH1: "pHeap h as1 n1 \<Turnstile> P'"
    and Fr': "pHeap h as2 n2 \<Turnstile> F * true"  by blast 

  assume m: "m = SPECT M"

  from D1[OF pH1 m]  obtain h' t r ra Ca where
         1: "execute c h = Some (r, h', t)" "Some (enat Ca) \<le> M ra" and 2: "t \<le> n1 + Ca"
       and 3:                   "pHeap h' (new_addrs h as1 h') (n1 + Ca - t) \<Turnstile> Q' * R ra r * true"
       and 4:                   "relH {a. a < heap.lim h \<and> a \<notin> as1} h h'" and 5: "heap.lim h \<le> heap.lim h'"
    by blast

  have Fr: "pHeap h' as2 n2 \<Turnstile> F * true"
    apply(rule mod_relH[OF _ Fr'])
    apply(rule relH_subset) apply fact  
    using Fr' a models_in_range by fastforce 

  have na: "new_addrs h as1 h' \<inter> as2 = {}" 
    using a models_in_range[OF Fr'] 4
    by (auto simp: new_addrs_def)

  have n': "n1 + Ca - t + n2 = n + Ca - t" using n 2 by auto
  have ne: "new_addrs h as1 h' \<union> as2 = new_addrs h as h'"
    using uni new_addrs_def by auto 

  thm mod_star_convI
  have "pHeap h' (new_addrs h as1 h' \<union> as2) (n1 + Ca - t + n2) \<Turnstile> (Q' * R ra r * true) * (F * true)" 
    by(rule mod_star_convI[OF na 3 Fr])  
  then have "pHeap h' (new_addrs h as h') (n + Ca - t) \<Turnstile> (Q' * R ra r * true) * (F * true)"
    by(simp only: n' ne)
  then have 31: "pHeap h' (new_addrs h as h') (n + Ca - t) \<Turnstile> F * Q' * R ra r * true"
    apply(rule entailsD[rotated]) 
    by (simp add: assn_times_assoc entails_def mult.left_commute top_assn_reduce)   
    
  have 41: "relH {a. a < heap.lim h \<and> a \<notin> as} h h'"
    apply(rule relH_subset) apply fact
    using uni by blast
  
  have 21: "t \<le> n + Ca" using 2 n by auto 

  from 1 21 31 41 5 show " \<exists>h' t r. execute c h = Some (r, h', t) \<and>
                         (\<exists>ra Ca. Some (enat Ca) \<le> M ra \<and> t \<le> n + Ca \<and> pHeap h' (new_addrs h as h') (n + Ca - t) \<Turnstile> F * Q' * R ra r * true) \<and>
                         relH {a. a < heap.lim h \<and> a \<notin> as} h h' \<and> heap.lim h \<le> heap.lim h'"
    by auto
qed

subsection "Consequence rules"



lemma hn_refine_cons':
  assumes I: "P\<Longrightarrow>\<^sub>AP' * true"
  assumes R: "hn_refine P' c Q R m"
  assumes I': "Q\<Longrightarrow>\<^sub>A Q' * true"
  assumes R': "\<And>x y. R x y \<Longrightarrow>\<^sub>A R' x y * true"
  shows "hn_refine P c Q' R' m"
proof -
  have "hn_refine P c Q R m" 
    apply(rule hnr_frame[OF R, where F=emp,simplified])
    unfolding entailst_def by fact

  then have R2: "(\<And>h as n M. nofailT (SPECT M) \<Longrightarrow>
   pHeap h as n \<Turnstile> P \<Longrightarrow>
              m = SPECT M \<Longrightarrow>
              (\<exists>h' t r. execute c h = Some (r, h', t) \<and>
                        (\<exists>ra Ca. Some (enat Ca) \<le> M ra \<and> t \<le> n + Ca \<and> pHeap h' (new_addrs h as h') (n + Ca - t) \<Turnstile> Q * R ra r * true) \<and>
                        relH {a. a < heap.lim h \<and> a \<notin> as} h h' \<and> heap.lim h \<le> heap.lim h'))" unfolding hn_refine_def by auto

  show ?thesis unfolding hn_refine_def
  proof (safe,goal_cases)
    case (1 h as n M) 
    from R2[OF 1] obtain h' t r ra Ca where a: "execute c h = Some (r, h', t)"
          "Some (enat Ca) \<le> M ra" "t \<le> n + Ca" 
          "relH {a. a < heap.lim h \<and> a \<notin> as} h h'" "heap.lim h \<le> heap.lim h'"
       and b: "pHeap h' (new_addrs h as h') (n + Ca - t) \<Turnstile> Q * R ra r * true" by blast
    have b': "pHeap h' (new_addrs h as h') (n + Ca - t) \<Turnstile> Q' * R' ra r * true"
      apply(rule entailsD[OF _b])
      using I' R' 
      by (smt assn_times_assoc ent_star_mono ent_true_drop(1) merge_true_star mult.left_commute)

    from a b' show ?case by blast
  qed
qed 


lemma hn_refine_cons_pre':
  assumes I: "P\<Longrightarrow>\<^sub>AP' * true"
  assumes R: "hn_refine P' c Q R m"
  shows "hn_refine P c Q R m"
  apply(rule hn_refine_cons'[OF I R])  
    by (auto simp add: entt_refl')   

lemma hn_refine_preI: 
  assumes "\<And>h. h\<Turnstile>\<Gamma> \<Longrightarrow> hn_refine \<Gamma> c \<Gamma>' R a"
  shows "hn_refine \<Gamma> c \<Gamma>' R a"
  using assms unfolding hn_refine_def   
  by blast 

lemma hn_refine_cons:
  assumes I: "P\<Longrightarrow>\<^sub>tP'"
  assumes R: "hn_refine P' c Q R m"
  assumes I': "Q\<Longrightarrow>\<^sub>t Q'"
  assumes R': "\<And>x y. R x y \<Longrightarrow>\<^sub>t R' x y"
  shows "hn_refine P c Q' R' m"
  by(rule hn_refine_cons'[OF assms[unfolded entailst_def]])

lemma hn_refine_cons_post':
  assumes R: "hn_refine P c Q R m"
  assumes I: "Q\<Longrightarrow>\<^sub>AQ'*true"
  shows "hn_refine P c Q' R m"
  using assms
  by (rule hn_refine_cons'[OF entt_refl' _ _ entt_refl'])

lemma hn_refine_cons_post:
  assumes R: "hn_refine P c Q R m"
  assumes I: "Q\<Longrightarrow>\<^sub>tQ'"
  shows "hn_refine P c Q' R m"
  using assms
  by (rule hn_refine_cons[OF entt_refl _ _ entt_refl])

lemma hn_refine_split_post:
  assumes "hn_refine \<Gamma> c \<Gamma>' R a"
  shows "hn_refine \<Gamma> c (\<Gamma>' \<or>\<^sub>A \<Gamma>'') R a"
  apply (rule hn_refine_cons_post[OF assms])
  by (rule entt_disjI1_direct)


lemma hn_refine_post_other: 
  assumes "hn_refine \<Gamma> c \<Gamma>'' R a"
  shows "hn_refine \<Gamma> c (\<Gamma>' \<or>\<^sub>A \<Gamma>'') R a"
  apply (rule hn_refine_cons_post[OF assms])
  by (rule entt_disjI2_direct)


lemma hn_refine_cons_pre:
  assumes I: "P\<Longrightarrow>\<^sub>tP'"
  assumes R: "hn_refine P' c Q R m"
  shows "hn_refine P c Q R m"
  by(rule hn_refine_cons_pre'[OF assms[unfolded entailst_def]])
   

definition hn_ctxt :: "('a\<Rightarrow>'c\<Rightarrow>assn) \<Rightarrow> 'a \<Rightarrow> 'c \<Rightarrow> assn" 
  -- {* Tag for refinement assertion *}
  where
  "\<And>P. hn_ctxt P a c \<equiv> P a c"



definition pure :: "('b \<times> 'a) set \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> assn"
  -- {* Pure binding, not involving the heap *}
  where "pure R \<equiv> (\<lambda>a c. \<up>((c,a)\<in>R))"


abbreviation "hn_val R \<equiv> hn_ctxt (pure R)"

lemma pure_app_eq: "pure R a c = \<up>((c,a)\<in>R)" by (auto simp: pure_def)

lemma pure_eq_conv[simp]: "pure R = pure R' \<longleftrightarrow> R=R'"
  unfolding pure_def 
  apply (rule iffI)
  apply safe
  apply (meson pure_assn_eq_conv)
  apply (meson pure_assn_eq_conv)
  done

lemma pure_rel_eq_false_iff: "pure R x y = false \<longleftrightarrow> (y,x)\<notin>R"
  by (auto simp: pure_def)

definition "invalid_assn R x y \<equiv> \<up>(\<exists>h. h\<Turnstile>R x y) * true"

abbreviation "hn_invalid R \<equiv> hn_ctxt (invalid_assn R)"

lemma move_back_pure: "\<And>B P. \<up>B * P = P * \<up>B"  
    by (simp add: assn_times_comm)  
lemma move_back_pure': "\<And>Q B P. Q * \<up>B * P = Q * P * \<up>B"   
    using assn_times_assoc assn_times_comm by auto  
lemma consume_true: "\<And>R. true * R   * true = R   * true"  
    by (metis mult.assoc mult.left_commute top_assn_reduce)

lemmas move = move_back_pure move_back_pure' consume_true


lemma invalidate_clone': "R x y \<Longrightarrow>\<^sub>A invalid_assn R x y * R x y * true" 
    apply (rule entailsI)
    unfolding invalid_assn_def apply(simp add: move)
    apply (auto simp: mod_star_trueI)
    done
 
  

subsection \<open>Return\<close>

lemma hnr_RETURN_pass:
  "hn_refine (hn_ctxt R x p) (return p) (hn_invalid R x p) R (REST [x\<mapsto>1])"
  -- \<open>Pass on a value from the heap as return value\<close>
  unfolding hn_refine_def 
  apply (auto simp: hn_ctxt_def)
  subgoal for h as n
    using execute_return'[of p h] apply auto
    subgoal  apply(rule exI[where x=1]) apply (simp add: one_enat_def) 
      apply(rule entailsD)  by(auto  simp: invalidate_clone')   
    subgoal by(simp add:  relH_def)  done
  done


lemma hnr_RETURN_pure:
  assumes "(c,a)\<in>R"
  shows "hn_refine emp (return c) emp (pure R) (REST [a\<mapsto>1])"
  -- \<open>Return pure value\<close>
  unfolding hn_refine_def 
  apply (auto simp: hn_ctxt_def)
  subgoal for h as n
    using execute_return'[of c h] apply auto
    subgoal  apply(rule exI[where x=1]) apply (simp add: one_enat_def pure_def)  
      apply(simp add: move assms)  
      using entailsD entails_true by blast   
    subgoal by(simp add:  relH_def)  done
  done

section "assert"


definition "iASSERT ret \<Phi> \<equiv> if \<Phi> then ret () else top"

definition ASSERT where "ASSERT \<equiv> iASSERT RETURNT"

lemma ASSERT_True[simp]: "ASSERT True = RETURNT ()" 
  by (auto simp: ASSERT_def iASSERT_def)
lemma ASSERT_False[simp]: "ASSERT False = FAILT" 
  by (auto simp: ASSERT_def iASSERT_def) 


lemma bind_ASSERT_eq_if: "do { ASSERT \<Phi>; m } = (if \<Phi> then m else FAILT)"
  unfolding ASSERT_def iASSERT_def by simp


lemma hnr_ASSERT:
  assumes "\<Phi> \<Longrightarrow> hn_refine \<Gamma> c \<Gamma>' R c'"
  shows "hn_refine \<Gamma> c \<Gamma>' R (do { ASSERT \<Phi>; c'})"
  using assms
  apply (cases \<Phi>)
  by(auto simp add: bind_ASSERT_eq_if) 

section "ureturn"

lemma hnr_uRETURN_pure:
  assumes "(c,a)\<in>R"
  shows "hn_refine emp (ureturn c) emp (pure R) (RETURNT a)"
  -- \<open>Return pure value\<close>
  unfolding hn_refine_def 
  apply (auto simp: hn_ctxt_def)
  subgoal for h as n
    using execute_ureturn'[of c h] apply auto
    subgoal  apply(rule exI[where x=0]) apply (simp add: zero_enat_def pure_def)  
      apply(simp add: move assms)  
      using entailsD entails_true by blast   
    subgoal by(simp add:  relH_def)  done
  done

lemma hnr_uRETURN_pass:
  "hn_refine (hn_ctxt R x p) (ureturn p) (hn_invalid R x p) R (RETURNT x)"
  -- \<open>Pass on a value from the heap as return value\<close>
  unfolding hn_refine_def 
  apply (auto simp: hn_ctxt_def)
  subgoal for h as n
    using execute_ureturn'[of p h] apply auto
    subgoal  apply(rule exI[where x=0]) apply (simp add: zero_enat_def) 
      apply(rule entailsD)  by(auto  simp: invalidate_clone')   
    subgoal by(simp add:  relH_def)  done
  done







subsubsection \<open>bind\<close>


lemma hnr_bind:
  assumes D1: "hn_refine \<Gamma> m' \<Gamma>1 Rh m"
  assumes D2: 
    "\<And>x x'. RETURNT x \<le> m \<Longrightarrow> hn_refine (\<Gamma>1 * hn_ctxt Rh x x') (f' x') (\<Gamma>2 x x') R (f x)"
  assumes IMP: "\<And>x x'. \<Gamma>2 x x' \<Longrightarrow>\<^sub>A \<Gamma>' * hn_ctxt Rx x x' * true"
  shows "hn_refine \<Gamma> (m'\<bind>f') \<Gamma>' R (m\<bind>f)"
    unfolding hn_refine_def apply clarify
proof (goal_cases)
  case (1 h as n Mf)
  from 1(1) have nfm: "nofailT m" and nff: "\<And>x t. inresT m x t \<Longrightarrow> nofailT (f x)" by (auto simp: pw_bindT_nofailT)

  from nfm obtain M where M: "m = SPECT M" by fastforce 

  from D1 nfm 1(2) M 
  obtain r h' t ra Ca where execm: "execute m' h = Some (r, h', t)"
    and Mra: "M ra \<ge> Some (enat Ca)" and pH1: "pHeap h' (new_addrs h as h') (n + Ca - t) \<Turnstile> (\<Gamma>1 * Rh ra r) * true" and t: "t \<le> n + Ca"
    and relH1:  "relH {a. a < heap.lim h \<and> a \<notin> as} h h'" and hl1: "heap.lim h \<le> heap.lim h'"
    unfolding hn_refine_def by blast

  from M Mra have ram: "RETURNT ra \<le> m" apply (auto simp: le_fun_def RETURNT_def) 
    using dual_order.trans by fastforce
  have noff: "nofailT (f ra)" apply(rule nff[where t=0]) using Mra M unfolding inresT_def
    by (smt le_some_optE nrest.simps(5) zero_enat_def zero_le) 
  then obtain fM where fMra: "f ra = SPECT fM" by fastforce

  from D2[OF ram, of r] have D2': "\<And>h as n M.
       pHeap h as n \<Turnstile> \<Gamma>1 * Rh ra r \<Longrightarrow>
       f ra = SPECT M \<Longrightarrow>
       \<exists>h' t rb. execute (f' r) h = Some (rb, h', t) \<and>
                 (\<exists>raa Ca. M raa \<ge> Some (enat Ca) \<and> t \<le> n + Ca \<and> pHeap h' (new_addrs h as h') (n + Ca - t) \<Turnstile> \<Gamma>2 ra r * R raa rb * true) \<and>
                 relH {a. a < heap.lim h \<and> a \<notin> as} h h' \<and> heap.lim h \<le> heap.lim h'"   unfolding hn_refine_def hn_ctxt_def by auto

  from mod_star_convE[OF pH1]   obtain as1 as2 n1 n2 where  uni: "(new_addrs h as h') = as1 \<union> as2"
    and a: "as1 \<inter> as2 = {}" and  n: "(n + Ca - t) = n1 + n2"
    and pH1: "pHeap h' as1 n1 \<Turnstile> \<Gamma>1 * Rh ra r"
    and Fr': "pHeap h' as2 n2 \<Turnstile> true"  by blast 

  from D2'[OF pH1 fMra] obtain h'' t' r' ra' Ca' where execf: "execute (f' r) h' = Some (r', h'', t')" and
    fMra': " fM ra' \<ge> Some (enat Ca')"
    and M'':    " pHeap h'' (new_addrs h' as1 h'') (n1  + Ca' - t') \<Turnstile> \<Gamma>2 ra r * R ra' r' * true"
    and t':" t' \<le> n1  + Ca'" 
    and relH2': "relH {a. a < heap.lim h' \<and> a \<notin> as1} h' h''" and hl2: "heap.lim h' \<le> heap.lim h'' "
    by blast

  from Fr' have  Fr: "pHeap h'' as2 n2 \<Turnstile> true"  
    using hl2 top_assn_rule by auto  

  have disj: "new_addrs h' as1 h'' \<inter> as2 = {}"  
    using a models_in_range[OF Fr'] hl2
    by (auto simp: in_range.simps new_addrs_def)

  have k: "{a. a < lim h' \<and> a \<notin> (new_addrs h as h')} \<subseteq> {a. a < lim h' \<and> a \<notin> as1}"
    using uni  by auto
  have relH2: "relH {a. a < heap.lim h' \<and> a \<notin> (new_addrs h as h')} h' h''" 
    by(rule relH_subset[OF relH2' k])
        

      thm relH_subset
  have addrs: "(new_addrs h' as1 h'' \<union> as2) = (new_addrs h' (new_addrs h as h') h'')"
    using \<open>new_addrs h as h' = as1 \<union> as2\<close> new_addrs_def by auto

  have n12: " (n1 + Ca' - t' + n2) = (n + Ca - t) + Ca' - t'" using n t' by auto


  from mod_star_convI[OF disj M'' Fr] have
    M'': "pHeap h'' (new_addrs h' (new_addrs h as h') h'') ((n + Ca - t) + Ca' - t') \<Turnstile> \<Gamma>2 ra r * R ra' r' * true"
    unfolding n12  addrs by (metis assn_times_assoc assn_times_comm entailsD' entails_true)

  from Mra fMra' obtain Car Car' where PF: "M ra = Some Car" "fM ra' = Some Car'" by fastforce+


  thm execute_bind
  have t'': "n + Ca - t + Ca' - t' = n + (Ca + Ca') - (t + t')" using t t' by simp 
  have  
    "new_addrs h' (new_addrs h as h') h'' = new_addrs h as h''" 
    using hl1 hl2 
    by (auto simp add: new_addrs_def)
  with M'' have  
    ende: "pHeap h'' (new_addrs h as h'') (n + (Ca + Ca') - (t + t')) \<Turnstile>  \<Gamma>2 ra r * R ra' r' * true" 
    by (simp add: t'') 
  thm Sup_upper 
  have "Some (enat (Ca+Ca')) \<le> Some (Car+Car')" 
    using PF Mra fMra' add_mono by fastforce 
  also 
  from  1(3) fMra M have 
    "Some ((Car+Car')) \<le> Mf ra' "
    unfolding bindT_def  apply simp apply(drule nrest_Sup_SPECT_D[where x=ra'])
    apply simp apply(rule Sup_upper) apply auto
    apply(rule exI[where x="(map_option (op + (Car)) \<circ> fM)"]) 
    using PF  
    apply simp apply(rule exI[where x=ra]) apply(rule exI[where x="Car"]) by simp  
  finally have "Some (enat (Ca+Ca')) \<le> Mf ra' " .

  show ?case
    apply(rule exI[where x=h''])
    apply(rule exI[where x="t+t'"])
    apply(rule exI[where x="r'"])
  proof (safe)
    show "execute (m' \<bind> f') h = Some (r', h'', t + t')"
      by (simp add: execute_bind(1)[OF execm] execf) 
    show "\<exists>ra Ca. Mf ra \<ge> Some (enat Ca)\<and> t + t' \<le> n + Ca \<and> pHeap h'' (new_addrs h as h'') (n + Ca - (t + t')) \<Turnstile> \<Gamma>' * R ra r' * true "
      apply(rule exI[where x=ra'])
      apply(rule exI[where x="Ca+Ca'"])
    proof (safe)
      show "Mf ra' \<ge> Some (enat (Ca+Ca'))" apply fact done

      from IMP have "\<Gamma>2 ra r * R ra' r' * true \<Longrightarrow>\<^sub>A \<Gamma>' * R ra' r' * true"   
      proof -
        have "\<forall>a aa ab ac. (ac * ab \<Longrightarrow>\<^sub>A a * true) \<or> \<not> (ac \<Longrightarrow>\<^sub>A aa * a)"
          by (metis (full_types) assn_times_assoc entail_trans2 entails_frame entails_true mult.left_commute)
        then have "\<forall>a aa ab. ab * (aa * a) \<Longrightarrow>\<^sub>A aa * true"
          by (metis (no_types) assn_times_assoc entails_frame entails_true)
        then show ?thesis
          by (metis (no_types) IMP assn_times_assoc entail_trans2 entails_frame)
      qed  

      with ende  show "pHeap h'' (new_addrs h as h'') (n + (Ca + Ca') - (t + t')) \<Turnstile> \<Gamma>' * R ra' r' * true"
        using entailsD by blast
      show "t + t' \<le> n + (Ca + Ca')" using n t t' by simp
    qed 
    note relH1
    also have "relH {a. a < lim h \<and> a \<notin> as} h' h''"
      apply (rule relH_subset[OF relH2])
      using hl1 hl2
      by (auto simp: new_addrs_def) 
    finally show "relH {a. a < lim h \<and> a \<notin> as} h h''" . 
    show "heap.lim h \<le> heap.lim h'' "
      using hl1 hl2 by simp
  qed   
qed 



subsubsection \<open>Recursion\<close>
(* from Refine_Imperative_HOL.Sepref_Basic *)

lemma hnr_RECT:
  assumes S: "\<And>cf af ax px. \<lbrakk>
    \<And>ax px. hn_refine (hn_ctxt Rx ax px * F) (cf px) (F' ax px) Ry (af ax)\<rbrakk> 
    \<Longrightarrow> hn_refine (hn_ctxt Rx ax px * F) (cB cf px) (F' ax px) Ry (aB af ax)"
  assumes M: "(\<And>x. mono_Heap (\<lambda>f. cB f x))"
  shows "hn_refine 
    (hn_ctxt Rx ax px * F) (heap.fixp_fun cB px) (F' ax px) Ry (Sepreftime.RECT aB ax)"
  unfolding RECT_flat_gfp_def
proof (simp, intro conjI impI)
  assume "mono2 aB"
  hence "flatf_mono_ge aB" by(rule trimonoD_flatf_ge)
  have "\<forall>ax px. 
    hn_refine (hn_ctxt Rx ax px * F) (heap.fixp_fun cB px) (F' ax px) Ry 
      (flatf_gfp aB ax)"
      
    apply (rule flatf_ord.fixp_induct[OF _ \<open>flatf_mono_ge aB\<close>])  

    apply (rule flatf_admissible_pointwise)
    apply simp

    apply (auto simp: hn_refine_def) [] (* have no idea what happens here ! *)

    apply clarsimp
    apply (subst heap.mono_body_fixp[of cB, OF M])
    apply (rule S)
    apply blast
    done
  thus "hn_refine (hn_ctxt Rx ax px * F)
     (ccpo.fixp (fun_lub Heap_lub) (fun_ord Heap_ord) cB px) (F' ax px) Ry
     (flatf_gfp aB ax)" by simp
qed  
 








lemma hnr_If':
  assumes P: "\<Gamma> \<Longrightarrow>\<^sub>A \<Gamma>1 * hn_val bool_rel a a' * true"
  assumes RT: "a \<Longrightarrow> hn_refine (\<Gamma>1 * hn_val bool_rel a a') b' \<Gamma>2b R b"
  assumes RE: "\<not>a \<Longrightarrow> hn_refine (\<Gamma>1 * hn_val bool_rel a a') c' \<Gamma>2c R c"
  assumes IMP: "\<Gamma>2b \<or>\<^sub>A \<Gamma>2c \<Longrightarrow>\<^sub>A \<Gamma>' * true"
  shows "hn_refine \<Gamma> (if a' then b' else c') \<Gamma>' R (if a then b else c)"
  apply (rule hn_refine_cons'[OF P])
  apply (rule hn_refine_preI)
  apply (cases a; simp add: hn_ctxt_def pure_def)
     
      apply  (rule hn_refine_split_post)
      apply  (rule hn_refine_cons_pre'[OF _ RT])
        apply  (simp add: hn_ctxt_def pure_def entt_refl')
      apply  simp 

    apply (rule hn_refine_post_other)
    apply (rule hn_refine_cons_pre'[OF _ RE])
        apply (simp add: hn_ctxt_def pure_def entt_refl')
      apply  simp  
  apply  (rule IMP)
  apply  (rule entt_refl')
  done 


lemma hnr_If:
  assumes P: "\<Gamma> \<Longrightarrow>\<^sub>t \<Gamma>1 * hn_val bool_rel a a'"
  assumes RT: "a \<Longrightarrow> hn_refine (\<Gamma>1 * hn_val bool_rel a a') b' \<Gamma>2b R b"
  assumes RE: "\<not>a \<Longrightarrow> hn_refine (\<Gamma>1 * hn_val bool_rel a a') c' \<Gamma>2c R c"
  assumes IMP: "\<Gamma>2b \<or>\<^sub>A \<Gamma>2c \<Longrightarrow>\<^sub>t \<Gamma>'"
  shows "hn_refine \<Gamma> (if a' then b' else c') \<Gamma>' R (if a then b else c)"
  apply (rule hn_refine_cons[OF P])
  apply1 (rule hn_refine_preI)
  applyF (cases a; simp add: hn_ctxt_def pure_def)
    focus
      apply1 (rule hn_refine_split_post)
        applyF (rule hn_refine_cons_pre[OF _ RT])
        applyS (simp add: hn_ctxt_def pure_def entt_refl)
        applyS simp
      solved
    solved
    apply1 (rule hn_refine_post_other)
    applyF (rule hn_refine_cons_pre[OF _ RE])
      applyS (simp add: hn_ctxt_def pure_def entt_refl)
      applyS simp
    solved
  solved
  applyS (rule IMP)
  applyS (rule entt_refl)
  done

subsection "how to extract a hoare triple from hn_refine"

lemma extract_cost_ub:
  assumes "hn_refine \<Gamma> c \<Gamma>' R (REST M)" "(\<And>c. c\<in>ran M \<Longrightarrow> c \<le> Cost_ub)"
  shows "<\<Gamma> * $Cost_ub> c <\<lambda>r. \<Gamma>' * (\<exists>\<^sub>Ara. R ra r * \<up>(ra \<in> dom M)) >\<^sub>t"
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
       (\<exists>ra Ca. Ma ra \<ge> Some (enat Ca) \<and> t \<le> n + Ca \<and> pHeap h' (new_addrs h as h') ((n + Ca) - t) \<Turnstile> \<Gamma>' * R ra r * true) \<and>
      relH {a. a < heap.lim h \<and> a \<notin> as} h h' \<and> heap.lim h \<le> heap.lim h')" 
    by auto

  thm effect_deterministic

  from 3[OF 2 ] obtain h' t' r' where E: "execute c h = Some (r', h', t') " and
    R:  "(\<exists>ra Ca. M ra \<ge> Some (enat Ca) \<and>
                    pHeap h' (new_addrs h as h') (n - Cost_ub + Ca - t') \<Turnstile> \<Gamma>' * R ra r' * true \<and> t' \<le> n - Cost_ub + Ca) \<and>
           relH {a. a < heap.lim h \<and> a \<notin> as} h h' \<and> heap.lim h \<le> heap.lim h'" by blast

  have F: "\<sigma> = Some h'" and prime: "r' = r" "t' = t"  
    using E 1(3) run.cases apply force
    using E 1(3) run.cases apply force
    using E 1(3) run.cases by force 
  then have sig: "the \<sigma> = h'" by auto
  from R  have
    B: "(\<exists>ra Ca. M ra \<ge> Some (enat Ca) \<and>
     pHeap (the \<sigma>) (new_addrs h as (the \<sigma>)) (n - Cost_ub + Ca - t) \<Turnstile> \<Gamma>' * R ra r * true \<and>
        t \<le> n - Cost_ub + Ca )" and C:
    "relH {a. a < heap.lim h \<and> a \<notin> as} h (the \<sigma>)" "heap.lim h \<le> heap.lim (the \<sigma>) " 
    unfolding prime sig by auto



  from B obtain ra Ca where i: "pHeap (the \<sigma>) (new_addrs h as (the \<sigma>)) (n - Cost_ub + Ca - t) \<Turnstile> \<Gamma>' * R ra r * true"
    and ii:  "t \<le> n - Cost_ub + Ca"  and ineq: "M ra \<ge> Some (enat Ca)"
    using B by auto

  from ineq have radom: "ra \<in> dom M" using domIff by fastforce  
  then obtain Mra where Mra: "M ra = Some Mra" by blast
  with assms(2) have "Mra \<le> enat Cost_ub" by (meson ranI)
  with Mra ineq have "Some (enat Ca) \<le> Some (enat Cost_ub)" 
    using dual_order.trans by fastforce 
  then have ie: "Ca \<le> Cost_ub" by auto

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



lemma extraction_example: "hn_refine \<Gamma> c \<Gamma>' (\<lambda>ra r. \<up>(ra = r)) (REST [length xs\<mapsto> enat (Costs)]) \<Longrightarrow>
           <\<Gamma> * $Costs> c <\<lambda>r. \<Gamma>' * \<up>(r = length xs) >\<^sub>t"
  unfolding hn_refine_def
  unfolding hoare_triple_def 
  apply clarify
proof (goal_cases)
  case (1 h as \<sigma> r n t)
  from 1(2) have 2: "pHeap h as (n-Costs) \<Turnstile> \<Gamma>" and  nf: "n\<ge>Costs"
    using mod_timeCredit_dest by auto

  from 1(1) have 3: "\<And>h as n M.
       pHeap h as n \<Turnstile> \<Gamma> \<Longrightarrow> 
      SPECT [length xs \<mapsto> enat (Costs)] = SPECT M \<Longrightarrow> (\<exists>h' t r. execute c h = Some (r, h', t) \<and>      
       (\<exists>ra Ca. M ra \<ge> Some (enat Ca) \<and> t \<le> n + Ca \<and> pHeap h' (new_addrs h as h') ((n + Ca) - t) \<Turnstile> \<Gamma>' * \<up> (ra = r) * true) \<and>
      relH {a. a < heap.lim h \<and> a \<notin> as} h h' \<and> heap.lim h \<le> heap.lim h')" 
      by auto

    thm effect_deterministic
  
    from 3[OF 2 ] obtain h' t' r' where E: "execute c h = Some (r', h', t') " and
          R:  "(\<exists>ra Ca. [length xs \<mapsto> enat (Costs)] ra \<ge> Some (enat Ca) \<and>
                    pHeap h' (new_addrs h as h') (n - Costs + Ca - t') \<Turnstile> \<Gamma>' * \<up> (ra = r') * true \<and> t' \<le> n - Costs + Ca) \<and>
           relH {a. a < heap.lim h \<and> a \<notin> as} h h' \<and> heap.lim h \<le> heap.lim h'" by blast

    have F: "\<sigma> = Some h'" and prime: "r' = r" "t' = t"  
      using E 1(3) run.cases apply force
      using E 1(3) run.cases apply force
      using E 1(3) run.cases by force 
    then have sig: "the \<sigma> = h'" by auto
    from R  have
    B: "(\<exists>ra  Ca. [length xs \<mapsto> enat (Costs)] ra \<ge> Some (enat Ca) \<and>
     pHeap (the \<sigma>) (new_addrs h as (the \<sigma>)) (n - Costs + Ca - t) \<Turnstile> \<Gamma>' * (\<lambda>ra r. \<up>(ra = r)) ra r * true \<and>
        t \<le> n - Costs + Ca )" and C:
  "relH {a. a < heap.lim h \<and> a \<notin> as} h (the \<sigma>)" "heap.lim h \<le> heap.lim (the \<sigma>) " 
      unfolding prime sig by auto
 

   have p2: "\<And>ra Ca. ([length xs \<mapsto> enat (Costs)] ra \<ge> Some (enat Ca)) =
                (ra = length xs \<and> Ca \<le> Costs)" by auto
 

  from B obtain Ca where i: "pHeap (the \<sigma>) (new_addrs h as (the \<sigma>)) (n - Costs + Ca - t) \<Turnstile> \<Gamma>' * (\<lambda>ra r. \<up>(ra = r)) (length xs) r * true"
      and ii:  "t \<le> n - Costs + Ca"  and ineq: "Ca \<le> Costs"
         
    using B unfolding p2 using nf by auto


  have pr: "(n - Costs + Ca - t) = (n - t) - (Costs - Ca)" using ineq ii nf by auto
  have pl: "(n - (t + (Costs - Ca)) + (Costs - Ca)) = n-t" using ineq ii nf by auto

  have "pHeap (the \<sigma>) (new_addrs h as (the \<sigma>) \<union> {}) ((n - t) - (Costs - Ca) + (Costs - Ca)) \<Turnstile> \<Gamma>' * (\<lambda>ra r. \<up>(ra = r)) (length xs) r * true * true"
    apply(rule mod_star_convI)  apply simp
    apply(rule i[unfolded pr])  by (simp add: top_assn_rule)
 
  then have H: "pHeap (the \<sigma>) (new_addrs h as (the \<sigma>)) (n - t) \<Turnstile> \<Gamma>' * \<up> (r = length xs) * true"
    apply (simp add: pl)  
    apply (simp add: assn_times_assoc top_assn_reduce)  by argo  
  
  from ii ineq nf have T: "t \<le> n " by auto

  show ?case
    apply safe
    subgoal using F by auto
    subgoal using H by simp  
    subgoal by fact
    apply fact apply fact done
    
qed
  


end