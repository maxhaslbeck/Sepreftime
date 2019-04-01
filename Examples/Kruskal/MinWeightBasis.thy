theory MinWeightBasis
  imports "../../Sepreftime" "../../Refine_Foreach"
    "List-Index.List_Index" Matroids.Matroid     
begin
  
abbreviation "sorted_wrt_w w == sorted_wrt (\<lambda>e1 e2. w e1 \<le> w e2)"
  
locale minWeightBasis = matroid carrier indep for carrier::"'a set" and indep  +
  fixes w :: "'a \<Rightarrow> 'b::{linorder, ordered_comm_monoid_add}"
begin
   
section \<open>minWeightBasis algorithm\<close>
   

subsection \<open>Proof that it computes an minimum Basis\<close>

definition minBasis where "minBasis B \<equiv> basis B \<and> (\<forall>B'. basis B' \<longrightarrow> sum w B \<le> sum w B')"  
                                         
subsubsection \<open>preparation\<close>
     
fun in_sort_edge where
   "in_sort_edge x [] = [x]" 
 | "in_sort_edge x (y#ys) = (if w x \<le> w y then x#y#ys else y# in_sort_edge x ys)"  

lemma [simp]: "set (in_sort_edge x L) = insert x (set L)"
apply(induct L) by auto

lemma in_sort_edge: "sorted_wrt (\<lambda>e1 e2. w e1 \<le> w e2) L \<Longrightarrow> sorted_wrt (\<lambda>e1 e2. w e1 \<le> w e2) (in_sort_edge x L)"
  apply(induct L ) by auto
   
lemma in_sort_edge_distinct: "x \<notin> set L \<Longrightarrow> distinct L \<Longrightarrow> distinct (in_sort_edge x L)"    
apply(induct L) by auto 
    
lemma finite_sorted_edge_distinct:
  assumes "finite S" 
  obtains L where "distinct L" "sorted_wrt (\<lambda>e1 e2. w e1 \<le> w e2) L" "S = set L"
proof -
  {
    have "\<exists>L.  distinct L \<and> sorted_wrt (\<lambda>e1 e2. w e1 \<le> w e2) L \<and> S = set L"
      using assms
      apply(induct S)
       apply(clarsimp)
      apply(clarsimp) 
      subgoal for x L apply(rule exI[where x="in_sort_edge x L"])
        by (auto simp: in_sort_edge in_sort_edge_distinct)
    done
  }
  with that show ?thesis by blast
qed    
    
abbreviation "wsorted == sorted_wrt_w w"
  
lemma sum_list_map_cons: "sum_list (map w (y # ys)) = w y + sum_list (map w ys)" by auto  
     
lemma exists_greater:
  assumes  len: "length F = length F'"
      and sum: "sum_list (map w F) > sum_list (map w F')"
    shows "\<exists>i<length F. w (F ! i) > w (F' ! i)"
using len sum    
proof (induct rule: list_induct2) 
  case (Cons x xs y ys)    
  show ?case
  proof(cases "w y < w x")
    case True
    then show ?thesis by auto
  next
    case False
    from False Cons(3) have "sum_list (map w ys) < sum_list (map w xs)"
      apply(simp add: sum_list_map_cons) 
      by (meson add_mono leD le_less_linear)
    from Cons(2)[OF this] show ?thesis by auto
  qed
qed simp
 

  
lemma wsorted_Cons: "wsorted (x#xs) = (wsorted xs & (ALL y:set xs. w x <= w y))"
  by (induct xs arbitrary: x) auto 
  
   

lemma wsorted_nth_mono: assumes "wsorted L" "i\<le>j" "j<length L"
  shows "w (L!i) \<le> w (L!j)"
  using assms apply (induct L arbitrary: i j rule: list.induct) by (auto simp: nth_Cons' wsorted_Cons) 
 
(**
  limi T g is the set T restricted  
     to elements only with weight
    strictly smaller than g.
*)
definition "limi T g == {e. e\<in>T \<and> w e < g}"
  
lemma limi_subset: "limi T g \<subseteq> T" unfolding limi_def by auto  
  
lemma limi_mono: "A \<subseteq> B \<Longrightarrow> limi A g \<subseteq> limi B g"
unfolding limi_def by auto


(*
  let F be a set of elements
  limi F g is the set F restricted to elements with weight smaller than g
  let E be a set of elements we want to exclude
    
  no_smallest_element_skipped E F says,
     that going greedyly over (carrier-E), every every element,
     that did not render the akkumulated set dependent, was added to the set F.
*)
definition "no_smallest_element_skipped E F = (\<forall>e\<in>carrier - E. \<forall>g>w e. indep (insert e (limi F g)) \<longrightarrow> (e \<in> limi F g))"
  
lemma no_smallest_element_skipped_empty[simp]: "no_smallest_element_skipped carrier {}"
  by(auto simp: no_smallest_element_skipped_def)

lemma no_smallest_element_skippedD: "no_smallest_element_skipped E F \<Longrightarrow> (\<And>e g. e \<in>carrier - E \<Longrightarrow> w e < g \<Longrightarrow> (indep (insert e (limi F g)) \<Longrightarrow>  e\<in> limi F g))"
  by(auto simp: no_smallest_element_skipped_def)
 
subsubsection \<open>the heart of the argument\<close>


lemma greedy_approach_leads_to_minBasis: assumes "indep F"
  and "\<forall>e\<in>carrier - F. \<not> indep (insert e F)"
  and "no_smallest_element_skipped {} F"
  shows "minBasis F"
proof (rule ccontr)
  \<comment> \<open>from our assumptions we have that F is a basis\<close>  
  from assms have bF: "basis F" using indep_not_basis by blast
  \<comment> \<open>towards a contradiction, assume F is not a minimum Basis\<close>
  assume notmin: "\<not> minBasis F"    
  \<comment> \<open>then we can get a smaller Basis B\<close>
  from bF notmin[unfolded minBasis_def] obtain B where bB: "basis B" and sum: "sum w B < sum w F"
    by force
  \<comment> \<open>lets us obtain two sorted lists for the bases F and B\<close>
  from bF basis_finite finite_sorted_edge_distinct
    obtain FL where dF[simp]: "distinct FL" and wF[simp]: "wsorted FL" and sF[simp]: "F = set FL"
    by blast
  from bB basis_finite finite_sorted_edge_distinct
    obtain BL where dB[simp]: "distinct BL" and wB[simp]: "wsorted BL" and sB[simp]: "B = set BL"
      by blast
  \<comment> \<open>as basis F has more total weight than basis B ...\<close>
  from sum have suml: "sum_list (map w BL) < sum_list (map w FL)"
    by(simp add: sum.distinct_set_conv_list[symmetric]) 
  from bB bF have "card B = card F"
    using basis_card by blast 
  then have l: "length FL = length BL"
    by (simp add: distinct_card) 
  \<comment> \<open>... there exists an index i such that the ith element of the BL is strictly smaller 
      than the ith element of FL \<close>
  from exists_greater[OF (*_ _ _ _*) l suml] obtain i where i: "i<length FL" and gr: "w (BL ! i) < w (FL ! i)"
    by auto
  let ?FL_restricted = "limi (set FL) (w (FL ! i))"

  \<comment> \<open>now let us look at the two independent sets X and Y:
        let X and Y be the set if we take the first i-1 elements of BL
         and the first i elements of FL respectively. 
      We want to use the augment property of Matroids in order to show that we must have skipped
      and optimal element, which then contradicts our assumption. \<close>
  let ?X = "take i FL"
  have X_size: "card (set ?X) = i" using i
    by (simp add: distinct_card)
  have X_indep: "indep (set ?X)" using bF
    using indep_iff_subset_basis set_take_subset by force

  let ?Y = "take (Suc i) BL"
  have Y_size: "card (set ?Y) = Suc i" using i l
    by (simp add: distinct_card)
  have Y_indep: "indep (set ?Y)" using bB
    using indep_iff_subset_basis set_take_subset by force 

  have "card (set ?X) < card (set ?Y)" using X_size Y_size by simp

  \<comment> \<open>X and Y are independent and X is smaller than Y, thus we can augment X with some element x\<close>
  with Y_indep X_indep                                 
    obtain x where x: "x\<in>set (take (Suc i) BL) - set ?X" and indepX: "indep (insert x (set ?X))"
      using augment by auto

  \<comment> \<open>we know many things about x now, i.e. x weights strictly less than the ith element of FL ...\<close>
  have "x\<in>carrier"  using indepX indep_subset_carrier by blast     
  from x have xs: "x\<in>set (take (Suc i) BL)" and xnX: "x \<notin> set ?X" by auto
  from xs have "w x \<le> w (BL ! i)" using wB
    by (metis List.length_take Lists_Thms.nth_take Suc_leI Suc_le_mono dB distinct_Ex1 distinct_take i local.l min_Suc_gt(2) wsorted_nth_mono)
      (* FIXME *)
  then have k: "w x < w (FL ! i)" using gr by auto

  \<comment> \<open>... and that adding x to X gives us an independent set\<close>
  have "?FL_restricted \<subseteq> set ?X"
    unfolding  limi_def apply auto
    by (smt dF i index_nth_id leD leI linorder_linear mem_Collect_eq set_conv_nth set_take_if_index wF wsorted_nth_mono) (* FIXME *) 
  have z': "insert x ?FL_restricted \<subseteq> insert x (set ?X)"
    using xnX `?FL_restricted \<subseteq> set (take i FL)` by auto 
  from indep_subset[OF indepX z'] have add_x_stay_indep: "indep (insert x ?FL_restricted)" .

  \<comment> \<open>... finally this means that we must have taken the element during our greedy algorithm\<close>
  from `no_smallest_element_skipped {} F` `x\<in>carrier` `w x < w (FL ! i)` add_x_stay_indep
    have "x \<in> ?FL_restricted"  by (auto dest: no_smallest_element_skippedD)
  with `?FL_restricted \<subseteq> set ?X` have "x \<in> set ?X"  by auto

  \<comment> \<open>... but we actually didn't. This finishes our proof by contradiction.\<close>  
  with xnX show "False" by auto              
qed

lemma assumes createsCycle: "\<not> indep (insert e F)"
       and    I: "no_smallest_element_skipped (E\<union>{e}) F"
       and    sorted: "(\<forall>x\<in>F.\<forall>y\<in>(E\<union>{e}). w x \<le> w y)"
     shows I_preservation1': "no_smallest_element_skipped E F"
  unfolding no_smallest_element_skipped_def
proof (clarsimp)
  fix x g
  assume x: "x \<in> carrier"  "x \<notin> E"  "w x < g"
  assume f: "indep (insert x (limi F g))" 
  show "(x \<in> limi F g)"  
  proof (cases "x=e")
    case True 
    from True have "limi F g = F"
      unfolding limi_def using \<open>w x < g\<close> sorted by fastforce  
    with createsCycle f True have "False" by auto  
    then show ?thesis by simp
  next
    case False
    show ?thesis 
    apply(rule I[THEN no_smallest_element_skippedD, OF _ \<open>w x < g\<close>])
    using x f False
    by (auto simp add: )
  qed
qed
 
lemma I_preservation2:       
    assumes "e \<in> E" "\<forall>e\<in>carrier - E - F. \<not> indep (insert e F)"        
    shows  "(\<forall>x\<in>carrier - (E - {e}) - insert e F. \<not> indep (insert x (insert e F)))"
using assms  by (smt Diff_insert Diff_insert2 indep_subset insert_Diff insert_commute subset_insertI)
 

lemma I_preservation3':
  assumes I: "no_smallest_element_skipped (E\<union>{e}) F"
  shows "no_smallest_element_skipped E (insert e F)"
  unfolding no_smallest_element_skipped_def
proof (clarsimp)
  fix x g
  assume xc: "x \<in> carrier"
  assume x: "x \<notin> E"
  assume wx: "w x < g"
  assume f: "indep (insert x (limi (insert e F) g))"
  show "(x \<in> limi (insert e F) g)"
  proof(cases "x=e")
    case True   
    then show ?thesis unfolding limi_def
      using wx by blast 
  next
    case False
    have ind: "indep (insert x (limi F g))" apply(rule indep_subset[OF f]) using limi_mono by blast  
    have "indep (insert x (limi F g)) \<Longrightarrow> x \<in> limi F g" 
      apply(rule I[THEN no_smallest_element_skippedD]) using False xc wx x by auto
    with ind show ?thesis using limi_mono by blast
  qed      
qed 
 
  
  
definition I_minWeightBasis_fine where
  "I_minWeightBasis_fine == \<lambda>(T,E). indep T 
                \<and> T \<subseteq> carrier
                 \<and> E \<subseteq> carrier  \<and> T \<inter> E = {} 
                 \<and> (\<forall>x\<in>T.\<forall>y\<in>E. w x \<le> w y)
                \<and> (\<forall>e\<in>carrier-E-T. ~indep (insert e T))
                 \<and> no_smallest_element_skipped E T"

lemma I_minWeightBasis_fineD: 
  assumes 
   "I_minWeightBasis_fine (T,E)"
 shows"indep T" "\<And>e. e\<in>carrier-E-T \<Longrightarrow> ~indep (insert e T)"
    "E \<subseteq> carrier" "\<And>x y. x\<in>T \<Longrightarrow> y\<in>E \<Longrightarrow> w x \<le> w y" "T \<inter> E = {}" "T \<subseteq> carrier"
    "no_smallest_element_skipped E T"
  using assms by(auto simp: no_smallest_element_skipped_def I_minWeightBasis_fine_def)

lemma I_minWeightBasis_fineI:
  assumes "indep T" "\<And>e. e\<in>carrier-E-T \<Longrightarrow> ~indep (insert e T)"
    "E \<subseteq> carrier" "\<And>x y. x\<in>T \<Longrightarrow> y\<in>E \<Longrightarrow> w x \<le> w y" "T \<inter> E = {}" "T \<subseteq> carrier"
    "no_smallest_element_skipped E T"
  shows "I_minWeightBasis_fine (T,E)"
  using assms by(auto simp: no_smallest_element_skipped_def I_minWeightBasis_fine_def)

lemma I_minWeightBasis_fineG: "I_minWeightBasis_fine (T,E) \<Longrightarrow> no_smallest_element_skipped E T" by(auto simp: no_smallest_element_skipped_def I_minWeightBasis_fine_def)

lemma I_minWeightBasis_sorted: "I_minWeightBasis_fine (T,E) \<Longrightarrow> (\<forall>x\<in>T.\<forall>y\<in>E. w x \<le> w y)" by(auto simp: no_smallest_element_skipped_def I_minWeightBasis_fine_def)
 
  
end

locale minWeightBasis_time = minWeightBasis +
  fixes sorted_carrier_time :: nat
    and  empty_basis_time indep_test_time insert_time :: nat
begin
subsection \<open>Refinement to an algorithm using sorted lists\<close> 

  definition (in -) "obtain_sorted_carrier_aux sct c w \<equiv> SPECT (emb (\<lambda>L. sorted_wrt_w w L \<and> distinct L \<and> set L = c) sct)"

  abbreviation "obtain_sorted_carrier \<equiv> obtain_sorted_carrier_aux sorted_carrier_time carrier w"
      
section \<open>minWeightBasis algorithm with nfoldi\<close>

abbreviation "empty_basis \<equiv> {}"

 

definition (in -) minWeightBasis3_aux where 
  "minWeightBasis3_aux osc_t c we ebt itt it ind eb \<equiv> do {
        l \<leftarrow> obtain_sorted_carrier_aux osc_t c we ;
        ASSERT (set l = c);
        s \<leftarrow> SPECT [eb\<mapsto>ebt];
        T \<leftarrow> nfoldli l (\<lambda>_. True)
        (\<lambda>e T. do { 
            ASSERT (e\<notin>T \<and> ind T \<and> e\<in>c \<and> T\<subseteq>c);
            b \<leftarrow> SPECT [ind (insert e T) \<mapsto> itt];
            if b then
              SPECT [(insert e T)\<mapsto>it]
            else 
              RETURNT T
        }) s;
        RETURNT T
      }"

abbreviation "minWeightBasis3 \<equiv> minWeightBasis3_aux sorted_carrier_time carrier w empty_basis_time
                                     indep_test_time insert_time indep empty_basis"



lemma I_minWeightBasis_fine_empty: "I_minWeightBasis_fine ({}, carrier)"
  by (auto simp: I_minWeightBasis_fine_def)

lemma I_minWeightBasis_fine_final: "I_minWeightBasis_fine (T, {}) \<Longrightarrow> minBasis T"
  by(auto simp: greedy_approach_leads_to_minBasis I_minWeightBasis_fine_def)

lemma preservation_else: "set x = carrier \<Longrightarrow>
    x = l1 @ xa # l2 \<Longrightarrow> I_minWeightBasis_fine (\<sigma>, set (xa # l2))
     \<Longrightarrow> indep \<sigma>   \<Longrightarrow> \<not> indep (insert xa \<sigma>) \<Longrightarrow> I_minWeightBasis_fine (\<sigma>, set l2)"
  apply(rule I_minWeightBasis_fineI)
  subgoal by simp
  subgoal by (auto simp: DiffD2 I_minWeightBasis_fine_def)   
  subgoal by auto 
  subgoal by(auto simp: I_minWeightBasis_fine_def)   
  subgoal by(auto simp: I_minWeightBasis_fine_def)  
  subgoal by(auto simp: I_minWeightBasis_fine_def)  
  subgoal apply (rule I_preservation1')
    by(auto intro!:  simp: I_minWeightBasis_fine_def)  
  done

lemma I_preservation2':       
  assumes "e \<in> E" "\<forall>e\<in>carrier - E - F. \<not> indep (insert e F)"        
    and "x\<in>carrier - (E - {e}) - insert e F"
    shows  "\<not> indep (insert x (insert e F))"
  using assms I_preservation2 by auto

lemma preservation_if: "wsorted x \<Longrightarrow> distinct x \<Longrightarrow> set x = carrier \<Longrightarrow>
    x = l1 @ xa # l2 \<Longrightarrow> I_minWeightBasis_fine (\<sigma>, set (xa # l2)) \<Longrightarrow> True \<Longrightarrow> xa \<notin> \<sigma>  
   \<Longrightarrow> xa \<in> carrier \<Longrightarrow> indep (insert xa \<sigma>) \<Longrightarrow> I_minWeightBasis_fine (insert xa \<sigma>, set l2)"
  apply(rule I_minWeightBasis_fineI)
  subgoal by simp      
  subgoal unfolding I_minWeightBasis_fine_def apply(rule I_preservation2'[where E="set (xa # l2)"]) 
    by simp_all 
  subgoal by auto        
  subgoal by (metis insert_iff list.set(2) I_minWeightBasis_sorted sorted_wrt_append wsorted_Cons)  
  subgoal by(auto simp: I_minWeightBasis_fine_def)  
  subgoal by(auto simp: I_minWeightBasis_fine_def)  
  subgoal apply (rule I_preservation3')
    by(auto intro!:  simp: I_minWeightBasis_fine_def)  
  done

definition "minBasis_time = sorted_carrier_time +  empty_basis_time
             +  card carrier * (indep_test_time + insert_time)"


lemma le_Id: "M \<le> M' \<Longrightarrow> M \<le> \<Down> Id M'"
  by auto

theorem minWeightBasis3_refine: "minWeightBasis3 \<le> \<Down> Id (SPECT (emb minBasis minBasis_time))"
  unfolding minWeightBasis3_aux_def obtain_sorted_carrier_aux_def
  unfolding nfoldliIE_def[where E="indep_test_time + insert_time" and I="\<lambda>l1 l2 s. I_minWeightBasis_fine (s,set l2)", symmetric]
  apply(rule le_Id)
  apply(rule T_specifies_I) 
  unfolding nfoldliIE'_def[symmetric]                      
  apply(vcg' \<open>-\<close> rules: nfoldliIE'_rule  )
  unfolding Some_le_emb'_conv
       apply (safe) 
  oops

lemmas f = nfoldliIE_rule[where  t="card carrier * (indep_test_time + insert_time)" and
                    P="\<lambda>T. I_minWeightBasis_fine (T, {})", THEN T_specifies_rev, THEN T_conseq4]
theorem minWeightBasis3_refine: "minWeightBasis3 \<le> \<Down> Id (SPECT (emb minBasis minBasis_time))"
  unfolding minWeightBasis3_aux_def obtain_sorted_carrier_aux_def
  unfolding nfoldliIE_def[where E="indep_test_time + insert_time" and I="\<lambda>l1 l2 s. I_minWeightBasis_fine (s,set l2)", symmetric]
  apply(rule le_Id)
    apply(rule T_specifies_I)             
  apply(vcg' \<open>-\<close> rules: f ) 

  subgoal by (auto simp: I_minWeightBasis_fine_empty) 
  subgoal (* loop body *)
    apply(rule T_specifies_I)
    apply(vcg' \<open>-\<close> rules: f ) 
      apply(simp_all add: Some_le_emb'_conv )

    subgoal apply(rule preservation_if) by (auto dest!: I_minWeightBasis_fineD(5))  
    subgoal apply(rule preservation_else) by (auto dest!: I_minWeightBasis_fineD(1))  

    (* asserts *)
    subgoal by (auto      simp: I_minWeightBasis_fine_def)  
    done
  subgoal by simp
  subgoal by simp

  subgoal by (auto  simp:  distinct_card Some_le_emb'_conv )
  subgoal by (auto  simp: I_minWeightBasis_fine_final minBasis_time_def vcg_simp_rules)
  subgoal by auto                      
  done
 



end
  
  
end