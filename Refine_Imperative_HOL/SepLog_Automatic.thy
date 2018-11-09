theory SepLog_Automatic
imports "SepLogicTime_RBTreeBasic.SepAuto" 
  "HOL-Eisbach.Eisbach" "../SepLogic_Misc"
begin


lemma ent_pure_pre_iff[simp]: "(P*\<up>b \<Longrightarrow>\<^sub>A Q) \<longleftrightarrow> (b \<longrightarrow> (P \<Longrightarrow>\<^sub>A Q))"
  unfolding entails_def
  by (auto   )

lemma ent_pure_pre_iff_sng[simp]: 
  "(\<up>b \<Longrightarrow>\<^sub>A Q) \<longleftrightarrow> (b \<longrightarrow> (emp \<Longrightarrow>\<^sub>A Q))"
  using ent_pure_pre_iff[where P=emp]
  by simp

lemma ent_pure_post_iff[simp]: 
  "(P \<Longrightarrow>\<^sub>A Q*\<up>b) \<longleftrightarrow> ((\<forall>h. h\<Turnstile>P \<longrightarrow> b) \<and> (P \<Longrightarrow>\<^sub>A Q))"
  unfolding entails_def
  by (auto)

lemma ent_pure_post_iff_sng[simp]: 
  "(P \<Longrightarrow>\<^sub>A \<up>b) \<longleftrightarrow> ((\<forall>h. h\<Turnstile>P \<longrightarrow> b) \<and> (P \<Longrightarrow>\<^sub>A emp))"
  using ent_pure_post_iff[where Q=emp]
  by simp 



subsection "Rotate method"

definition gr where "gr A B = A * B"

lemma right_swap: "(A \<Longrightarrow>\<^sub>A B * (C * D)) \<Longrightarrow> (A \<Longrightarrow>\<^sub>A B * (D * C))"
  by (simp add: assn_times_comm)
lemma right_take: "(A \<Longrightarrow>\<^sub>A gr B C * D) \<Longrightarrow> (A \<Longrightarrow>\<^sub>A B * (C * D))"
  by (simp add: gr_def assn_times_assoc) 
lemma left_swap: "(B * (C * D) \<Longrightarrow>\<^sub>A A) \<Longrightarrow> (B * (D * C) \<Longrightarrow>\<^sub>A A)"
  by (simp add: assn_times_comm)
lemma left_take: "(gr B C * D \<Longrightarrow>\<^sub>A A) \<Longrightarrow> (B * (C * D) \<Longrightarrow>\<^sub>A A)"
  by (simp add: gr_def assn_times_assoc) 

lemma right_move_back: "(A \<Longrightarrow>\<^sub>A B * C) \<Longrightarrow> (A \<Longrightarrow>\<^sub>A C * B)"
  by (simp add: assn_times_comm)
lemma left_move_back: "(B * C \<Longrightarrow>\<^sub>A A) \<Longrightarrow> (C * B \<Longrightarrow>\<^sub>A A)"
  by (simp add: assn_times_comm)
lemma right_move_backt: "(A \<Longrightarrow>\<^sub>t B * C) \<Longrightarrow> (A \<Longrightarrow>\<^sub>t C * B)"
  by (simp add: assn_times_comm)
lemma left_move_backt: "(B * C \<Longrightarrow>\<^sub>t A) \<Longrightarrow> (C * B \<Longrightarrow>\<^sub>t A)"
  by (simp add: assn_times_comm)

thm mult.assoc
method rotater = ( (simp only: mult.assoc)? , rule right_move_back , (simp only: mult.assoc)?  )
method rotatel = ( (simp only: mult.assoc)? , rule left_move_back , (simp only: mult.assoc)?  )

method swapl = ( (simp only: mult.assoc)? ,rule left_swap, (simp only: mult.assoc)?   )
method takel = ( (simp only: mult.assoc)? , rule left_take, (simp only: mult.assoc)?  )

method swapr = ( (simp only: mult.assoc)? , rule right_swap , (simp only: mult.assoc)?  )
method taker = ( (simp only: mult.assoc)? , rule right_take, (simp only: mult.assoc)?  )

method rotatert = ( (simp only: mult.assoc)? , rule right_move_backt , (simp only: mult.assoc)?  )
method rotatelt = ( (simp only: mult.assoc)? , rule left_move_backt , (simp only: mult.assoc)?  )


lemma match_firstt: "A \<Longrightarrow>\<^sub>t B \<Longrightarrow> \<Gamma> * A \<Longrightarrow>\<^sub>t \<Gamma> * B"   
  by (simp add: entt_star_mono) 

lemma match_restt: "emp \<Longrightarrow>\<^sub>t B \<Longrightarrow> \<Gamma> \<Longrightarrow>\<^sub>t \<Gamma> * B"  
  using match_firstt by fastforce 

lemma match_first: "A \<Longrightarrow>\<^sub>A B \<Longrightarrow> \<Gamma> * A \<Longrightarrow>\<^sub>A \<Gamma> * B"  
  by (simp add: assn_times_comm entails_frame)  

lemma match_rest: "emp \<Longrightarrow>\<^sub>A B \<Longrightarrow> \<Gamma> \<Longrightarrow>\<^sub>A \<Gamma> * B"  
  using match_first by fastforce 

lemma run_and_execute: "(\<forall>\<sigma> t r. run c (Some h) \<sigma> r t \<longrightarrow> \<sigma> \<noteq> None \<and> P (the \<sigma>) r t)
        \<longleftrightarrow> (\<exists>h' t r. execute c h = Some (r, h', t) \<and> P h' r t)"  
  apply rule
  subgoal by (metis option.sel run.intros(2) run.intros(3) timeFrame.elims) 
  subgoal by (metis (mono_tags) not_None_eq option.sel prod.sel(1) prod.sel(2) run_to_execute) 
  done





subsection "Simplifier setup"


lemma is_entails: "P\<Longrightarrow>\<^sub>AQ \<Longrightarrow> P \<Longrightarrow>\<^sub>AQ" .
 
text {* Used by existential quantifier extraction tactic *}
lemma enorm_exI': (* Incomplete, as chosen x may depend on heap! *)
  "(\<And>x. Z x \<longrightarrow> (P \<Longrightarrow>\<^sub>A Q x)) \<Longrightarrow> (\<exists>x. Z x) \<longrightarrow> (P \<Longrightarrow>\<^sub>A (\<exists>\<^sub>Ax. Q x))"
  by (metis ent_ex_postI)


lemma ent_false: "false \<Longrightarrow>\<^sub>A P" by simp  
lemmas solve_ent_preprocess_simps = 
  ent_pure_post_iff ent_pure_post_iff_sng ent_pure_pre_iff ent_pure_pre_iff_sng
lemmas ent_refl = entails_triv
lemmas ent_triv = ent_true ent_false
lemmas norm_assertion_simps = assn_one_left 

(*
theorem solve_ent_preprocess_simps:
            (?P \<Longrightarrow>\<^sub>A ?Q * \<up> ?b) = ((\<forall>h. h \<Turnstile> ?P \<longrightarrow> ?b) \<and> (?P \<Longrightarrow>\<^sub>A ?Q))
            (?P \<Longrightarrow>\<^sub>A \<up> ?b) = ((\<forall>h. h \<Turnstile> ?P \<longrightarrow> ?b) \<and> (?P \<Longrightarrow>\<^sub>A emp))
            (?P * \<up> ?b \<Longrightarrow>\<^sub>A ?Q) = (?b \<longrightarrow> (?P \<Longrightarrow>\<^sub>A ?Q))
            (\<up> ?b \<Longrightarrow>\<^sub>A ?Q) = (?b \<longrightarrow> (emp \<Longrightarrow>\<^sub>A ?Q)) *) 


subsection {* Frame Matcher *}
text {* Given star-lists P,Q and a frame F, this method tries to match 
  all elements of Q with corresponding elements of P. The result is a 
  partial match, that contains matching pairs and the unmatched content.*}

text {* The frame-matcher internally uses syntactic lists separated by
  star, and delimited by the special symbol @{text "SLN"}, which is defined
  to be @{text "emp"}. *}
definition [simp]: "SLN \<equiv> emp"
lemma SLN_left: "SLN * P = P" by simp
lemma SLN_right: "P * SLN = P" by simp

lemmas SLN_normalize = SLN_right mult.assoc[symmetric, where 'a=assn]
lemmas SLN_strip = SLN_right SLN_left mult.assoc[symmetric, where 'a=assn]

text {* A query to the frame matcher. Contains the assertions
  P and Q that shall be matched, as well as a frame F, that is not 
  touched. *}

definition [simp]: "FI_QUERY P Q F \<equiv> P \<Longrightarrow>\<^sub>A Q*F"

abbreviation "fi_m_fst M \<equiv> foldr (( * )) (map fst M) emp"
abbreviation "fi_m_snd M \<equiv> foldr (( * )) (map snd M) emp"
abbreviation "fi_m_match M \<equiv> (\<forall>(p,q)\<in>set M. p \<Longrightarrow>\<^sub>A q)"

text {* A result of the frame matcher. Contains a list of matching pairs,
  as well as the unmatched parts of P and Q, and the frame F.
*}
definition [simp]: "FI_RESULT M UP UQ F \<equiv> 
  fi_m_match M \<longrightarrow> (fi_m_fst M * UP \<Longrightarrow>\<^sub>A fi_m_snd M * UQ * F)"

text {* Internal structure used by the frame matcher: 
  m contains the matched pairs; p,q the assertions that still needs to be 
  matched; up,uq the assertions that could not be matched; and f the frame.
  p and q are SLN-delimited syntactic lists. 
*}

definition [simp]: "FI m p q up uq f \<equiv> 
  fi_m_match m \<longrightarrow> (fi_m_fst m * p * up \<Longrightarrow>\<^sub>A fi_m_snd m * q * uq * f)"

text {* Initialize processing of query *}
lemma FI_init: 
  assumes "FI [] (SLN*P) (SLN*Q) SLN SLN F"
  shows "FI_QUERY P Q F"
  using assms by simp

text {* Construct result from internal representation *}
lemma FI_finalize:
  assumes "FI_RESULT m (p*up) (q*uq) f"
  shows "FI m p q up uq f"
  using assms by (simp add: mult.assoc )

text {* Auxiliary lemma to show that all matching pairs together form
  an entailment. This is required for most applications. *}
lemma fi_match_entails:
  assumes "fi_m_match m"
  shows "fi_m_fst m \<Longrightarrow>\<^sub>A fi_m_snd m"
  using assms apply (induct m)
  apply (simp_all split: prod.split_asm add: ent_star_mono)
  done

text {* Internally, the frame matcher tries to match the first assertion
  of q with the first assertion of p. If no match is found, the first
  assertion of p is discarded. If no match for any assertion in p can be
  found, the first assertion of q is discarded. *}

text {* Match *}
lemma FI_match:
  assumes "p \<Longrightarrow>\<^sub>A q"
  assumes "FI ((p,q)#m) (ps*up) (qs*uq) SLN SLN f"
  shows "FI m (ps*p) (qs*q) up uq f"
  using assms unfolding FI_def
  apply (simp add: mult.assoc) 
  by (simp add: mult.left_commute) 

text {* No match *}
lemma FI_p_nomatch:
  assumes "FI m ps (qs*q) (p*up) uq f"
  shows "FI m (ps*p) (qs*q) up uq f"
  using assms unfolding FI_def
  by (simp add: mult.assoc)  

text {* Head of q could not be matched *}
lemma FI_q_nomatch:
  assumes "FI m (SLN*up) qs SLN (q*uq) f"
  shows "FI m SLN (qs*q) up uq f"
  using assms unfolding FI_def
  by (simp add: mult.assoc)  

subsection {* Frame Inference *}
lemma frame_inference_init:
  assumes "FI_QUERY P Q F"
  shows "P \<Longrightarrow>\<^sub>A Q * F"
  using assms by simp

lemma frame_inference_finalize:
  shows "FI_RESULT M F emp F"
  apply simp
  apply rule
  apply (drule fi_match_entails)
  apply (rule ent_star_mono[OF _ ent_refl])
  apply assumption
  done

subsection {* Entailment Solver *}
lemma entails_solve_init:
  "FI_QUERY P Q true \<Longrightarrow> P \<Longrightarrow>\<^sub>A Q * true"
  "FI_QUERY P Q emp \<Longrightarrow> P \<Longrightarrow>\<^sub>A Q"
  by (simp_all add: mult.assoc)  

lemma entails_solve_finalize:
  "FI_RESULT M P emp true"
  "FI_RESULT M emp emp emp"
  by (auto simp add: fi_match_entails intro: ent_star_mono)


named_theorems sep_dflt_simps "Seplogic: Default simplification rules for automated solvers"
named_theorems sep_eintros "Seplogic: Intro rules for entailment solver"
named_theorems sep_heap_rules "Seplogic: VCG heap rules"
named_theorems sep_decon_rules "Seplogic: VCG deconstruct rules"

ML \<open>
structure Seplogic_Auto =
struct


  (***********************************)
  (*          Method Setup           *)
  (***********************************)

  val dflt_simps_modifiers = [
    Args.$$$ "dflt_simps" -- Scan.option Args.add -- Args.colon 
      >> K (Method.modifier (Named_Theorems.add @{named_theorems sep_dflt_simps}) \<^here>),
    Args.$$$ "dflt_simps" -- Scan.option Args.del -- Args.colon 
      >> K (Method.modifier (Named_Theorems.del @{named_theorems sep_dflt_simps}) \<^here>)
  ];
  val heap_modifiers = [
    Args.$$$ "heap" -- Scan.option Args.add -- Args.colon 
      >> K (Method.modifier (Named_Theorems.add @{named_theorems sep_heap_rules}) \<^here>),
    Args.$$$ "heap" -- Scan.option Args.del -- Args.colon 
      >> K (Method.modifier (Named_Theorems.del @{named_theorems sep_heap_rules}) \<^here>)
  ];
  val decon_modifiers = [
    Args.$$$ "decon" -- Scan.option Args.add -- Args.colon 
      >> K (Method.modifier (Named_Theorems.add @{named_theorems sep_decon_rules}) \<^here>),
    Args.$$$ "decon" -- Scan.option Args.del -- Args.colon 
      >> K (Method.modifier (Named_Theorems.del @{named_theorems sep_decon_rules}) \<^here>)
  ];

  val eintros_modifiers = [
    Args.$$$ "eintros" -- Scan.option Args.add -- Args.colon 
      >> K (Method.modifier (Named_Theorems.add @{named_theorems sep_eintros}) \<^here>),
    Args.$$$ "eintros" -- Scan.option Args.del -- Args.colon 
      >> K (Method.modifier (Named_Theorems.del @{named_theorems sep_eintros}) \<^here>)
  ];


  val solve_entails_modifiers = dflt_simps_modifiers @ eintros_modifiers;
  val sep_auto_modifiers = 
    clasimp_modifiers (* @ vcg_modifiers @ eintros_modifiers; *)

  (***********************************)
  (*     Assertion Normalization     *)
  (***********************************)
  (* Find two terms in a list whose key is equal *)
  fun find_similar (key_of:term -> term) (ts:term list) = let
    fun frec _ [] = NONE
    | frec tab (t::ts) = let val k=key_of t in
      if Termtab.defined tab k then
        SOME (the (Termtab.lookup tab k),t)
      else frec (Termtab.update (k,t) tab) ts
    end
  in
    frec Termtab.empty ts
  end;

  (* Perform DFS over term with binary operator opN, threading through
    a state. Atomic terms are transformed by tr. Supports omission of
    terms from the result structure by transforming them to NONE. *)
  fun dfs_opr opN (tr:'state -> term -> ('state*term option)) 
    d (t as ((op_t as Const (fN,_))$t1$t2)) =
    if fN = opN then let
        val (d1,t1') = dfs_opr opN tr d t1;
        val (d2,t2') = dfs_opr opN tr d1 t2;
      in
        case (t1',t2') of
          (NONE,NONE) => (d2,NONE)
        | (SOME t1',NONE) => (d2,SOME t1')
        | (NONE,SOME t2') => (d2,SOME t2')
        | (SOME t1',SOME t2') => (d2,SOME (op_t$t1'$t2'))
      end
    else tr d t
  | dfs_opr _ tr d t = tr d t;
    
  (* Replace single occurrence of (atomic) ot in t by nt. 
    Returns new term or NONE if nothing was removed. *)
  fun dfs_replace_atomic opN ot nt t = let
    fun tr d t = if not d andalso t=ot then (true,SOME nt) else (d,SOME t);
    val (success,SOME t') = dfs_opr opN tr false t; 
  in
    if success then SOME t' else NONE
  end;

  fun assn_simproc_fun ctxt credex = let
    val ([redex],ctxt') = Variable.import_terms true [Thm.term_of credex] ctxt;
    (*val _ = tracing (tr_term redex);*)
    val export = singleton (Variable.export ctxt' ctxt)

    fun mk_star t1 t2 = @{term "( * )::assn \<Rightarrow> _ \<Rightarrow> _"}$t2$t1;

    fun mk_star' NONE NONE = NONE
    | mk_star' (SOME t1) NONE  = SOME t1
    | mk_star' NONE (SOME t2) = SOME t2
    | mk_star' (SOME t1) (SOME t2) = SOME (mk_star t1 t2);

    fun ptrs_key (_$k$_) = k;

    fun remove_term pt t = case
      dfs_replace_atomic @{const_name "Groups.times_class.times"} pt 
        @{term emp} t 
    of
      SOME t' => t';  

    fun normalize t = let

      fun ep_tr (has_true,ps,ptrs) t = case t of 
        Const (@{const_name "pure_assn"},_)$_ 
        => ((has_true,t::ps,ptrs),NONE)
      | Const (@{const_name "sngr_assn"},_)$_$_ 
        => ((has_true,ps,t::ptrs),SOME t)
      | Const (@{const_name "snga_assn"},_)$_$_
        => ((has_true,ps,t::ptrs),SOME t)
      | Const (@{const_name "top_assn"},_)
        => ((true,ps,ptrs),NONE)
      | (inf_op as Const (@{const_name "and_assn"},_))$t1$t2
        => ((has_true,ps,ptrs),SOME (inf_op$normalize t1$normalize t2))
      | _ => ((has_true,ps,ptrs),SOME t);

      fun normalizer t = case dfs_opr @{const_name "Groups.times_class.times"}
        ep_tr (false,[],[]) t 
      of 
        ((has_true,ps,ptrs),rt) => ((has_true,rev ps,ptrs),rt);

      fun normalize_core t = let 
        val ((has_true,pures,ptrs),rt) = normalizer t;
        val similar = find_similar ptrs_key ptrs;
        val true_t = if has_true then SOME @{term "top_assn"} 
          else NONE;
        val pures' = case pures of 
            [] => NONE
          | p::ps => SOME (fold mk_star ps p);
      in
        case similar of NONE => the (mk_star' pures' (mk_star' true_t rt))
        | SOME (t1,t2) => let
            val t_stripped = remove_term t1 (remove_term t2 t);
          in mk_star t_stripped (mk_star t1 t2) end
      end;

      fun skip_ex ((exq as Const (@{const_name "ex_assn"},_))$(Abs (n,ty,t))) =
        exq$Abs (n,ty,skip_ex t)
      | skip_ex t = normalize_core t;

      val (bs,t') = strip_abs t;
      val ty = fastype_of1 (map #2 bs,t');
    in
      if ty = @{typ assn} then
        Logic.rlist_abs (bs,skip_ex t')
      else t
    end;

    (*val _ = tracing (tr_term redex);*)
    val (f,terms) = strip_comb redex;
    val nterms = map (fn t => let
        (*val _ = tracing (tr_term t); *)
        val t'=normalize t; 
        (*val _ = tracing (tr_term t');*)
      in t' end) terms;
    val new_form = list_comb (f,nterms);

    val res_ss = (put_simpset HOL_basic_ss ctxt addsimps @{thms star_aci});
    val result = Option.map (export o mk_meta_eq) (Arith_Data.prove_conv_nohyps
      [simp_tac res_ss 1] ctxt' (redex,new_form)
    );

  in 
    result
  end handle exc =>
    if Exn.is_interrupt exc then Exn.reraise exc
    else
      (tracing ("assn_simproc failed with exception\n:" ^ Runtime.exn_message exc);
        NONE) (* Fail silently *);


  val assn_simproc =
    Simplifier.make_simproc @{context} "assn_simproc"
     {lhss =
      [@{term "h \<Turnstile> P"},
       @{term "P \<Longrightarrow>\<^sub>A Q"},
       @{term "P \<Longrightarrow>\<^sub>t Q"} (*,
       @{term "Hoare_Triple.hoare_triple P c Q"},
       @{term "(P::assn) = Q"} *)],
      proc = K assn_simproc_fun};


  (***********************************)
  (*     Default Simplifications     *)
  (***********************************)

  (* Default simplification. MUST contain assertion normalization!
    Tactic must not fail! *)
  fun dflt_tac ctxt = asm_full_simp_tac
    (put_simpset HOL_ss ctxt
      addsimprocs [assn_simproc] 
      addsimps @{thms norm_assertion_simps}
      addsimps (Named_Theorems.get ctxt @{named_theorems sep_dflt_simps})
      |> fold Splitter.del_split @{thms if_split}
    );


  (***********************************)
  (*         Frame Matcher           *)
  (***********************************)

  (* Do frame matching
    imp_solve_tac - tactic used to discharge first assumption of match-rule
      cf. lemma FI_match.
  *)
  fun match_frame_tac imp_solve_tac ctxt = let
    (* Normalize star-lists *)
    val norm_tac = simp_tac (
      put_simpset HOL_basic_ss ctxt addsimps @{thms SLN_normalize});

    (* Strip star-lists *)
    val strip_tac = 
      simp_tac (put_simpset HOL_basic_ss ctxt addsimps @{thms SLN_strip}) THEN'
      simp_tac (put_simpset HOL_basic_ss ctxt addsimps @{thms SLN_def});

    (* Do a match step *)
    val match_tac = resolve_tac ctxt @{thms FI_match} (* Separate p,q*)
      THEN' SOLVED' imp_solve_tac (* Solve implication *)
      THEN' norm_tac;

    (* Do a no-match step *)
    val nomatch_tac = resolve_tac ctxt @{thms FI_p_nomatch} ORELSE' 
      (resolve_tac ctxt @{thms FI_q_nomatch} THEN' norm_tac);
  in
    resolve_tac ctxt @{thms FI_init} THEN' norm_tac 
    THEN' REPEAT_DETERM' (FIRST' [
      CHANGED o dflt_tac ctxt,
      (match_tac ORELSE' nomatch_tac)])
    THEN' resolve_tac ctxt @{thms FI_finalize} THEN' strip_tac
  end;



  (***********************************)
  (*       Entailment Solver         *)
  (***********************************)

  (* Extract existential quantifiers from entailment goal *)
  fun extract_ex_tac ctxt i st = let
    fun count_ex (Const (@{const_name SepAuto.entails},_)$_$c) = 
      count_ex c RS @{thm HOL.mp}
    | count_ex (Const (@{const_name SepAuto.ex_assn},_)$Abs (_,_,t))
      = count_ex t RS @{thm enorm_exI'}
    | count_ex _ = @{thm imp_refl};

    val concl = Logic.concl_of_goal (Thm.prop_of st) i |> HOLogic.dest_Trueprop;
    val thm = count_ex concl;
  in
    (TRY o REPEAT_ALL_NEW (match_tac ctxt @{thms ent_ex_preI}) THEN'
     resolve_tac ctxt [thm]) i st
  end;


  (* Solve Entailment *)
  fun solve_entails_tac ctxt = let
    val preprocess_entails_tac = 
      dflt_tac ctxt 
      THEN' extract_ex_tac ctxt
      THEN' simp_tac 
        (put_simpset HOL_ss ctxt addsimps @{thms solve_ent_preprocess_simps});

    val match_entails_tac =
      resolve_tac ctxt @{thms entails_solve_init} 
      THEN' match_frame_tac (resolve_tac ctxt @{thms ent_refl}) ctxt
      THEN' resolve_tac ctxt @{thms entails_solve_finalize};
  in
    preprocess_entails_tac
    THEN' (TRY o
      REPEAT_ALL_NEW (match_tac ctxt (rev (Named_Theorems.get ctxt @{named_theorems sep_eintros}))))
    THEN_ALL_NEW (dflt_tac ctxt THEN' 
      TRY o (match_tac ctxt @{thms ent_triv} 
        ORELSE' resolve_tac ctxt @{thms ent_refl}
        ORELSE' match_entails_tac))
  end;



  (***********************************)
  (*        Automatic Solver         *)
  (***********************************)

  fun sep_autosolve_tac do_pre do_post ctxt = let
    val pre_tacs = [
      CHANGED o clarsimp_tac ctxt,
      CHANGED o REPEAT_ALL_NEW (match_tac ctxt @{thms ballI allI impI conjI})
    ];                                
    val main_tacs = [
      (* match_tac ctxt @{thms is_hoare_triple} THEN' CHANGED o vcg_tac ctxt, *)
      match_tac ctxt @{thms is_entails} THEN' CHANGED o solve_entails_tac ctxt
    ];
    val post_tacs = [SELECT_GOAL (auto_tac ctxt)];
    val tacs = (if do_pre then pre_tacs else [])
      @ main_tacs 
      @ (if do_post then post_tacs else []);
  in
    REPEAT_DETERM' (CHANGED o FIRST' tacs)
  end;



end; \<open>struct\<close>


\<close> 



method_setup sep_auto = 
  {* Scan.lift (Args.mode "nopre" -- Args.mode "nopost" -- Args.mode "plain") 
      --| Method.sections Seplogic_Auto.sep_auto_modifiers >>
  (fn ((nopre,nopost),plain) => fn ctxt => SIMPLE_METHOD' (
    CHANGED o Seplogic_Auto.sep_autosolve_tac 
      ((not nopre) andalso (not plain)) 
      ((not nopost) andalso (not plain)) ctxt
  )) *} "Seplogic: Automatic solver"

method_setup solve_entails = {* 
  Method.sections Seplogic_Auto.solve_entails_modifiers >>
  (fn _ => fn ctxt => SIMPLE_METHOD' (
  CHANGED o Seplogic_Auto.solve_entails_tac ctxt
)) *} "Seplogic: Entailment Solver"




lemma "A \<Longrightarrow>\<^sub>A A"
  by solve_entails





lemma hand_commute[simp]: "A \<and>\<^sub>A B = B \<and>\<^sub>A A"
using ent_conjE1 ent_conjE2 ent_conjI ent_iffI by auto

lemma and_extract_pure_left_iff[simp]: "\<up>b \<and>\<^sub>A Q = (emp\<and>\<^sub>AQ)*\<up>b"
  by (cases b) auto

lemma and_extract_pure_left_ctx_iff[simp]: "P*\<up>b \<and>\<^sub>A Q = (P\<and>\<^sub>AQ)*\<up>b"
  by (cases b) auto

lemma and_extract_pure_right_iff[simp]: "P \<and>\<^sub>A \<up>b = (emp\<and>\<^sub>AP)*\<up>b"
  by (cases b) (auto simp: hand_commute)  
  

lemma and_extract_pure_right_ctx_iff[simp]: "P \<and>\<^sub>A Q*\<up>b = (P\<and>\<^sub>AQ)*\<up>b"
  by (cases b) auto

lemma [simp]: "(x \<and>\<^sub>A y) \<and>\<^sub>A z = x \<and>\<^sub>A y \<and>\<^sub>A z"
  sorry

simproc_setup assn_simproc 
  ( "h \<Turnstile> P" | "P\<Longrightarrow>\<^sub>AQ" | "P\<Longrightarrow>\<^sub>tQ" | "(P::assn) = Q" ) 
  = {*K Seplogic_Auto.assn_simproc_fun*}
 
lemma "h \<Turnstile> F * \<up> (a' = None) * F' \<Longrightarrow> G" apply simp oops
lemma "true * true = G" apply simp oops
lemma "G * true * F * true = H"  apply (simp )  oops

lemma "G * \<up>f * true *  F   = H"  apply (simp )   oops

lemma "h \<Turnstile> F \<and>\<^sub>A \<up> (a' = None) * F' \<Longrightarrow> G" apply simp oops

lemma "h \<Turnstile> \<up>t * (F \<and>\<^sub>A \<up> (a' = None) * F') * X \<Longrightarrow> G" apply (simp del:  ) oops


lemma p_c[simp]: "\<up> P * \<up> Q = \<up> (P \<and> Q)" using pure_conj by simp

lemma "\<up>a * B * \<up>c \<Longrightarrow>\<^sub>A G" apply (simp add:  del: pure_conj) oops


lemma "\<exists>\<^sub>Ab. \<up> ((b, a) \<in> R) *C *\<up>a \<Longrightarrow>\<^sub>A emp" apply simp oops


declare mod_ex_dist [simp] 
declare pure_assn_rule [simp] 

thm ent_ex_preI ent_ex_postI


text {* Apply precision rule with frame inference. *}
lemma prec_frame:
  assumes PREC: "precise P"
  assumes M1: "h\<Turnstile>(R1 \<and>\<^sub>A R2)"
  assumes F1: "R1 \<Longrightarrow>\<^sub>A P x p * F1"
  assumes F2: "R2 \<Longrightarrow>\<^sub>A P y p * F2"
  shows "x=y"
  using preciseD[OF PREC] M1 F1 F2  
  by (meson mod_and_dist entailsD)

thm false_absorb 

               

end