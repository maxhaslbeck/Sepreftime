theory SepLog_Automatic
imports "SepLogicTime_RBTreeBasic.SepAuto" 
  "HOL-Eisbach.Eisbach" "../SepLogic_Misc"
begin




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

ML \<open>
structure Seplogic_Auto =
struct

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
  end;
\<close> 

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
lemma "true * true = G" apply simp sorry
lemma "G * true * F * true = H"  apply (simp )  oops

lemma "G * \<up>f * true *  F   = H"  apply (simp )   oops

lemma "h \<Turnstile> F \<and>\<^sub>A \<up> (a' = None) * F' \<Longrightarrow> G" apply simp oops

lemma "h \<Turnstile> \<up>t * (F \<and>\<^sub>A \<up> (a' = None) * F') * X \<Longrightarrow> G" apply (simp del:  ) oops


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