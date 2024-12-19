section \<open>A collection of lemmas, definitions and tactics that aid the certification of the 
CFG-to-DAG phase\<close>

theory BackedgeElim
imports Lang Semantics Util TypeSafety "HOL-Eisbach.Eisbach" "HOL-Eisbach.Eisbach_Tools"
begin

subsection \<open>State equality up to a set\<close>

definition nstate_same_on :: "var_context \<Rightarrow> 'a nstate \<Rightarrow> 'a nstate \<Rightarrow> vname set \<Rightarrow> bool"
  where "nstate_same_on \<Lambda> ns1 ns2 D = ((\<forall>d. d \<notin> D \<longrightarrow> lookup_var \<Lambda> ns1 d = lookup_var \<Lambda> ns2 d) \<and> 
                                            binder_state ns1 = binder_state ns2 \<and>
                                            old_global_state ns1 = old_global_state ns2)"

text \<open>\<^term>\<open>nstate_same_on\<close> is true if two states behave the same on all (named) variables w.r.t. some
variable context (\<^term>\<open>\<Lambda>\<close> here) except those in some fixed set (\<^term>\<open>D\<close> here). We use this to express
that states before and after the CFG-to-DAG phase may differ on the variables modified in the loop 
whenever the executions start a new loop iteration. The havocs of the modified variables at the 
beginning of a loop after the CFG-to-DAG phase can then synchronize the states again fully.\<close>

lemma nstate_same_on_empty: "nstate_same_on \<Lambda> ns1 ns1 {}"
  unfolding nstate_same_on_def
  by simp

lemma nstate_same_on_refl: "nstate_same_on \<Lambda> ns ns D"
  unfolding nstate_same_on_def
  by simp

lemma nstate_same_on_sym: "nstate_same_on \<Lambda> ns1 ns2 D \<Longrightarrow> nstate_same_on \<Lambda> ns2 ns1 D"
  unfolding nstate_same_on_def
  by simp

lemma nstate_same_on_subset: "D1 \<subseteq> D2 \<Longrightarrow> nstate_same_on \<Lambda> ns1 ns2 D1 \<Longrightarrow> nstate_same_on \<Lambda> ns1 ns2 D2"
  unfolding nstate_same_on_def
  by auto

lemma nstate_same_on_subset_2: "nstate_same_on \<Lambda> ns1 ns2 D1 \<Longrightarrow> D1 \<subseteq> D2  \<Longrightarrow> nstate_same_on \<Lambda> ns1 ns2 D2"
  unfolding nstate_same_on_def
  by auto

lemma nstate_same_on_empty_subset: "nstate_same_on \<Lambda> ns1 ns2 {} \<Longrightarrow> nstate_same_on \<Lambda> ns1 ns2 D"
  unfolding nstate_same_on_def
  by auto

lemma nstate_same_on_transitive: "nstate_same_on \<Lambda> ns1 ns2 D \<Longrightarrow> nstate_same_on \<Lambda> ns2 ns3 D \<Longrightarrow> nstate_same_on \<Lambda> ns1 ns3 D"
  unfolding nstate_same_on_def
  by simp

lemma nstate_same_on_transitive_2: "nstate_same_on \<Lambda> ns1 ns2 D \<Longrightarrow> nstate_same_on \<Lambda> ns3 ns2 D \<Longrightarrow> nstate_same_on \<Lambda> ns3 ns4 D \<Longrightarrow> nstate_same_on \<Lambda> ns1 ns4 D"
  unfolding nstate_same_on_def
  by simp

lemma nstate_same_on_update_global:
  assumes "nstate_same_on \<Lambda> ns1 ns2 D"
  shows "nstate_same_on \<Lambda> (ns1\<lparr>global_state := gs\<rparr>) (ns2 \<lparr>global_state := gs\<rparr>) D"  
  unfolding nstate_same_on_def
proof (intro conjI, rule allI, rule impI)
  fix d
  assume "d \<notin> D"
  show "lookup_var \<Lambda> (ns1\<lparr>global_state := gs\<rparr>) d = lookup_var \<Lambda> (ns2\<lparr>global_state := gs\<rparr>) d"
  proof (cases "map_of (snd \<Lambda>) d \<noteq> None")
    case True
    have "lookup_var \<Lambda> ns2 d = lookup_var \<Lambda> ns1 d"
      by (metis (full_types) \<open>d \<notin> D\<close> assms nstate_same_on_def)
    then show ?thesis
      by (metis (no_types) True lookup_var_def nstate.select_convs(3) nstate.surjective nstate.update_convs(2) option.exhaust option.simps(5))
  next
    thm nstate.select_convs(2) nstate.surjective
    case False
    then show ?thesis
      unfolding lookup_var_def
      by (metis nstate.select_convs(2) nstate.surjective nstate.update_convs(2) option.simps(4))
  qed
next
  show "binder_state (ns1\<lparr>global_state := gs\<rparr>) = binder_state (ns2\<lparr>global_state := gs\<rparr>)"
    using assms
    by (simp add: nstate_same_on_def)
next
  show "old_global_state (ns1\<lparr>global_state := gs\<rparr>) = old_global_state (ns2\<lparr>global_state := gs\<rparr>)"
    using assms
    by (simp add: nstate_same_on_def)
qed

lemma nstate_same_on_full_ext_env:
  assumes "nstate_same_on \<Lambda> ns1 ns2 D"
  shows "nstate_same_on \<Lambda> (full_ext_env ns1 v) (full_ext_env ns2 v) D"
  using assms
  unfolding nstate_same_on_def
  by (simp add: lookup_var_binder_upd)

lemma nstate_same_on_update:
  assumes "nstate_same_on \<Lambda> ns1 ns2 (set (h#H))" and "lookup_var \<Lambda> ns1 h = Some v"
  shows "nstate_same_on \<Lambda> ns1 (update_var \<Lambda> ns2 h v) (set H)"
  using assms
  unfolding nstate_same_on_def
  by (simp add: update_var_binder_same update_var_old_global_same)

lemma nstate_same_on_update_2:
  assumes "nstate_same_on \<Lambda> ns1 ns2 D"
  shows "nstate_same_on \<Lambda> (update_var \<Lambda> ns1 h v) (update_var \<Lambda> ns2 h v) D"
  using assms
  unfolding nstate_same_on_def
  by (simp add: update_var_binder_same update_var_old_global_same)

lemma nstate_same_on_update_3:
  assumes "h \<in> D"
  shows "nstate_same_on \<Lambda> ns2 (update_var \<Lambda> ns2 h v) D"
  using assms
  unfolding nstate_same_on_def
  by (simp add: update_var_binder_same update_var_old_global_same)

text \<open>The following lemma reflects that if two states cannot be distinguished w.r.t. a variable context,
then evaluation yields the same value.\<close>
lemma eval_nstate_same_on:
  shows "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e, ns1\<rangle> \<Down> v \<Longrightarrow> nstate_same_on \<Lambda> ns1 ns2 {} \<Longrightarrow> A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e, ns2\<rangle> \<Down> v" and 
        "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>es, ns1\<rangle> [\<Down>] vs \<Longrightarrow> nstate_same_on \<Lambda> ns1 ns2 {} \<Longrightarrow> A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>es, ns2\<rangle> [\<Down>] vs"
proof (induction arbitrary: ns2 and ns2 rule: red_expr_red_exprs.inducts)
  case (RedOld \<Omega> e ns1 v ns2)
  hence "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e, ns2\<lparr>global_state := old_global_state ns1\<rparr>\<rangle> \<Down> v" using nstate_same_on_update_global
    by blast
  thus ?case 
    using RedOld nstate_same_on_def
    by (metis red_expr_red_exprs.RedOld)
next
  case (RedForAllTrue \<Omega> ty e ns1 ns2) 
  thus ?case using nstate_same_on_full_ext_env
    by (metis red_expr_red_exprs.RedForAllTrue)
next
  case (RedForAllFalse \<Omega> ty e ns1 ns2)
   thus ?case using nstate_same_on_full_ext_env
     by (metis red_expr_red_exprs.RedForAllFalse) 
next
 case (RedExistsTrue \<Omega> ty e ns1 ns2)
 thus ?case using nstate_same_on_full_ext_env
   by (metis red_expr_red_exprs.RedExistsTrue) 
next
 case (RedExistsFalse \<Omega> ty e ns1 ns2)
 thus ?case using nstate_same_on_full_ext_env
   by (metis red_expr_red_exprs.RedExistsFalse) 
qed (auto simp: nstate_same_on_def intro: red_expr_red_exprs.intros)

lemma expr_all_sat_nstate_same_on:
  assumes "nstate_same_on \<Lambda> ns1 ns2 {}" and
          "expr_all_sat A \<Lambda> \<Gamma> \<Omega> ns1 posts" 
        shows "expr_all_sat A \<Lambda> \<Gamma> \<Omega> ns2 posts"  
  using assms(2)
  unfolding expr_all_sat_def expr_sat_def
  apply (induction posts)
   apply simp
  using assms(1) eval_nstate_same_on(1)
  by fastforce

subsection \<open>Some lemmas on well-typed states and reductions\<close>

lemma update_var_state_wt:
  assumes "state_well_typed A \<Lambda> \<Omega> ns" and Lookup:"lookup_var_ty \<Lambda> x = Some ty" and TyV:"type_of_val A v = instantiate \<Omega> ty"
  shows "state_well_typed A \<Lambda> \<Omega> (update_var \<Lambda> ns x v)" (is "state_well_typed A \<Lambda> \<Omega> ?ns'")
  proof (cases "map_of (snd \<Lambda>) x = None")
    case True
    with \<open>lookup_var_ty \<Lambda> x = Some ty\<close> have IsGlobal:"lookup_vdecls_ty (fst \<Lambda>) x = Some ty"
      unfolding lookup_vdecls_ty_def       
      using lookup_var_ty_decl_Some lookup_var_decl_global_3
      by (metis (mono_tags, lifting) fst_conv map_option_eq_Some)
    from True have "local_state ?ns' = local_state ns"
      unfolding update_var_def
      by simp
    moreover from IsGlobal \<open>state_well_typed A \<Lambda> \<Omega> ns\<close> have "state_typ_wf A \<Omega> (global_state ?ns') (fst \<Lambda>)"
      unfolding state_typ_wf_def state_well_typed_def
      by (simp add: True global_update TyV)
    ultimately show ?thesis
      unfolding state_well_typed_def
      using state_well_typed_def
      by (metis assms(1) update_var_binder_same update_var_old_global_same)
  next
    case False
    hence IsLocal: "lookup_vdecls_ty (snd \<Lambda>) x = Some ty"
      using lookup_var_decl_local_2 lookup_var_ty_decl_Some[OF \<open>lookup_var_ty \<Lambda> x = Some ty\<close>]
      unfolding lookup_vdecls_ty_def      
      by (metis fst_conv option.simps(9))
    from False have "global_state ?ns' = global_state ns"
      unfolding update_var_def
      by auto
    moreover from \<open>state_well_typed A \<Lambda> \<Omega> ns\<close> have "state_typ_wf A \<Omega> (local_state ?ns') (snd \<Lambda>)"      
      using  IsLocal
      unfolding state_typ_wf_def state_well_typed_def
      by (metis (mono_tags, lifting) False Lookup TyV local_state_update_other lookup_var_decl_local_2 lookup_var_local lookup_var_ty_decl_Some option.simps(9) prod.collapse update_var_same)
     ultimately show ?thesis 
      unfolding state_well_typed_def
      using state_well_typed_def
      by (metis assms(1) update_var_binder_same update_var_old_global_same)
  qed    

fun is_proc_call :: "cmd \<Rightarrow> bool"
  where
    "is_proc_call (ProcCall m args rets) = True"
  | "is_proc_call _ = False"

lemma red_cmd_state_wt_preserve:
  assumes "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>c, Normal ns\<rangle> \<rightarrow> Normal ns'" and "state_well_typed A \<Lambda> \<Omega> ns" and "\<not> (is_proc_call c)"
  shows "state_well_typed A \<Lambda> \<Omega> ns'"
  using assms
proof cases
  case (RedAssign x ty v e)
  then show ?thesis using update_var_state_wt assms by blast 
next
  case (RedHavocNormal x ty w v)
  then show ?thesis using update_var_state_wt assms lookup_var_decl_ty_Some by blast 
qed auto

lemma normal_reduce_aux:
  assumes "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>c, Normal ns\<rangle> \<rightarrow> s''" and "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs, s''\<rangle> [\<rightarrow>] Normal ns'"
  shows "\<exists>ns''. s'' = Normal ns''"
  using assms
  using failure_stays_cmd_list magic_stays_cmd_list state.exhaust by blast

lemma red_cmds_state_wt_preserve_aux:
  assumes "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs, s\<rangle> [\<rightarrow>] s'" and "s = Normal ns" and "s' = Normal ns'" and
          "state_well_typed A \<Lambda> \<Omega> ns" and "list_all (\<lambda>c. \<not> (is_proc_call c)) cs"
  shows "state_well_typed A \<Lambda> \<Omega> ns'"
  using assms
  apply (induction arbitrary: ns ns')
   apply simp
  using red_cmd_state_wt_preserve normal_reduce_aux
  by (metis list_all_simps(1))

lemma red_cmds_state_wt_preserve:
  assumes "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs, Normal ns\<rangle> [\<rightarrow>] Normal ns'"
          "state_well_typed A \<Lambda> \<Omega> ns" and "list_all (\<lambda>c. \<not> (is_proc_call c)) cs"
  shows "state_well_typed A \<Lambda> \<Omega> ns'"
  using assms red_cmds_state_wt_preserve_aux
  by blast

subsection \<open>Helper lemmas to prove the local block lemmas in the CFG-to-DAG phase\<close>

text \<open>The following inductive definition is used to relate blocks before and after the CFG-to-DAG
phase.\<close>

inductive cfg_dag_rel :: "bool \<Rightarrow> vname list \<Rightarrow> expr list \<Rightarrow> expr list \<Rightarrow> cmd list \<Rightarrow> cmd list \<Rightarrow> bool"
  for "cut_edge" :: bool
  where      
     DagRel_Havoc:
     "\<lbrakk>cfg_dag_rel cut_edge H pre_invs post_invs cs1 cs2\<rbrakk> \<Longrightarrow>
     cfg_dag_rel cut_edge (h#H) pre_invs post_invs cs1 (Havoc h # cs2)"
   | DagRel_PreInv:
     "\<lbrakk>cfg_dag_rel cut_edge [] pre_invs post_invs cs1 cs2\<rbrakk> \<Longrightarrow>
     cfg_dag_rel cut_edge [] (e_inv#pre_invs) post_invs (Assert e_inv # cs1) (Assume e_inv # cs2)"
   | DagRel_PreInv_Assume:
     "\<lbrakk>cfg_dag_rel cut_edge [] (e_inv#pre_invs) post_invs cs1 cs2\<rbrakk> \<Longrightarrow>
     cfg_dag_rel cut_edge [] (e_inv#pre_invs) post_invs (Assume e # cs1) (Assume e # cs2)"
(* procedure calls are already desugared in this phase *)
   | DagRel_Main:
     "\<lbrakk>\<not> is_proc_call c; cfg_dag_rel cut_edge [] [] post_invs cs1 cs2\<rbrakk> \<Longrightarrow>
     cfg_dag_rel cut_edge [] [] post_invs (c # cs1) (c # cs2)"
   | DagRel_PostInv:
     "\<lbrakk>cfg_dag_rel cut_edge [] [] post_invs [] cs2\<rbrakk> \<Longrightarrow>
     cfg_dag_rel cut_edge [] [] (e_inv # post_invs) [] (Assert e_inv # cs2)"
   | DagRel_Nil:
     "cfg_dag_rel cut_edge [] [] [] [] []"
   | DagRel_CutEdge:
     "cut_edge \<Longrightarrow> cfg_dag_rel cut_edge [] [] [] [] [Assume (Lit (LBool False))]"

lemma cfg_dag_rel_no_calls_1: "cfg_dag_rel c H pre_invs post_invs cs1 cs2 \<Longrightarrow> list_all (\<lambda>cmd. \<not> is_proc_call cmd) cs1"
  by (induction rule: cfg_dag_rel.induct) auto

lemma cfg_dag_rel_no_calls_2: "cfg_dag_rel c H pre_invs post_invs cs1 cs2 \<Longrightarrow> list_all (\<lambda>cmd. \<not> is_proc_call cmd) cs2"
  by (induction rule: cfg_dag_rel.induct) auto

text \<open>Eisbach tactic to prove two blocks are in the CFG-to-DAG block relation\<close>
method cfg_dag_rel_tac_single uses R_def R_old_def LocVar_assms = 
  (match conclusion in                       
                       "cfg_dag_rel ?cut_edge [] [] ?post_invs (?c#?cs1) (?c#?cs2)" \<Rightarrow> \<open>rule DagRel_Main, simp\<close> \<bar>
                       "cfg_dag_rel ?cut_edge [] [] [] [] [Assume (Lit (LBool False))]" \<Rightarrow> \<open>rule DagRel_CutEdge, simp\<close> \<bar>
                       "cfg_dag_rel ?cut_edge ?H ?pre_invs ?post_invs ?cs1 ?cs2" \<Rightarrow> \<open>rule\<close> \<bar>
                       "_" \<Rightarrow> fail) | (rule DagRel_Nil)

text \<open>Next we prove a series of lemmas that will allow us to prove the main lemma that we use to
prove the local block lemma in the CFG-to-DAG phase\<close>

(* don't support where clauses for now *)
lemma cfg_dag_rel_havoc:
  assumes "cfg_dag_rel c H pre_invs post_invs cs1 cs2" and
          "nstate_same_on \<Lambda> ns1 ns2 (set H)" and
          StateWt:"state_well_typed A \<Lambda> \<Omega> ns1" and
          TyExists:"list_all (\<lambda>x. \<exists>t. lookup_var_decl \<Lambda> x = Some (t, None)) H"
        shows "(\<exists>cs2A cs2B ns1'. cs2 = cs2A@cs2B \<and> nstate_same_on \<Lambda> ns1 ns1' {} \<and> (A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs2A, Normal ns2\<rangle> [\<rightarrow>] Normal ns1') \<and> cfg_dag_rel c [] pre_invs post_invs cs1 cs2B)"
  using assms
proof (induction arbitrary: ns2)
  case (DagRel_Havoc H pre_invs post_invs cs1 cs2 h)  
  hence TyH:"list_all (\<lambda>x. \<exists>t. lookup_var_decl \<Lambda> x = Some (t, None)) H" by simp
  from \<open>list_all (\<lambda>x. \<exists>t. lookup_var_decl \<Lambda> x = Some (t, None)) (h # H)\<close> obtain \<tau> where LookupH:"lookup_var_decl \<Lambda> h = Some (\<tau>,None)" by auto
  from this obtain v where "lookup_var \<Lambda> ns1 h = Some v" and TyV: "type_of_val A v = instantiate \<Omega> \<tau>"
    using StateWt state_well_typed_def state_typ_wf_lookup lookup_var_decl_ty_Some by blast  
  let ?ns2 = "update_var \<Lambda> ns2 h v"
  have HavocRed:"A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>Havoc h, Normal ns2\<rangle> \<rightarrow> Normal ?ns2"
    using RedHavocNormal LookupH TyV
    by blast
  have "nstate_same_on \<Lambda> ns1 ?ns2 (set H)"
    using nstate_same_on_update[OF \<open>nstate_same_on \<Lambda> ns1 ns2 (set (h # H))\<close> \<open>lookup_var \<Lambda> ns1 h = Some v\<close>]
    by simp
  from this TyH StateWt DagRel_Havoc.IH obtain cs2A cs2B ns1' where
    "cs2 = cs2A @ cs2B" and
    FinalStateSame:"nstate_same_on \<Lambda> ns1 ns1' {}" and
    RedRest:"A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs2A,Normal ?ns2\<rangle> [\<rightarrow>] Normal ns1'" and 
    RelRest:"cfg_dag_rel c [] pre_invs post_invs cs1 cs2B"
    by blast
  show ?case
    apply (rule exI[where ?x="[Havoc h]@cs2A"], rule exI[where ?x=cs2B], rule exI[where ?x=ns1'])
    apply (intro conjI)
    using \<open>cs2 = cs2A @ cs2B\<close> apply simp
    apply (rule FinalStateSame)
    using HavocRed RedRest 
    using RedCmdListCons apply fastforce
    using RelRest by simp
qed (auto intro: RedCmdListNil cfg_dag_rel.intros)

lemma cfg_dag_rel_pre_invs:
  assumes "cfg_dag_rel c H pre_invs post_invs cs1 cs2" and
          "H = []" and
          "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs1, Normal ns1\<rangle> [\<rightarrow>] s'" and
          "nstate_same_on \<Lambda> ns1 ns2 {}" and
          "list_all (expr_sat A \<Lambda> \<Gamma> \<Omega> ns1) pre_invs"
  shows "(\<exists> cs1A cs1B cs2A cs2B s''. cs1 = cs1A@cs1B \<and> cs2 = cs2A@cs2B \<and>  
   (A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs1A, Normal ns1\<rangle> [\<rightarrow>] s'') \<and> (A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs1B, s''\<rangle> [\<rightarrow>] s') \<and> 
    s'' \<noteq> Failure \<and>
   (s'' \<noteq> Magic \<longrightarrow> s'' = Normal ns1 \<and> cfg_dag_rel c [] [] post_invs cs1B cs2B \<and>
                    (A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs2A, Normal ns2\<rangle> [\<rightarrow>] Normal ns2)))"
  using assms
proof (induction)
  case (DagRel_PreInv pre_invs post_invs cs1 cs2 e_inv)
  hence InvHolds:"A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e_inv, ns1\<rangle> \<Down> BoolV True" using expr_sat_def
    by (simp add: expr_sat_def RedAssertOk)
  with \<open>A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>Assert e_inv # cs1,Normal ns1\<rangle> [\<rightarrow>] s'\<close>
  have RedAssertInv:"A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>Assert e_inv, Normal ns1\<rangle> \<rightarrow> Normal ns1" and 
       RedCs1:"A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs1, Normal ns1\<rangle> [\<rightarrow>] s'"
    by (auto elim: assert_ml intro:  RedAssertOk)  
  with DagRel_PreInv obtain cs1A cs1B cs2A cs2B s'' where
    "cs1 = cs1A @ cs1B" and "cs2 = cs2A @ cs2B" and
    RedCs1A:"A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs1A,Normal ns1\<rangle> [\<rightarrow>] s''" and RedCs1B:"A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs1B, s''\<rangle> [\<rightarrow>] s'"    
    "s'' \<noteq> Failure" and NotMagic:"(s'' \<noteq> Magic \<longrightarrow> s'' = Normal ns1 \<and> cfg_dag_rel c [] [] post_invs cs1B cs2B \<and> 
                                       (A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs2A,Normal ns2\<rangle> [\<rightarrow>] Normal ns2))"
    by fastforce        
  show ?case
  proof (cases "s'' = Magic")
    case True
    show ?thesis 
    apply (rule exI[where ?x="Assert e_inv # cs1A"])
    apply (rule exI[where ?x="cs1B"])
    apply (rule exI[where ?x="Assume e_inv # cs2A"])
      apply (rule exI[where ?x=cs2B])
      apply (rule exI[where ?x= Magic])
      apply (intro conjI)
      using \<open>cs1 = cs1A @ cs1B\<close> apply simp
      using \<open>cs2 = cs2A @ cs2B\<close> apply simp          
      using RedAssertInv RedCs1A RedCmdListCons True apply blast
      using RedCs1B True by auto
  next
    case False
    hence "s'' = Normal ns1" and RedCs2A:"(A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs2A, Normal ns2\<rangle> [\<rightarrow>] Normal ns2)" and
          RelRest:"cfg_dag_rel c [] [] post_invs cs1B cs2B"
      using NotMagic by auto
    show ?thesis
    apply (rule exI[where ?x="Assert e_inv # cs1A"])
    apply (rule exI[where ?x="cs1B"])
    apply (rule exI[where ?x="Assume e_inv # cs2A"])
      apply (rule exI[where ?x=cs2B])
      apply (rule exI[where ?x="Normal ns1"])
      apply (intro conjI)
      using \<open>cs1 = cs1A @ cs1B\<close> apply simp
      using \<open>cs2 = cs2A @ cs2B\<close> apply simp
      using RedAssertInv RedCmdListCons RedCs1A \<open>s'' = Normal ns1\<close> apply blast
      using RedCs1B \<open>s'' = Normal ns1\<close> apply auto[1]
       apply simp
      using InvHolds RedCs2A RedCmdListCons RedAssumeOk RelRest
      by (metis assms(4) eval_nstate_same_on(1))
  qed
next
  case (DagRel_PreInv_Assume e_inv pre_invs post_invs cs1 cs2 e)
  then show ?case
  proof (cases "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e, ns1\<rangle> \<Down> BoolV True")
    case True
    hence RedAssumeE:"A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>Assume e, Normal ns1\<rangle> \<rightarrow> Normal ns1"
      by (auto intro: red_cmd.intros)
    hence "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs1, Normal ns1\<rangle> [\<rightarrow>] s'"
      using \<open>A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>Assume e # cs1,Normal ns1\<rangle> [\<rightarrow>] s'\<close>
      by (metis RedCmdListCons_case assume_determ)
    with DagRel_PreInv_Assume obtain cs1A cs1B cs2A cs2B s'' where
        A: "cs1 = cs1A @ cs1B"  "cs2 = cs2A @ cs2B"
       "(A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs1A,Normal ns1\<rangle> [\<rightarrow>] s'')" 
       "(A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs1B,s''\<rangle> [\<rightarrow>] s')" 
       "s'' \<noteq> Failure" 
      "(s'' \<noteq> Magic \<longrightarrow> s'' = Normal ns1 \<and> cfg_dag_rel c [] [] post_invs cs1B cs2B \<and> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs2A,Normal ns2\<rangle> [\<rightarrow>] Normal ns2)"
      by fastforce
    have RedAssumeE2:"A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>Assume e, Normal ns2\<rangle> \<rightarrow> Normal ns2" using True \<open>nstate_same_on \<Lambda> ns1 ns2 {}\<close>
      using RedAssumeOk eval_nstate_same_on(1) by blast
    show ?thesis 
      apply (rule exI[where ?x="(Assume e)#cs1A"])
      apply (rule exI[where ?x=cs1B])
      apply (rule exI[where ?x="(Assume e)#cs2A"])
      apply (rule exI[where ?x=cs2B])
      apply (rule exI[where ?x=s''])
      apply (intro conjI)
      using A RedAssumeE RedAssumeE2
      by (auto intro: red_cmd.intros RedCmdListCons)      
  next
    case False
    hence InvFalse:"A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e,ns1\<rangle> \<Down> BoolV False" using \<open>A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>Assume e # cs1,Normal ns1\<rangle> [\<rightarrow>] s'\<close>
      by (metis (full_types) RedCmdListCons_case assume_red_bool)     
    show ?thesis
      apply (rule exI[where ?x="[Assume e]"])
      apply (rule exI[where ?x=cs1])
      apply (rule exI[where ?x="[Assume e]"])
      apply (rule exI[where ?x=cs2])
      apply (rule exI[where ?x=Magic])
      apply (intro conjI)
      using InvFalse 
            apply simp
          apply simp
      using InvFalse 
         apply (meson RedAssumeMagic RedCmdListCons RedCmdListNil)
        apply (metis \<open>A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>Assume e # cs1,Normal ns1\<rangle> [\<rightarrow>] s'\<close> False assume_ml magic_red_cmd_list)
      by auto
  qed
next
  case (DagRel_Main post_invs cs1 cs2 c)
  show ?case
    apply (rule exI[where ?x="[]"])
    using DagRel_Main
      by (auto intro: RedCmdListNil cfg_dag_rel.DagRel_Main)
qed (auto intro: RedCmdListNil cfg_dag_rel.intros simp: nstate_same_on_def)

lemma red_cmd_nstate_same_on:
  assumes "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>c, Normal ns1\<rangle> \<rightarrow> s'" and
          "nstate_same_on \<Lambda> ns1 ns2 {}" and
          "\<not> (is_proc_call c)"
  shows "(((s' = Failure) \<or> (s' = Magic)) \<longrightarrow> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>c, Normal ns2\<rangle> \<rightarrow> s') \<and>
         (\<forall>ns1'. s' = Normal ns1' \<longrightarrow> (\<exists>ns2'. nstate_same_on \<Lambda> ns1' ns2' {} \<and> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>c, Normal ns2\<rangle> \<rightarrow> Normal ns2'))"
  using assms
proof cases
  case (RedAssertOk e)
   then show ?thesis 
  using assms(2) eval_nstate_same_on(1) red_cmd.RedAssertOk by blast
next
  case (RedAssertFail e)
  then show ?thesis 
  using assms(2) eval_nstate_same_on(1) red_cmd.RedAssertFail by blast
next
  case (RedAssumeOk e)
  then show ?thesis 
    using assms(2) eval_nstate_same_on(1) red_cmd.RedAssumeOk by blast
next
  case (RedAssumeMagic e)
  then show ?thesis 
    using assms(2) eval_nstate_same_on(1) red_cmd.RedAssumeMagic by blast
next
  case (RedAssign x ty v e)
  then show ?thesis using nstate_same_on_update_2
  by (metis assms(2) eval_nstate_same_on(1) red_cmd.RedAssign state.distinct(1) state.distinct(3) state.inject)
next
  case (RedHavocNormal x ty w v)
  then show ?thesis using nstate_same_on_update_2[OF assms(2)]
    using red_cmd.RedHavocNormal eval_nstate_same_on(1)
    by (metis (full_types) assms(2) state.distinct(1) state.distinct(3) state.inject)
next
  case (RedHavocMagic x ty cond v)
  then show ?thesis
  by (metis assms(2) eval_nstate_same_on(1) nstate_same_on_update_2 red_cmd.RedHavocMagic state.distinct(3))
qed (auto)

lemma cfg_dag_rel_same:
  assumes "cfg_dag_rel c H pre_invs post_invs cs1 cs2" and
          "H = []" and
          "pre_invs = []" and
          "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs1, Normal ns1\<rangle> [\<rightarrow>] s'" and         
          "nstate_same_on \<Lambda> ns1 ns2 {}" and
          "\<And> s2'. A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs2, Normal ns2\<rangle> [\<rightarrow>] s2' \<Longrightarrow> s2' \<noteq> Failure"
  shows "\<exists>cs2A cs2B. cs2 = cs2A@cs2B \<and>   
    s' \<noteq> Failure \<and> 
    (\<forall>ns1'. s' = Normal ns1' \<longrightarrow> (\<exists>ns2'. nstate_same_on \<Lambda> ns1' ns2' {} \<and> cfg_dag_rel c [] [] post_invs [] cs2B \<and> (A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs2A, Normal ns2\<rangle> [\<rightarrow>] Normal ns2')))"
  using assms
proof (induction arbitrary: ns1 ns2)
  case (DagRel_Main cmd post_invs cs1 cs2)
  from this obtain s'' where
    RedC1:"A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cmd, Normal ns1\<rangle> \<rightarrow> s''" and RedCs1: "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs1, s''\<rangle> [\<rightarrow>] s'"
    by auto
  show ?case 
  proof (cases s'')
    case (Normal ns1'')
    from this obtain ns2'' where RedCmd2:"A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cmd, Normal ns2\<rangle> \<rightarrow> Normal ns2''" and "nstate_same_on \<Lambda> ns1'' ns2'' {}"
      using DagRel_Main.hyps(1) \<open> nstate_same_on \<Lambda> ns1 ns2 {}\<close> RedC1 red_cmd_nstate_same_on by blast
    hence "(\<And>s2'. A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs2,Normal ns2''\<rangle> [\<rightarrow>] s2' \<Longrightarrow> s2' \<noteq> Failure)"
      using DagRel_Main.prems(5) RedCmdListCons by blast
    with DagRel_Main.IH RedCs1 Normal \<open>nstate_same_on \<Lambda> ns1'' ns2'' {}\<close> obtain cs2A cs2B where 
     Rec:"cs2 = cs2A @ cs2B" "s' \<noteq> Failure" 
         "\<forall>ns1'. s' = Normal ns1' \<longrightarrow> (\<exists>ns2'. nstate_same_on \<Lambda> ns1' ns2' {} \<and> cfg_dag_rel c [] [] post_invs [] cs2B \<and> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs2A,Normal ns2''\<rangle> [\<rightarrow>] Normal ns2')"
      by metis    
    show ?thesis 
      apply (rule exI[where ?x = "(cmd)#cs2A"])
      apply (rule exI[where ?x = "cs2B"])
      using Rec RedCmd2 
      by (metis RedCmdListCons append_Cons)      
  next
    case Failure
    then show ?thesis 
      by (metis DagRel_Main.hyps(1) DagRel_Main.prems(4) DagRel_Main.prems(5) RedC1 failure_red_cmd_list red_cmd_list.simps red_cmd_nstate_same_on)
  next
    case Magic
    hence "s' = Magic" using RedCs1
      by (simp add: magic_stays_cmd_list)
    thus ?thesis 
      by auto     
  qed
next
 case (DagRel_PostInv post_invs cs2 e_inv)
  then show ?case 
    by (metis (full_types) RedCmdListNil append.left_neutral cfg_dag_rel.DagRel_PostInv nil_cmd_elim state.distinct(1) state.inject)
next
  case  DagRel_CutEdge
  then show ?case     
    by (metis RedCmdListNil append.left_neutral cfg_dag_rel.DagRel_CutEdge nil_cmd_elim state.distinct(1) state.inject)
qed (auto intro: RedCmdListNil cfg_dag_rel.intros)

lemma cfg_dag_rel_post_invs:
  assumes "cfg_dag_rel c H pre_invs post_invs cs1 cs2" and
          "H = []" and "pre_invs = []" and "cs1 = []"
          "\<And> s2'. A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs2, Normal ns\<rangle> [\<rightarrow>] s2' \<Longrightarrow> s2' \<noteq> Failure" and
          "list_all (\<lambda>inv. \<exists>b. A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>inv, ns\<rangle> \<Down> BoolV b) post_invs"
  shows "\<exists> cs2A cs2B.  cs2 = cs2A@cs2B \<and> 
    cfg_dag_rel c [] [] [] [] cs2B \<and> 
    (A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs2A, Normal ns\<rangle> [\<rightarrow>] Normal ns) \<and>
    list_all (expr_sat A \<Lambda> \<Gamma> \<Omega> ns) post_invs"
  using assms
proof induction
  case (DagRel_PostInv post_invs cs2 e_inv)
  from this obtain b where "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e_inv,ns\<rangle> \<Down> (BoolV b)" by auto
  with DagRel_PostInv obtain s'' where Red1:"A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>Assert e_inv, Normal ns\<rangle> \<rightarrow> s''"
    by (metis (full_types) RedAssertFail RedAssertOk)
  hence Normal:"s'' = Normal ns" using \<open>\<And>s2'. A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>Assert e_inv # cs2,Normal ns\<rangle> [\<rightarrow>] s2' \<Longrightarrow> s2' \<noteq> Failure\<close>
    by (metis (full_types) RedAssertFail RedCmdListCons \<open>A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e_inv,ns\<rangle> \<Down> BoolV b\<close> assert_correct failure_red_cmd_list)
  with Red1 DagRel_PostInv obtain cs2A cs2B where
    Rec:"cs2 = cs2A @ cs2B \<and> cfg_dag_rel c [] [] [] [] cs2B \<and> (A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs2A,Normal ns\<rangle> [\<rightarrow>] Normal ns) \<and> list_all (expr_sat A \<Lambda> \<Gamma> \<Omega> ns) post_invs"
    by (metis RedCmdListCons list.pred_inject(2))
  show ?case
    apply (rule exI[where ?x="Assert e_inv # cs2A"])
    apply (rule exI[where ?x=cs2B])
    using Red1 Normal Rec 
    unfolding expr_sat_def 
    by (auto intro: RedCmdListCons)
qed (auto intro: RedCmdListNil cfg_dag_rel.intros)

lemma cfg_dag_rel_post_invs_2:
  assumes "\<And> s2'. A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs2, Normal ns\<rangle> [\<rightarrow>] s2' \<Longrightarrow> s2' \<noteq> Failure" and
          "list_all (\<lambda>inv. \<exists>b. A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>inv, ns\<rangle> \<Down> BoolV b) post_invs" and
          "cfg_dag_rel c [] [] post_invs [] cs2" 
        shows "list_all (expr_sat A \<Lambda> \<Gamma> \<Omega> ns) post_invs"
  using assms cfg_dag_rel_post_invs
  by blast

lemma cfg_dag_rel_post_invs_3:
  assumes Red:"\<And>m2' s2'. (A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl m, Normal ns) -n\<rightarrow>* (m2', s2')) \<Longrightarrow> s2' \<noteq> Failure" and
          Block:"node_to_block G ! m = cs"
          "list_all (\<lambda>inv. \<exists>b. A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>inv, ns\<rangle> \<Down> BoolV b) post_invs"
          "cfg_dag_rel c [] [] post_invs [] cs" 
    shows "list_all (expr_sat A \<Lambda> \<Gamma> \<Omega> ns) post_invs"
proof -
  from Red Block have "\<And> s2'. A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs, Normal ns\<rangle> [\<rightarrow>] s2' \<Longrightarrow> s2' \<noteq> Failure"
    using RedFailure by blast
  thus ?thesis
    using cfg_dag_rel_post_invs_2 assms(3-)
    by blast
qed

lemma cfg_dag_rel_no_proc_calls:
  assumes "cfg_dag_rel c H pre_invs post_invs cs1 cs2"
  shows "list_all (\<lambda>c. \<not> is_proc_call c) cs2"
  using assms
  by (induction) auto

text \<open>The following lemma is the main lemma used to prove the local block lemma in the CFG-to-DAG 
phase. The lemma is in "expanded" form. Below we prove another version that hides some parts in 
definitions, which is easier to use in the actual proofs.\<close>

lemma dag_rel_block_lemma:
  assumes Red:"A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs1, Normal ns1\<rangle> [\<rightarrow>] s'" and
          InvsHold:"list_all (expr_sat A \<Lambda> \<Gamma> \<Omega> ns1) pre_invs" and
          DagVerifies:"\<And>s2'. A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs2, Normal ns2\<rangle> [\<rightarrow>] s2' \<Longrightarrow> s2' \<noteq> Failure" and
          SameModH:"nstate_same_on \<Lambda> ns1 ns2 (set H)" and
          Rel:"cfg_dag_rel c H pre_invs post_invs cs1 cs2" and
          StateWt:"state_well_typed A \<Lambda> \<Omega> ns1" and
          StateWt2: "state_well_typed A \<Lambda> \<Omega> ns2" and
          TyExists:"list_all (\<lambda>x. \<exists>t. lookup_var_decl \<Lambda> x = Some (t, None)) H" and
          PostInvsReduce: "\<And>ns. state_well_typed A \<Lambda> \<Omega> ns \<Longrightarrow> list_all (\<lambda>inv. \<exists>b. A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>inv, ns\<rangle> \<Down> BoolV b) post_invs"
        shows "s' \<noteq> Failure \<and> 
              (\<forall>ns1'. s' = Normal ns1' \<longrightarrow> state_well_typed A \<Lambda> \<Omega> ns1' \<and> list_all (expr_sat A \<Lambda> \<Gamma> \<Omega> ns1') post_invs \<and> 
                 (\<exists>ns2'. nstate_same_on \<Lambda> ns1' ns2' {} \<and> state_well_typed A \<Lambda> \<Omega> ns2' \<and>
                         (\<not>c \<longrightarrow> (A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs2, Normal ns2\<rangle> [\<rightarrow>] Normal ns2'))))"
proof -
  from cfg_dag_rel_havoc[OF Rel SameModH StateWt TyExists] obtain cs2A cs2B ns2' where
    "cs2 = cs2A@cs2B" and StateRel1:"nstate_same_on \<Lambda> ns1 ns2' {}" and A2Red1:"A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs2A, Normal ns2\<rangle> [\<rightarrow>] Normal ns2'"
    and RelHavoc:"cfg_dag_rel c [] pre_invs post_invs cs1 cs2B"
    by metis

  with StateWt2 have StateWtNs2':"state_well_typed A \<Lambda> \<Omega> ns2'" using cfg_dag_rel_no_calls_2 red_cmds_state_wt_preserve Rel
    by (metis list_all_append)

  from cfg_dag_rel_pre_invs[OF RelHavoc _ Red StateRel1 InvsHold] obtain cs1A cs1B cs2A' cs2B' s'' where
    "cs1 = cs1A@cs1B" and "cs2B = cs2A'@cs2B'" and 
    A1Red1:"(A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs1A, Normal ns1\<rangle> [\<rightarrow>] s'')" and A1Red2:"(A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs1B, s''\<rangle> [\<rightarrow>] s')" and
    "s'' \<noteq> Failure" and
    NotMagic1:"(s'' \<noteq> Magic \<longrightarrow> s'' = Normal ns1 \<and> cfg_dag_rel c [] [] post_invs cs1B cs2B' \<and> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs2A',Normal ns2'\<rangle> [\<rightarrow>] Normal ns2')"
    by metis

  show ?thesis
  proof (cases "s'' = Magic")
    case True
    then show ?thesis using A1Red2
      using magic_stays_cmd_list by blast
  next
    case False
    hence "s'' = Normal ns1" and RelPreInvs:"cfg_dag_rel c [] [] post_invs cs1B cs2B'" and 
          A2Red2:"A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs2A',Normal ns2'\<rangle> [\<rightarrow>] Normal ns2'"
      using NotMagic1
      by auto
    hence A1Red2Normal:"(A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs1B, Normal ns1\<rangle> [\<rightarrow>] s')" using A1Red2 by simp
   
    from A2Red1 A2Red2 have A2Red3:"A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs2A@cs2A',Normal ns2\<rangle> [\<rightarrow>] Normal ns2'"
      using red_cmd_list_append by blast
    have "cs2 = (cs2A@cs2A')@cs2B'" using \<open>cs2 = cs2A@cs2B\<close> and \<open>cs2B = cs2A'@cs2B'\<close> by simp
    with A2Red3 have DagVerifies2:"\<And>s2'. A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs2B', Normal ns2'\<rangle> [\<rightarrow>] s2' \<Longrightarrow> s2' \<noteq> Failure"
      using DagVerifies red_cmd_list_append
      by blast
    
    from cfg_dag_rel_same[OF RelPreInvs _ _ A1Red2Normal StateRel1 DagVerifies2]  obtain cs2A'' cs2B''
      where "cs2B' = cs2A'' @ cs2B''" 
       "s' \<noteq> Failure" and
       Normal1:"(\<forall>ns1'. s' = Normal ns1' \<longrightarrow> (\<exists>ns2'a. nstate_same_on \<Lambda> ns1' ns2'a {} \<and> cfg_dag_rel c [] [] post_invs [] cs2B'' \<and> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs2A'',Normal ns2'\<rangle> [\<rightarrow>] Normal ns2'a))"
      by blast
  
    show ?thesis
    proof (rule conjI[OF \<open>s' \<noteq> Failure\<close>], rule allI, rule impI)
      fix ns'
      assume "s' = Normal ns'"
      with Red StateWt Rel have StateWtNs':"state_well_typed A \<Lambda> \<Omega> ns'" using cfg_dag_rel_no_calls_1 red_cmds_state_wt_preserve
        by blast
        
      from \<open>s' = Normal ns'\<close> obtain ns2'' where 
        StateRel2:"nstate_same_on \<Lambda> ns' ns2'' {}" and RelSame:"cfg_dag_rel c [] [] post_invs [] cs2B''" and 
        A2Red4:"A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs2A'',Normal ns2'\<rangle> [\<rightarrow>] Normal ns2''"
        using Normal1 by auto
  
      with \<open>cs2B' = cs2A'' @ cs2B''\<close>
      have DagVerifies3: "\<And>s2'. A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs2B'', Normal ns2''\<rangle> [\<rightarrow>] s2' \<Longrightarrow> s2' \<noteq> Failure"
      using DagVerifies2 red_cmd_list_append
      by blast
  
      have "list_all (\<lambda>c. \<not> is_proc_call c) cs2" using cfg_dag_rel_no_proc_calls[OF Rel] by simp
      hence NoProcCallPrefix:"list_all (\<lambda>c. \<not> is_proc_call c) ((cs2A @ cs2A')@cs2A'')"
        using \<open>cs2 = (cs2A@cs2A')@cs2B'\<close> \<open>cs2B' = cs2A'' @ cs2B''\<close>
        by simp
      from A2Red3 A2Red4 have "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(cs2A @ cs2A')@cs2A'',Normal ns2\<rangle> [\<rightarrow>] Normal ns2''"
        using red_cmd_list_append by blast
      with StateWtNs2' A2Red4 NoProcCallPrefix have StateWt2:"state_well_typed A \<Lambda> \<Omega> ns2''"
        using list_all_append red_cmds_state_wt_preserve_aux by blast
        
      from cfg_dag_rel_post_invs[OF RelSame _ _ _ DagVerifies3 PostInvsReduce[OF StateWt2]] obtain cs2A''' cs2B'''
        where "cs2B'' = cs2A''' @ cs2B'''" and
        RelPostInv:"cfg_dag_rel c [] [] [] [] cs2B'''" and
        A2Red5:"(A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs2A''', Normal ns2''\<rangle> [\<rightarrow>] Normal ns2'')" and
        PostInvsHold:"list_all (expr_sat A \<Lambda> \<Gamma> \<Omega> ns2'') post_invs"
        by blast
      have "list_all (expr_sat A \<Lambda> \<Gamma> \<Omega> ns') post_invs" 
        apply (rule List.List.list.pred_mono_strong)
        apply (rule PostInvsHold)
        unfolding expr_sat_def
        using StateRel2 eval_nstate_same_on(1) nstate_same_on_sym by blast
     
      show "state_well_typed A \<Lambda> \<Omega> ns' \<and> list_all (expr_sat A \<Lambda> \<Gamma> \<Omega> ns') post_invs \<and> 
           ((\<exists>ns2'. nstate_same_on \<Lambda> ns' ns2' {} \<and> state_well_typed A \<Lambda> \<Omega> ns2' \<and>
               (\<not> c \<longrightarrow> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs2,Normal ns2\<rangle> [\<rightarrow>] Normal ns2')))"
      proof (rule conjI[OF StateWtNs' conjI[OF _ exI]])
        show "list_all (expr_sat A \<Lambda> \<Gamma> \<Omega> ns') post_invs" 
          apply (rule List.List.list.pred_mono_strong)
          apply (rule PostInvsHold)
          unfolding expr_sat_def
          using StateRel2 eval_nstate_same_on(1) nstate_same_on_sym by blast
      next
        from RelPostInv have "\<not>c \<Longrightarrow> cs2B''' = []"
          by (cases) auto
        show "nstate_same_on \<Lambda> ns' ns2'' {} \<and> state_well_typed A \<Lambda> \<Omega> ns2'' \<and> (\<not> c \<longrightarrow> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs2,Normal ns2\<rangle> [\<rightarrow>] Normal ns2'')"
          apply (rule conjI[OF StateRel2])
          apply (rule conjI[OF StateWt2])
          apply (rule impI)
          using  \<open>cs2 = (cs2A@cs2A')@cs2B'\<close> \<open>cs2B' = cs2A'' @ cs2B''\<close> \<open>cs2B'' = cs2A''' @ cs2B'''\<close>  A2Red3 A2Red4 A2Red5
          by (metis \<open>\<not> c \<Longrightarrow> cs2B''' = []\<close> append.right_neutral red_cmd_list_append)
        qed
      qed
    qed
  qed

definition dag_lemma_assms :: "'a absval_ty_fun \<Rightarrow> var_context \<Rightarrow> 
                   'a fun_interp \<Rightarrow> rtype_env \<Rightarrow> vname list \<Rightarrow> expr list \<Rightarrow> 
                    'a nstate \<Rightarrow> 'a nstate \<Rightarrow> bool"
  where "dag_lemma_assms A \<Lambda> \<Gamma> \<Omega> H pre_invs ns1 ns2 \<equiv> 
         (list_all (expr_sat A \<Lambda> \<Gamma> \<Omega> ns1) pre_invs) \<and>
          (nstate_same_on \<Lambda> ns1 ns2 (set H)) \<and>
          state_well_typed A \<Lambda> \<Omega> ns1 \<and>
          state_well_typed A \<Lambda> \<Omega> ns2"

lemma dag_lemma_assms_state_wt_1: "dag_lemma_assms A \<Lambda> \<Gamma> \<Omega> H pre_invs ns1 ns2 \<Longrightarrow> state_well_typed A \<Lambda> \<Omega> ns1"
  unfolding dag_lemma_assms_def
  by simp

lemma dag_lemma_assms_state_wt_2: "dag_lemma_assms A \<Lambda> \<Gamma> \<Omega> H pre_invs ns1 ns2 \<Longrightarrow> state_well_typed A \<Lambda> \<Omega> ns2"
  unfolding dag_lemma_assms_def
  by simp

lemma dag_lemma_assms_same: "state_well_typed A \<Lambda> \<Omega> ns1 \<Longrightarrow> dag_lemma_assms A \<Lambda> \<Gamma> \<Omega> [] [] ns1 ns1"
  unfolding dag_lemma_assms_def
  by (auto simp: nstate_same_on_empty)

lemma dag_lemma_assms_subset:
  assumes "set H \<subseteq> set H'" and "dag_lemma_assms A \<Lambda> \<Gamma> \<Omega> H pre_invs ns1 ns2"
  shows "dag_lemma_assms A \<Lambda> \<Gamma> \<Omega> H' pre_invs ns1 ns2"
  using assms
  unfolding dag_lemma_assms_def
  using nstate_same_on_subset
  by blast

definition dag_lemma_conclusion :: "'a absval_ty_fun \<Rightarrow> mbodyCFG proc_context \<Rightarrow> var_context \<Rightarrow> 
                   'a fun_interp \<Rightarrow> rtype_env \<Rightarrow> expr list \<Rightarrow>
                    cmd list \<Rightarrow> 'a nstate \<Rightarrow> 'a state \<Rightarrow> bool \<Rightarrow> bool"
  where "dag_lemma_conclusion A M \<Lambda> \<Gamma> \<Omega> post_invs cs2 ns2 s' c \<equiv>
               s' \<noteq> Failure \<and> 
              (\<forall>ns1'. s' = Normal ns1' \<longrightarrow> state_well_typed A \<Lambda> \<Omega> ns1' \<and> list_all (expr_sat A \<Lambda> \<Gamma> \<Omega> ns1') post_invs \<and> 
                 (\<exists>ns2'. nstate_same_on \<Lambda> ns1' ns2' {} \<and> state_well_typed A \<Lambda> \<Omega> ns2' \<and>
                         (\<not>c \<longrightarrow> (A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs2, Normal ns2\<rangle> [\<rightarrow>] Normal ns2'))))"

text \<open>This is the "non-expanded"/compact form of the lemma that we use to prove the CFG-to-DAG phase
local block lemma.\<close>

lemma dag_rel_block_lemma_compact:
  assumes "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs1, Normal ns1\<rangle> [\<rightarrow>] s'" and
          "\<And>s2'. (A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs2, Normal ns2\<rangle> [\<rightarrow>] s2') \<Longrightarrow> s2' \<noteq> Failure" and
          "dag_lemma_assms A \<Lambda> \<Gamma> \<Omega> H pre_invs ns1 ns2" and
          Rel:"cfg_dag_rel c H pre_invs post_invs cs1 cs2" and
          "list_all (\<lambda>x. \<exists>w. lookup_var_decl \<Lambda> x = Some (w, None)) H" and
          "\<And>ns. state_well_typed A \<Lambda> \<Omega> ns \<Longrightarrow> list_all (\<lambda>inv. \<exists>b. A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>inv, ns\<rangle> \<Down> BoolV b) post_invs"
        shows "dag_lemma_conclusion A M \<Lambda> \<Gamma> \<Omega> post_invs cs2 ns2 s' c"
  using assms
  unfolding dag_lemma_assms_def dag_lemma_conclusion_def
  using dag_rel_block_lemma
  by blast

subsection \<open>Definitions and lemmas to track modified variables\<close>

fun mods_contained_in :: "vname set \<Rightarrow> cmd list \<Rightarrow> bool"
  where
    "mods_contained_in H [] = True"
  | "mods_contained_in H ((Havoc h)#cs) = ((h \<in> H) \<and> mods_contained_in H cs)"
  | "mods_contained_in H ((Assign x e)#cs) = ((x \<in> H) \<and> mods_contained_in H cs)"
(* method calls are already desugared in this phase *)
  | "mods_contained_in H ((ProcCall _ _ _)#cs) = False"
  | "mods_contained_in H (c#cs) = mods_contained_in H cs"

lemma mods_contained_in_rel_aux: 
  assumes "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs, s\<rangle> [\<rightarrow>] s'"
          "mods_contained_in D cs" and 
          "s = Normal ns" and "s' = Normal ns'"
  shows "nstate_same_on \<Lambda> ns ns' D"
  using assms
proof (induction arbitrary: ns)
  case (RedCmdListNil \<Omega> s)
     then show ?case 
     by (simp add: nstate_same_on_refl)
next
  case (RedCmdListCons \<Omega> c s s'' cs s')
  then show ?case
  proof cases
    case (RedAssertOk e n_s)
    then show ?thesis using RedCmdListCons by simp
  next
    case (RedAssertFail e n_s)
    then show ?thesis using RedCmdListCons 
      using failure_stays_cmd_list by blast
  next
    case (RedAssumeOk e n_s)
    then show ?thesis using RedCmdListCons by simp
  next
    case (RedAssumeMagic e n_s)
    then show ?thesis using RedCmdListCons 
      using magic_stays_cmd_list by blast
  next
    case (RedAssign x ty v e n_s)
    with RedCmdListCons have "x \<in> D" by simp
    hence "nstate_same_on \<Lambda> n_s (update_var \<Lambda> n_s x v) D" 
      by (simp add: nstate_same_on_update_3)
    moreover from RedAssign have "nstate_same_on \<Lambda> (update_var \<Lambda> n_s x v) ns' D" using RedCmdListCons by simp
    ultimately show ?thesis using RedCmdListCons  
      using RedAssign nstate_same_on_transitive by blast
  next
    case (RedHavocNormal x ty w v n_s)
    with RedCmdListCons have "x \<in> D" by simp
    hence "nstate_same_on \<Lambda> n_s (update_var \<Lambda> n_s x v) D" 
      by (simp add: nstate_same_on_update_3)
    moreover from RedHavocNormal have "nstate_same_on \<Lambda> (update_var \<Lambda> n_s x v) ns' D" using RedCmdListCons by simp
    ultimately show ?thesis using RedCmdListCons  
      using RedHavocNormal nstate_same_on_transitive by blast
  next
    case (RedHavocMagic x ty w v n_s)
    then show ?thesis using RedCmdListCons 
      using magic_stays_cmd_list by blast
  next
    case (RedProcCallOkAndMagic m msig args n_s v_args pre_ls new_ls ty_modifs vs_modifs vs_ret post_ls post_gs post_state n_s' rets)
    then show ?thesis using RedCmdListCons by simp
  next
    case (RedProcCallFail _)
    thus ?thesis using RedCmdListCons by simp 
  next
    case RedPropagateMagic
    then show ?thesis using RedCmdListCons by simp
  next
    case RedPropagateFailure
    then show ?thesis using RedCmdListCons by simp
  qed
qed

lemma mods_contained_in_rel:
  assumes "mods_contained_in D cs" and
          "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs, Normal ns\<rangle> [\<rightarrow>] Normal ns'"
  shows "nstate_same_on \<Lambda> ns ns' D"
  using assms mods_contained_in_rel_aux
  by blast

subsection \<open>Helper lemmas to prove the global block theorems in the CFG-to-DAG phase\<close>

lemma dag_verifies_propagate:
  assumes CfgVerifies:"(\<And>m2' s2'. (A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl m, Normal ns) -n\<rightarrow>* (m2', s2')) \<Longrightarrow> s2' \<noteq> Failure)" and
          Block: "node_to_block G ! m = cs" and
          Succ:"List.member (out_edges(G) ! m) msuc" and
          BlockRed:"A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs, Normal ns\<rangle> [\<rightarrow>] Normal ns'" and
          SuccRed:"A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl(msuc), Normal ns') -n\<rightarrow>* (m3', s3')"
        shows   "s3' \<noteq> Failure"
proof -
  have RedStep:"A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl m, Normal ns) -n\<rightarrow> (Inl msuc, Normal ns')"
    using Block Succ BlockRed
    by (auto intro: red_cfg.intros)
  have "A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl m, Normal ns) -n\<rightarrow>* (m3', s3')"
    apply (rule converse_rtranclp_into_rtranclp)
     apply (rule RedStep)
    by (rule SuccRed)
  thus ?thesis
    using CfgVerifies by auto
qed

lemma dag_verifies_propagate_2:
  assumes CfgVerifies:"(\<And>m2' s2'. A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl m, Normal ns) -n\<rightarrow>* (m2', s2') \<Longrightarrow> s2' \<noteq> Failure)" and
          Block:"node_to_block G ! m = cs" and
          BlockNormal:"A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs,Normal ns\<rangle> [\<rightarrow>] s'"
        shows "s' \<noteq> Failure"
  using assms
proof (cases "(out_edges G) ! m = []")
  case True
  hence "A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl m, Normal ns) -n\<rightarrow> (Inr (), s')"
    apply (cases s')
    using Block BlockNormal
    by (auto intro: red_cfg.intros)
  then show ?thesis using CfgVerifies by blast
next
  case False
  from this obtain msuc where "List.member (out_edges G ! m) msuc"
    by (metis list.exhaust member_rec(1))
  hence "\<exists>m'. A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl m, Normal ns) -n\<rightarrow> (m', s')"
    apply (cases s')
    using Block BlockNormal
    by (auto intro: red_cfg.intros)
  thus ?thesis using CfgVerifies by blast
qed

text \<open>The following lemma is the main global block theorem helper lemma for the case where the block
before the CFG-to-DAG phase has at least one successor (i.e., not a return block). Below we use this
lemma to derive more specific lemmas that we then use in the actual proofs.\<close>

lemma cfg_dag_helper_not_return_general:
  assumes
   Red: "A,M,\<Lambda>,\<Gamma>,\<Omega>,G1 \<turnstile> (Inl m1, (Normal  ns1)) -n\<rightarrow>^j (m', s')" and
   Block: "node_to_block G1 ! m1 = cs1" and
   Block2: "node_to_block G2 ! m2 = cs2" and 
   DagVerifies: "\<And> m2' s2'. (A,M,\<Lambda>,\<Gamma>,\<Omega>,G2 \<turnstile> (Inl m2, Normal ns2) -n\<rightarrow>* (m2', s2')) \<Longrightarrow> s2' \<noteq> Failure" and
   DagAssm:  "dag_lemma_assms A \<Lambda> \<Gamma> \<Omega> H pre_invs ns1 ns2" and
   BlockCorrect: "\<And> s1''. A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs1, Normal ns1\<rangle> [\<rightarrow>] s1'' \<Longrightarrow>
               (\<And>s2'. (A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs2, Normal ns2\<rangle> [\<rightarrow>] s2') \<Longrightarrow> s2' \<noteq> Failure) \<Longrightarrow>
               dag_lemma_assms A \<Lambda> \<Gamma> \<Omega> H pre_invs ns1 ns2  \<Longrightarrow>      
               dag_lemma_conclusion A M \<Lambda> \<Gamma> \<Omega> post_invs cs2 ns2 s1'' c" and
   Mods: "b \<Longrightarrow> mods_contained_in D cs1" and
   NonReturnNode: "out_edges(G1) ! m1 \<noteq> []" and
   SuccCorrect:"\<And> msuc ns1'' ns2'' j'.
            j = Suc j' \<Longrightarrow>
            List.member (out_edges(G1) ! m1) msuc \<Longrightarrow>
            state_well_typed A \<Lambda> \<Omega> ns1'' \<Longrightarrow>
            state_well_typed A \<Lambda> \<Omega> ns2'' \<Longrightarrow>
            list_all (expr_sat A \<Lambda> \<Gamma> \<Omega> ns1'') post_invs \<Longrightarrow>
            (b \<Longrightarrow> nstate_same_on \<Lambda> ns1 ns1'' D) \<Longrightarrow>
            nstate_same_on \<Lambda> ns1'' ns2'' {} \<Longrightarrow>
            (\<not>c \<longrightarrow> (\<forall>msuc2.  List.member (out_edges(G2) ! m2) msuc2 \<longrightarrow>
                (\<forall>m3 s3. ((A,M,\<Lambda>,\<Gamma>,\<Omega>,G2 \<turnstile> (Inl(msuc2), Normal ns2'') -n\<rightarrow>* (m3, s3)) \<longrightarrow> s3 \<noteq> Failure)))) \<Longrightarrow>
            A,M,\<Lambda>,\<Gamma>,\<Omega>,G1 \<turnstile> (Inl(msuc), Normal ns1'') -n\<rightarrow>^j' (m', s') \<Longrightarrow> valid_configuration A \<Lambda> \<Gamma> \<Omega> posts m' s'"
shows "valid_configuration A \<Lambda> \<Gamma> \<Omega> posts m' s'"
  using assms
proof (cases rule: relpowp_E2_2[OF assms(1)])
  case 1
  then show ?thesis unfolding valid_configuration_def by auto
next
  case (2 a b j')
  from \<open>A,M,\<Lambda>,\<Gamma>,\<Omega>,G1 \<turnstile> (Inl m1, Normal ns1) -n\<rightarrow> (a, b)\<close> show ?thesis
  proof (cases rule: red_cfg.cases)
    case (RedNormalSucc cs ns1'' msuc)
    hence "dag_lemma_conclusion A M \<Lambda> \<Gamma> \<Omega> post_invs cs2 ns2 (Normal ns1'') c"
      unfolding dag_lemma_conclusion_def
      using Block BlockCorrect dag_verifies_propagate_2 DagVerifies
      by (metis Block2 DagAssm dag_lemma_conclusion_def)
    from this obtain ns2'' where
      StateWt: "state_well_typed A \<Lambda> \<Omega> ns1''" and
      PostHolds:"list_all (expr_sat A \<Lambda> \<Gamma> \<Omega> ns1'') post_invs" and 
      StateRel:"nstate_same_on \<Lambda> ns1'' ns2'' {}" and
      StateWt2: "state_well_typed A \<Lambda> \<Omega> ns2''" and
      NormalDag:"\<not>c \<longrightarrow> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs2, Normal ns2\<rangle> [\<rightarrow>] Normal ns2''"
      unfolding dag_lemma_conclusion_def
      by blast
    show ?thesis
      apply (rule SuccCorrect[OF \<open>j = Suc j'\<close> \<open>List.member (out_edges G1 ! m1) msuc\<close> StateWt StateWt2 PostHolds _ StateRel])
        apply (erule mods_contained_in_rel[OF Mods])
      using Block RedNormalSucc apply fastforce
       apply (rule impI, rule allI, rule impI, rule allI, rule allI, rule impI)
      using Block2 DagVerifies NormalDag dag_verifies_propagate apply blast
      using RedNormalSucc 2 by simp
  next
  case (RedNormalReturn cs ns')
  then show ?thesis unfolding valid_configuration_def using 2 finished_remains NonReturnNode
    by simp
  next
    case (RedFailure cs)
    then show ?thesis using  BlockCorrect Block DagAssm dag_lemma_conclusion_def unfolding valid_configuration_def
      by (metis Block2 DagVerifies dag_verifies_propagate_2)
  next
    case (RedMagic cs)
    then show ?thesis using 2 unfolding valid_configuration_def
      by (meson Pair_inject finished_remains relpowp_imp_rtranclp state.distinct(3) state.distinct(5))     
  qed
qed

lemma cfg_dag_helper_1:
  assumes
   Red: "A,M,\<Lambda>,\<Gamma>,\<Omega>,G1 \<turnstile> (Inl m1, (Normal  ns1)) -n\<rightarrow>^j (m', s')" and
   Block: "node_to_block G1 ! m1 = cs1" and
   Block2: "node_to_block G2 ! m2 = cs2" and 
   DagVerifies: "\<And> m2' s2'. (A,M,\<Lambda>,\<Gamma>,\<Omega>,G2 \<turnstile> (Inl m2, Normal ns2) -n\<rightarrow>* (m2', s2')) \<Longrightarrow> s2' \<noteq> Failure" and
   DagAssm:  "dag_lemma_assms A \<Lambda> \<Gamma> \<Omega> H pre_invs ns1 ns2" and
   BlockCorrect: "\<And> s1''. A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs1, Normal ns1\<rangle> [\<rightarrow>] s1'' \<Longrightarrow>
               (\<And>s2'. (A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs2, Normal ns2\<rangle> [\<rightarrow>] s2') \<Longrightarrow> s2' \<noteq> Failure) \<Longrightarrow>
               dag_lemma_assms A \<Lambda> \<Gamma> \<Omega> H pre_invs ns1 ns2  \<Longrightarrow>      
               dag_lemma_conclusion A M \<Lambda> \<Gamma> \<Omega> post_invs cs2 ns2 s1'' c" and
   NonReturnNode: "out_edges(G1) ! m1 \<noteq> []" and
   SuccCorrect:"\<And> msuc ns1'' ns2'' j'.
            j = Suc j' \<Longrightarrow>
            List.member (out_edges(G1) ! m1) msuc \<Longrightarrow>
            state_well_typed A \<Lambda> \<Omega> ns1'' \<Longrightarrow>
            state_well_typed A \<Lambda> \<Omega> ns2'' \<Longrightarrow>
            list_all (expr_sat A \<Lambda> \<Gamma> \<Omega> ns1'') post_invs \<Longrightarrow>
            nstate_same_on \<Lambda> ns1'' ns2'' {} \<Longrightarrow>
            (\<not>c \<longrightarrow> (\<forall>msuc2.  List.member (out_edges(G2) ! m2) msuc2 \<longrightarrow>
                (\<forall>m3 s3. ((A,M,\<Lambda>,\<Gamma>,\<Omega>,G2 \<turnstile> (Inl(msuc2), Normal ns2'') -n\<rightarrow>* (m3, s3)) \<longrightarrow> s3 \<noteq> Failure)))) \<Longrightarrow>
            A,M,\<Lambda>,\<Gamma>,\<Omega>,G1 \<turnstile> (Inl(msuc), Normal ns1'') -n\<rightarrow>^j' (m', s') \<Longrightarrow> valid_configuration A \<Lambda> \<Gamma> \<Omega> posts m' s'"
 shows "valid_configuration A \<Lambda> \<Gamma> \<Omega> posts m' s'"
  using assms(1-6)
  apply (rule cfg_dag_helper_not_return_general[where ?b=False])
  using assms
  by auto

lemma cfg_dag_helper_2:
  assumes
   Red: "A,M,\<Lambda>,\<Gamma>,\<Omega>,G1 \<turnstile> (Inl m1, (Normal  ns1)) -n\<rightarrow>^j (m', s')" and
   Block: "node_to_block G1 ! m1 = cs1" and
   Block2: "node_to_block G2 ! m2 = cs2" and 
   DagVerifies: "\<And> m2' s2'. (A,M,\<Lambda>,\<Gamma>,\<Omega>,G2 \<turnstile> (Inl m2, Normal ns2) -n\<rightarrow>* (m2', s2')) \<Longrightarrow> s2' \<noteq> Failure" and
   DagAssm:  "dag_lemma_assms A \<Lambda> \<Gamma> \<Omega> H pre_invs ns1 ns2" and
   BlockCorrect: "\<And> s1''. A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs1, Normal ns1\<rangle> [\<rightarrow>] s1'' \<Longrightarrow>
               (\<And>s2'. (A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs2, Normal ns2\<rangle> [\<rightarrow>] s2') \<Longrightarrow> s2' \<noteq> Failure) \<Longrightarrow>
               dag_lemma_assms A \<Lambda> \<Gamma> \<Omega> H pre_invs ns1 ns2  \<Longrightarrow>      
               dag_lemma_conclusion A M \<Lambda> \<Gamma> \<Omega> post_invs cs2 ns2 s1'' c" and
   Mods: "mods_contained_in D cs1" and
   NonReturnNode: "out_edges(G1) ! m1 \<noteq> []" and
   SuccCorrect:"\<And> msuc ns1'' ns2'' j'.
            j = Suc j' \<Longrightarrow>
            List.member (out_edges(G1) ! m1) msuc \<Longrightarrow>
            state_well_typed A \<Lambda> \<Omega> ns1'' \<Longrightarrow>
            state_well_typed A \<Lambda> \<Omega> ns2'' \<Longrightarrow>
            list_all (expr_sat A \<Lambda> \<Gamma> \<Omega>  ns1'') post_invs \<Longrightarrow>
            nstate_same_on \<Lambda> ns1 ns1'' D \<Longrightarrow>
            nstate_same_on \<Lambda> ns1'' ns2'' {} \<Longrightarrow>
            (\<not>c \<longrightarrow> (\<forall>msuc2.  List.member (out_edges(G2) ! m2) msuc2 \<longrightarrow>
                (\<forall>m3 s3. ((A,M,\<Lambda>,\<Gamma>,\<Omega>,G2 \<turnstile> (Inl(msuc2), Normal ns2'') -n\<rightarrow>* (m3, s3)) \<longrightarrow> s3 \<noteq> Failure)))) \<Longrightarrow>
            A,M,\<Lambda>,\<Gamma>,\<Omega>,G1 \<turnstile> (Inl(msuc), Normal ns1'') -n\<rightarrow>^j' (m', s') \<Longrightarrow> valid_configuration A \<Lambda> \<Gamma> \<Omega> posts m' s'"
  shows "valid_configuration A \<Lambda> \<Gamma> \<Omega> posts m' s'"
  using assms(1-8)
  apply (rule cfg_dag_helper_not_return_general[where ?b=True])
    apply assumption
     apply assumption
    apply assumption
  apply assumption
  using SuccCorrect
  by blast


fun assume_pres :: "expr list \<Rightarrow> cmd list \<Rightarrow> bool"
  where 
    "assume_pres [] [] = True"
  | "assume_pres (e1#es) ((Assume e2)#cs) = ((e1 = e2) \<and> assume_pres es cs)"
  | "assume_pres _ _ = False"

lemma assume_pres_normal:
  assumes "expr_all_sat A \<Lambda> \<Gamma> \<Omega> ns es" and "assume_pres es cs" 
  shows "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs, Normal ns\<rangle> [\<rightarrow>] Normal ns"
  using assms
proof (induction cs arbitrary: es)
  case Nil
  then show ?case by (auto intro: RedCmdListNil)
next
  case (Cons a cs)
  from this obtain e es' where "es = e#es'" and "a = Assume e"
    using assume_pres.elims(2) by blast  
  with Cons have "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e, ns\<rangle> \<Down> BoolV True" and "expr_all_sat A \<Lambda> \<Gamma> \<Omega> ns es'"
    unfolding expr_all_sat_def expr_sat_def
    by auto
  then show ?case using Cons
    by (metis (full_types) RedAssumeOk RedCmdListCons \<open>a = Assume e\<close> \<open>es = e # es'\<close> assume_pres.simps(2))
qed

lemma cfg_dag_helper_entry:
  assumes
   Block: "node_to_block G2 ! m2 = cs2" and
   DagVerifies: "\<And> m2' s2'. (A,M,\<Lambda>,\<Gamma>,\<Omega>,G2 \<turnstile> (Inl m2, Normal ns2) -n\<rightarrow>* (m2', s2')) \<Longrightarrow> s2' \<noteq> Failure" and
   DagAssm:  "dag_lemma_assms A \<Lambda> \<Gamma> \<Omega> H pre_invs ns1 ns2" and
   BlockCorrect: "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs2, Normal ns2\<rangle> [\<rightarrow>] Normal ns2" and
   Propagate1: "out_edges(G2) ! m2 = [m2_suc]" and
   Block2Empty: "node_to_block G2 ! m2_suc = []" and
   Propagate2: "out_edges(G2) ! m2_suc = [m2_suc_suc]" and                
   SucCorrect: "(\<And> m2' s2'. (A,M,\<Lambda>,\<Gamma>,\<Omega>,G2 \<turnstile> (Inl m2_suc_suc, Normal ns2) -n\<rightarrow>* (m2', s2')) \<Longrightarrow> s2' \<noteq> Failure) \<Longrightarrow> R"
 shows "R"
proof -
  from Block BlockCorrect Propagate1 have RedM2:"A,M,\<Lambda>,\<Gamma>,\<Omega>,G2 \<turnstile> (Inl m2, Normal ns2) -n\<rightarrow> (Inl m2_suc,Normal ns2)"
    by (simp add: RedNormalSucc member_rec(1))
  from Block2Empty Propagate2 have RedM2Suc:"A,M,\<Lambda>,\<Gamma>,\<Omega>,G2 \<turnstile> (Inl m2_suc, Normal ns2) -n\<rightarrow> (Inl m2_suc_suc,Normal ns2)"
    by (simp add: RedCmdListNil RedNormalSucc member_rec(1))
  show "R"
    apply (rule SucCorrect)
    using RedM2 RedM2Suc
    by (meson DagVerifies converse_rtranclp_into_rtranclp)
qed


text \<open>The following lemma is a global block theorem helper lemma for the case where the block
before the CFG-to-DAG phase has no successor (i.e., not a return block) and where we do not expect
that the corresponding block B' after the CFG-to-DAG phase has a successor either (if there are multiple
return blocks, Boogie adds a new unique exit block). Hence, the assertion of the postcondition should
is inserted at the end of B'.\<close>

lemma cfg_dag_helper_return_1:
  assumes
   Red: "A,M,\<Lambda>,\<Gamma>,\<Omega>,G1 \<turnstile> (Inl m1, (Normal  ns1)) -n\<rightarrow>^j (m', s')" and
   Block: "node_to_block G1 ! m1 = cs1" and
   Block2: "node_to_block G2 ! m2 = cs2" and 
   DagVerifies: "\<And> m2' s2'. (A,M,\<Lambda>,\<Gamma>,\<Omega>,G2 \<turnstile> (Inl m2, Normal ns2) -n\<rightarrow>* (m2', s2')) \<Longrightarrow> s2' \<noteq> Failure" and
   DagAssm:  "dag_lemma_assms A \<Lambda> \<Gamma> \<Omega> H pre_invs ns1 ns2" and
   BlockCorrect: "\<And> s1''. A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs1, Normal ns1\<rangle> [\<rightarrow>] s1'' \<Longrightarrow>
               (\<And>s2'. (A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs2, Normal ns2\<rangle> [\<rightarrow>] s2') \<Longrightarrow> s2' \<noteq> Failure) \<Longrightarrow>
               dag_lemma_assms A \<Lambda> \<Gamma> \<Omega> H pre_invs ns1 ns2  \<Longrightarrow>      
               dag_lemma_conclusion A M \<Lambda> \<Gamma> \<Omega> post_invs cs2 ns2 s1'' c" and
   ReturnNode: "out_edges(G1) ! m1 = []"   
 shows "valid_configuration A \<Lambda> \<Gamma> \<Omega> post_invs m' s'"
  using assms
proof (cases rule: relpowp_E2_2[OF assms(1)])
  case 1
  then show ?thesis unfolding valid_configuration_def by auto
next
  case (2 a b j')
  from \<open>A,M,\<Lambda>,\<Gamma>,\<Omega>,G1 \<turnstile> (Inl m1, Normal ns1) -n\<rightarrow> (a, b)\<close> show ?thesis
  proof (cases rule: red_cfg.cases)
  case (RedNormalSucc cs ns1' n')
  then show ?thesis using ReturnNode
    by (simp add: member_rec(2))
  next
    case (RedNormalReturn cs ns1')
      hence "dag_lemma_conclusion A M \<Lambda> \<Gamma> \<Omega> post_invs cs2 ns2 (Normal ns1') c"
        unfolding dag_lemma_conclusion_def
        using Block BlockCorrect dag_verifies_propagate_2 DagVerifies
        by (metis Block2 DagAssm dag_lemma_conclusion_def)
      from this have
        PostHolds:"list_all (expr_sat A \<Lambda> \<Gamma> \<Omega> ns1') post_invs"
        unfolding dag_lemma_conclusion_def
        by blast
      from PostHolds show ?thesis 
        unfolding valid_configuration_def expr_all_sat_def      
        by (metis "2" (3) finished_remains local.RedNormalReturn(1) local.RedNormalReturn(2) prod.inject relpowp_imp_rtranclp state.distinct(1) state.inject)
  next
    case (RedFailure cs)
    then show ?thesis   
      using  BlockCorrect Block DagAssm dag_lemma_conclusion_def unfolding valid_configuration_def
      by (metis Block2 DagVerifies dag_verifies_propagate_2)
  next
    case (RedMagic cs)
    then show ?thesis
      using 2 unfolding valid_configuration_def
      by (meson Pair_inject finished_remains relpowp_imp_rtranclp state.distinct(3) state.distinct(5))     
  qed
qed

text \<open>The following lemma is a global block theorem helper lemma for the case where the block
before the CFG-to-DAG phase has no successor (i.e., not a return block) and 
the corresponding block B' after the CFG-to-DAG phase has one successor B''. B'' is the unique exit block
generated by Boogie and the assertion of the postcondition is added to the end of B''.\<close>

lemma cfg_dag_helper_return_2:
  assumes
   Red: "A,M,\<Lambda>,\<Gamma>,\<Omega>,G1 \<turnstile> (Inl m1, (Normal  ns1)) -n\<rightarrow>^j (m', s')" and
   Block: "node_to_block G1 ! m1 = cs1" and
   Block2: "node_to_block G2 ! m2 = cs2" and 
   DagVerifies: "\<And> m2' s2'. (A,M,\<Lambda>,\<Gamma>,\<Omega>,G2 \<turnstile> (Inl m2, Normal ns2) -n\<rightarrow>* (m2', s2')) \<Longrightarrow> s2' \<noteq> Failure" and
   DagAssm:  "dag_lemma_assms A \<Lambda> \<Gamma> \<Omega> H pre_invs ns1 ns2" and
   BlockCorrect: "\<And> s1''. A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs1, Normal ns1\<rangle> [\<rightarrow>] s1'' \<Longrightarrow>
               (\<And>s2'. (A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs2, Normal ns2\<rangle> [\<rightarrow>] s2') \<Longrightarrow> s2' \<noteq> Failure) \<Longrightarrow>
               dag_lemma_assms A \<Lambda> \<Gamma> \<Omega> H pre_invs ns1 ns2  \<Longrightarrow>      
               dag_lemma_conclusion A M \<Lambda> \<Gamma> \<Omega> post_invs cs2 ns2 s1'' False" and
   ReturnNode: "out_edges(G1) ! m1 = []" and
   DagUniqueExitEdge: "out_edges (G2) ! m2 = [m2_exit]" and
   UniqueExitAssm: "\<And>ns2 s2'.                    
                    (\<And> m2' s2'. (A,M,\<Lambda>,\<Gamma>,\<Omega>,G2 \<turnstile> (Inl m2_exit, Normal ns2) -n\<rightarrow>* (m2', s2') \<Longrightarrow> s2' \<noteq> Failure)) \<Longrightarrow>
                    state_well_typed A \<Lambda> \<Omega> ns2 \<Longrightarrow>
                    (expr_all_sat A \<Lambda> \<Gamma> \<Omega> ns2) posts"
 shows "valid_configuration A \<Lambda> \<Gamma> \<Omega> posts m' s'"
proof (cases rule: relpowp_E2_2[OF assms(1)])
  case 1
  then show ?thesis unfolding valid_configuration_def by auto
next
  case (2 a b j')
  from \<open>A,M,\<Lambda>,\<Gamma>,\<Omega>,G1 \<turnstile> (Inl m1, Normal ns1) -n\<rightarrow> (a, b)\<close> show ?thesis
  proof (cases rule: red_cfg.cases)
  case (RedNormalSucc cs ns' n')
  then show ?thesis using ReturnNode
    by (simp add: member_rec(2))
  next
    case (RedNormalReturn cs ns1')
    hence "dag_lemma_conclusion A M \<Lambda> \<Gamma> \<Omega> post_invs cs2 ns2 (Normal ns1') False"
      unfolding dag_lemma_conclusion_def
      using Block BlockCorrect dag_verifies_propagate_2 DagVerifies
      by (metis Block2 DagAssm dag_lemma_conclusion_def)
    from this obtain ns2' where
      StateWt: "state_well_typed A \<Lambda> \<Omega> ns1'" and
      StateWt2:"state_well_typed A \<Lambda> \<Omega> ns2'" and
      (*PostHolds:"list_all (expr_sat A \<Lambda> \<Gamma> \<Omega> ns1') post_invs" and *)
      StateRel:"nstate_same_on \<Lambda> ns1' ns2' {}" and
      NormalDag:"A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs2, Normal ns2\<rangle> [\<rightarrow>] Normal ns2'"
      unfolding dag_lemma_conclusion_def
      by blast
    from DagUniqueExitEdge NormalDag Block2  DagVerifies
    have "\<And>m2' s2'. (A,M,\<Lambda>,\<Gamma>,\<Omega>,G2 \<turnstile> (Inl m2_exit, Normal ns2') -n\<rightarrow>* (m2', s2')) \<Longrightarrow> s2' \<noteq> Failure"
      by (metis RedNormalSucc converse_rtranclp_into_rtranclp member_rec(1))
    with StateWt2 UniqueExitAssm have "(expr_all_sat A \<Lambda> \<Gamma> \<Omega> ns2') posts"
      by blast
    hence "expr_all_sat A \<Lambda> \<Gamma> \<Omega> ns1' posts"
      using expr_all_sat_nstate_same_on StateRel nstate_same_on_sym
      by blast      
    thus ?thesis
      unfolding valid_configuration_def
      by (metis "2"(3) finished_remains local.RedNormalReturn(1) local.RedNormalReturn(2) old.prod.inject relpowp_imp_rtranclp state.distinct(1) state.inject)
  next
    case (RedFailure cs)
    then show ?thesis
      by (metis Block Block2 BlockCorrect DagAssm DagVerifies dag_lemma_conclusion_def dag_verifies_propagate_2)
  next
  case (RedMagic cs)
  then show ?thesis 
    by (metis "2"(3) valid_configuration_def finished_remains old.prod.inject relpowp_imp_rtranclp state.distinct(3) state.distinct(5))
  qed
qed

lemma cfg_dag_rel_no_cut:
  assumes "cfg_dag_rel False [] [] [] [] cs"
  shows "cs = []"
  using assms
  by (cases) auto

lemma cfg_dag_simple_propagate_helper_general:
  assumes DagVerifies:"\<forall> m2' s2'. ((A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl m, Normal ns2) -n\<rightarrow>* (m2', s2')) \<longrightarrow> (s2' \<noteq> Failure))" and
         StateRel:"nstate_same_on \<Lambda> ns1 ns2 {}" and
         StateWt:"state_well_typed A \<Lambda> \<Omega> ns1" and
         StateWt2:"state_well_typed A \<Lambda> \<Omega> ns2" and 
         SucCorrect:
          "list_all (expr_sat A \<Lambda> \<Gamma> \<Omega> ns1) post_invs \<Longrightarrow> 
           (\<not>c \<Longrightarrow> (\<And> m2' s2'. ((A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl m_suc, Normal ns2) -n\<rightarrow>* (m2', s2')) \<Longrightarrow> (s2' \<noteq> Failure))))\<Longrightarrow>
                        R" and
         Block: "node_to_block G ! m = cs" and 
         SingleSucc: "\<not>c \<Longrightarrow> out_edges G ! m = [m_suc]" and
         Rel: "cfg_dag_rel c [] [] post_invs [] cs" and
         InvsWt:"\<And>ns. state_well_typed A \<Lambda> \<Omega> ns \<Longrightarrow> list_all (\<lambda>inv. \<exists>b. A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>inv, ns\<rangle> \<Down> BoolV b) post_invs"
  shows "R"
proof -
  have BlockCorrect:"\<And>s2'. A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs,Normal ns2\<rangle> [\<rightarrow>] s2' \<Longrightarrow> s2' \<noteq> Failure"
    using DagVerifies dag_verifies_propagate_2 Block
    by blast  
  from StateWt2 obtain csA csB where 
    "cs = csA @ csB" and
    Rel2:"cfg_dag_rel c [] [] [] [] csB" and 
    RedCsA:"(A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>csA,Normal ns2\<rangle> [\<rightarrow>] Normal ns2)" and
    InvsHold2:"list_all (expr_sat A \<Lambda> \<Gamma> \<Omega> ns2) post_invs"
    using cfg_dag_rel_post_invs[OF Rel refl refl refl BlockCorrect] InvsWt
    by metis
  have InvsHold1:"list_all (expr_sat A \<Lambda> \<Gamma> \<Omega> ns1) post_invs" 
    apply (rule List.List.list.pred_mono_strong)
    apply (rule InvsHold2)
    unfolding expr_sat_def
    using StateRel eval_nstate_same_on(1) nstate_same_on_sym by blast
  show R
  proof (cases c)
    case True
    show ?thesis
      apply (rule SucCorrect[OF InvsHold1])
      using True by simp
  next
    case False
      hence RedCs:"(A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs,Normal ns2\<rangle> [\<rightarrow>] Normal ns2)"
    using cfg_dag_rel_no_cut \<open>cs = csA@csB\<close> Rel2 RedCsA
    by fastforce
  have RedSuc:"A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl m, Normal ns2) -n\<rightarrow> (Inl m_suc, Normal ns2)"
    apply (rule RedNormalSucc[OF Block])
     apply (rule RedCs)
    using SingleSucc False
    by (simp add: member_rec(1))
  show R
    apply (rule SucCorrect[OF InvsHold1])
    using RedSuc DagVerifies 
    by (metis converse_rtranclp_into_rtranclp)
  qed
qed

lemma cfg_dag_no_cut_propagate_helper:
  assumes DagVerifies:"\<forall> m2' s2'. ((A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl m, Normal ns2) -n\<rightarrow>* (m2', s2')) \<longrightarrow> (s2' \<noteq> Failure))" and
         StateRel:"nstate_same_on \<Lambda> ns1 ns2 {}" and
         StateWt:"state_well_typed A \<Lambda> \<Omega> ns1" and
         StateWt2:"state_well_typed A \<Lambda> \<Omega> ns2" and
         SucCorrect:
          "list_all (expr_sat A \<Lambda> \<Gamma> \<Omega> ns1) post_invs \<Longrightarrow> 
           ((\<And> m2' s2'. ((A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl m_suc, Normal ns2) -n\<rightarrow>* (m2', s2')) \<Longrightarrow> (s2' \<noteq> Failure))))\<Longrightarrow>
                        R" and
         Block: "node_to_block G ! m = cs" and 
         SingleSucc: "out_edges G ! m = [m_suc]" and
         Rel: "cfg_dag_rel False [] [] post_invs [] cs" and
         InvsWt:"\<And>ns. state_well_typed A \<Lambda> \<Omega> ns \<Longrightarrow> list_all (\<lambda>inv. \<exists>b. A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>inv, ns\<rangle> \<Down> BoolV b) post_invs"
       shows "R"
  using assms(1-4)
  apply (rule cfg_dag_simple_propagate_helper_general[where ?c=False])
      apply (rule SucCorrect)
       apply simp
      apply simp
  using assms(5-)
  by simp_all

lemma cfg_dag_cut_propagate_helper:
  assumes DagVerifies:"\<forall> m2' s2'. ((A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl m, Normal ns2) -n\<rightarrow>* (m2', s2')) \<longrightarrow> (s2' \<noteq> Failure))" and
         StateRel:"nstate_same_on \<Lambda> ns1 ns2 {}" and
         StateWt:"state_well_typed A \<Lambda> \<Omega> ns1" and
         StateW2:"state_well_typed A \<Lambda> \<Omega> ns2" and
         SucCorrect:
          "list_all (expr_sat A \<Lambda> \<Gamma> \<Omega> ns1) post_invs \<Longrightarrow> R" and
         Block: "node_to_block G ! m = cs" and 
         Rel: "cfg_dag_rel True [] [] post_invs [] cs" and
         InvsWt:"\<And>ns. state_well_typed A \<Lambda> \<Omega> ns \<Longrightarrow> list_all (\<lambda>inv. \<exists>b. A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>inv, ns\<rangle> \<Down> BoolV b) post_invs"
       shows "R"
  using assms(1-4)
  apply (rule cfg_dag_simple_propagate_helper_general[where ?c=True])  
      apply (rule SucCorrect)
       apply simp
      apply simp
  using assms(5-)
  by simp_all

lemma cfg_dag_empty_propagate_helper:
  assumes DagVerifies:"\<forall> m2' s2'. ((A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl m, Normal ns2) -n\<rightarrow>* (m2', s2')) \<longrightarrow> (s2' \<noteq> Failure))" and
         StateRel:"nstate_same_on \<Lambda> ns1 ns2 {}" and
         StateWt:"state_well_typed A \<Lambda> \<Omega> ns1" and
         StateWt2:"state_well_typed A \<Lambda> \<Omega> ns2" and
         SucCorrect:
          "(\<And> m2' s2'. ((A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl m_suc, Normal ns2) -n\<rightarrow>* (m2', s2')) \<Longrightarrow> (s2' \<noteq> Failure)))\<Longrightarrow>
                        R" and
         Block: "node_to_block G ! m = cs" and 
         SingleSucc: "out_edges G ! m = [m_suc]" and
         Empty:"cs = []"
       shows "R"
  using assms(1-7)
  apply (rule cfg_dag_simple_propagate_helper_general[where ?c=False])
    apply simp
  using Empty
  by (auto intro: cfg_dag_rel.intros)

lemma strictly_smaller_helper: "j'' \<le> j' \<Longrightarrow> j = Suc j' \<Longrightarrow> j'' < j"
  by simp

definition loop_ih :: "'a absval_ty_fun \<Rightarrow> mbodyCFG proc_context \<Rightarrow> var_context \<Rightarrow> 
                   'a fun_interp \<Rightarrow> rtype_env \<Rightarrow> mbodyCFG \<Rightarrow> vname list \<Rightarrow> expr list \<Rightarrow> expr list \<Rightarrow>
                    'a nstate \<Rightarrow> 'a state \<Rightarrow> nat \<Rightarrow> nat + unit \<Rightarrow> nat \<Rightarrow> bool"
  where "loop_ih A M \<Lambda> \<Gamma> \<Omega> G H invs posts ns1 s' node_id  m' j\<equiv> 
          \<forall>j' ns1''. j' \<le> j \<longrightarrow> 
                     (A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl node_id, Normal ns1'') -n\<rightarrow>^j' (m', s')) \<longrightarrow>
                     dag_lemma_assms A \<Lambda> \<Gamma> \<Omega> H invs ns1'' ns1 \<longrightarrow> 
                     valid_configuration A \<Lambda> \<Gamma> \<Omega> posts m' s'"

lemma loop_ih_apply:
  assumes "loop_ih A M \<Lambda> \<Gamma> \<Omega> G H invs posts ns1 s' node_id  m' j" and
          "j' \<le> j" and
          "(A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl node_id, Normal ns1'') -n\<rightarrow>^j' (m', s'))" and
          "dag_lemma_assms A \<Lambda> \<Gamma> \<Omega> H invs ns1'' ns1"
        shows "valid_configuration A \<Lambda> \<Gamma> \<Omega> posts m' s'"
  using assms
  unfolding loop_ih_def
  by blast

lemma loop_ih_prove:
  assumes "\<And>j' ns1''. j' \<le> j \<Longrightarrow>
                     (A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl node_id, Normal ns1'') -n\<rightarrow>^j' (m', s')) \<Longrightarrow>
                     dag_lemma_assms A \<Lambda> \<Gamma> \<Omega> H invs ns1'' ns1 \<Longrightarrow>
                     valid_configuration A \<Lambda> \<Gamma> \<Omega> posts m' s'"
  shows "loop_ih A M \<Lambda> \<Gamma> \<Omega> G H invs posts ns1 s' node_id m' j"
  using assms
  unfolding loop_ih_def
  by blast

lemma loop_ih_convert_subset_smaller:
  assumes "loop_ih  A M \<Lambda> \<Gamma> \<Omega> G H invs posts ns1 s' node_id m' j" and 
          "nstate_same_on \<Lambda> ns1 ns1'' H'" and
          "state_well_typed A \<Lambda> \<Omega> ns1" and
          "H' \<subseteq> (set H)" and
          "j' \<le> j"
        shows "loop_ih  A M \<Lambda> \<Gamma> \<Omega> G H invs posts ns1'' s' node_id m' j'"
  using assms
  unfolding loop_ih_def dag_lemma_assms_def
  by (meson dual_order.trans nstate_same_on_subset_2 nstate_same_on_sym nstate_same_on_transitive)
  

lemma loop_ih_convert_pred:
  assumes "loop_ih  A M \<Lambda> \<Gamma> \<Omega> G H invs posts ns1 s' node_id m' (Suc j)" and 
          "nstate_same_on \<Lambda> ns1 ns1'' (set H)" and
          "state_well_typed A \<Lambda> \<Omega> ns1"
  shows "loop_ih  A M \<Lambda> \<Gamma> \<Omega> G H invs posts ns1'' s' node_id m' j"
  using assms
  by (meson Suc_n_not_le_n equalityE le_cases loop_ih_convert_subset_smaller)

lemma loop_ih_convert_subset_pred:
  assumes "loop_ih  A M \<Lambda> \<Gamma> \<Omega> G H invs posts ns1 s' node_id m' (Suc j)" and 
          "nstate_same_on \<Lambda> ns1 ns1'' H'" and
          "state_well_typed A \<Lambda> \<Omega> ns1"
          "H' \<subseteq> (set H)"
  shows "loop_ih  A M \<Lambda> \<Gamma> \<Omega> G H invs posts ns1'' s' node_id m' j"
  using assms 
  by (metis loop_ih_convert_pred nstate_same_on_subset_2)

lemma loop_ih_convert_subset_smaller_2:
  assumes 
          "loop_ih A M \<Lambda> \<Gamma> \<Omega> G H' invs posts ns1 s' m m' j" and
          "j' \<le> j" and      
          "nstate_same_on \<Lambda> ns3 ns2 H" and
          "nstate_same_on \<Lambda> ns1 ns2 H" and
          "state_well_typed A \<Lambda> \<Omega> ns1"
          "H \<subseteq> (set H')"          
   shows  "loop_ih A M \<Lambda> \<Gamma> \<Omega> G H' invs posts ns3 s' m m' j'"
  using assms
  by (meson loop_ih_convert_subset_smaller nstate_same_on_sym nstate_same_on_transitive)

lemma loop_ih_convert_2:
  assumes "loop_ih  A M \<Lambda> \<Gamma> \<Omega> G H invs posts ns1 s' node_id m' j" and 
          "state_well_typed A \<Lambda> \<Omega> ns1" and
          "set H' \<subseteq> set H"
  shows "loop_ih  A M \<Lambda> \<Gamma> \<Omega> G H' invs posts ns1 s' node_id m' j"
  apply (rule loop_ih_prove)
  apply (rule loop_ih_apply[OF assms(1)])
    apply assumption
   apply assumption
  using assms dag_lemma_assms_subset by blast

lemma smaller_transitive: "(j''::nat) \<le> j' \<Longrightarrow> j' \<le> j \<Longrightarrow> j'' \<le> j"
  by auto

lemma smaller_helper_suc: "j = Suc j' \<Longrightarrow> j' < j"
  by simp

lemma backedge_loop_head_helper:
  assumes 
       "j = Suc j'" and
    IH:"\<And>k ns1. k < j \<Longrightarrow>
        A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl n, Normal ns1) -n\<rightarrow>^k (m', s') \<Longrightarrow>
        dag_lemma_assms A \<Lambda> \<Gamma> \<Omega> H1 pre ns1 ns2 \<Longrightarrow> 
        cfg_dag_lemma_conclusion A \<Lambda> \<Gamma> \<Omega> post m' s'" and
       "A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl n, Normal ns1'') -n\<rightarrow>^j' (m', s')" and
       "state_well_typed A \<Lambda> \<Omega> ns1''" and
       "state_well_typed A \<Lambda> \<Omega> ns2" and
       "nstate_same_on \<Lambda> ns1 ns1'' H2" and
       "H2 \<subseteq> set H1" and
       "nstate_same_on \<Lambda> ns1 ns2 (set H1)" and
       "list_all (expr_sat A \<Lambda> \<Gamma> \<Omega> ns1'') pre"
  shows "cfg_dag_lemma_conclusion A \<Lambda> \<Gamma> \<Omega> post m' s'"
  apply (rule IH)
    apply (rule smaller_helper_suc[OF \<open>j = Suc j'\<close>])
   apply (rule assms(3))
  unfolding dag_lemma_assms_def
  apply (intro conjI)
     apply (rule assms(9))
  using \<open>H2 \<subseteq> set H1\<close> \<open>nstate_same_on \<Lambda> ns1 ns1'' H2\<close> \<open>nstate_same_on \<Lambda> ns1 ns2 (set H1)\<close>
  apply (meson nstate_same_on_subset nstate_same_on_sym nstate_same_on_transitive)
   apply (rule assms(4))
  apply (rule assms(5))
  done

subsection \<open>Helper lemma for final end-to-end theorem\<close>


lemma end_to_end_util:
  assumes AExpanded:"\<And> \<Gamma> m' s' ns M.
           A,M,\<Lambda>,\<Gamma>,[],cfg_body  \<turnstile> (Inl n, Normal ns) -n\<rightarrow>* (m', s') \<Longrightarrow>
           (\<And> v. (closed ((type_of_val A) v))) \<Longrightarrow>
           (\<And> t. ((closed t) \<Longrightarrow> (\<exists> v. (((type_of_val A) v) = t)))) \<Longrightarrow>
           (fun_interp_wf A fun_decls \<Gamma>) \<Longrightarrow>
           (axiom_assm A \<Gamma> constants (ns::(('a)nstate)) axioms) \<Longrightarrow>
           (expr_all_sat A \<Lambda> \<Gamma> [] ns all_pres) \<Longrightarrow>
           (state_typ_wf A [] (local_state ns) (snd \<Lambda>)) \<Longrightarrow>
           (state_typ_wf A [] (global_state ns) (fst \<Lambda>)) \<Longrightarrow>
            unique_constants_distinct (global_state ns) unique_consts \<Longrightarrow>
           ((global_state ns) = (old_global_state ns)) \<Longrightarrow>
           ((binder_state ns) = Map.empty) \<Longrightarrow> 
           (valid_configuration A \<Lambda> \<Gamma> [] checked_posts m' s')" and
          "all_pres = proc_all_pres proc" and
          "checked_posts = proc_checked_posts proc" and
          ABody: "procedure.proc_body proc = Some (locals, cfg_body)" and
          AVarContext:"\<Lambda> = (constants@global_vars, (proc_args proc)@locals)" and
          ARets:"proc_rets proc = []" and
         (* "fun_decls = prog_funcs prog" and
          "axs = prog_axioms prog" and*)
          "proc_ty_args proc = 0" and
          "n = entry cfg_body"
          (*"const_decls = prog_consts prog"*)
        shows "proc_is_correct A fun_decls constants unique_consts global_vars axioms proc Semantics.proc_body_satisfies_spec"
proof -
  show "proc_is_correct A fun_decls constants unique_consts global_vars axioms proc Semantics.proc_body_satisfies_spec"
  proof( (simp only: proc_is_correct.simps), subst ABody, simp split: option.split, (rule allI | rule impI)+,
         unfold proc_body_satisfies_spec_def,(rule allI | rule impI)+)  
    fix \<Gamma> \<Omega> gs ls m' s' 
    assume Atyp:"(\<forall>t. closed t \<longrightarrow> (\<exists>v. type_of_val A v = t)) \<and> (\<forall>v. closed (type_of_val A v))" and
           FunWf:"fun_interp_wf A fun_decls \<Gamma>" and
           ARenv: "list_all closed \<Omega> \<and> length \<Omega> = proc_ty_args proc" and
           WfGlobal: "state_typ_wf A \<Omega> gs (constants @ global_vars)" and
           WfLocal: "state_typ_wf A \<Omega> ls (proc_args proc @ locals @ proc_rets proc)" and
           UniqueConsts: "unique_constants_distinct gs unique_consts" and
           AxSat: "axioms_sat A (constants, []) \<Gamma>
        \<lparr>old_global_state = Map.empty, global_state = state_restriction gs constants, local_state = Map.empty, binder_state = Map.empty\<rparr>
        axioms" and
        APres:  "expr_all_sat A (constants @ global_vars, proc_args proc @ locals @ proc_rets proc) \<Gamma> \<Omega>
        \<lparr>old_global_state = gs, global_state = gs, local_state = ls, binder_state = Map.empty\<rparr> (map fst (proc_pres proc))" and
        Ared: "A,[],(constants @ global_vars,
                proc_args proc @
                locals @
                proc_rets
                 proc),\<Gamma>,\<Omega>,cfg_body \<turnstile>(Inl (entry cfg_body),
                                       Normal \<lparr>old_global_state = gs, global_state = gs, local_state = ls, binder_state = Map.empty\<rparr>) -n\<rightarrow>*
       (m', s')"
    have Contexteq:"\<Lambda> = (constants @ global_vars, proc_args proc @ locals @ proc_rets proc)"
      using AVarContext ARets by simp
    from ARenv \<open>proc_ty_args proc = 0\<close> have "\<Omega> = []" by simp
    have "valid_configuration A \<Lambda> \<Gamma> [] checked_posts m' s'"
      apply (rule AExpanded)
                apply (subst \<open>n = entry cfg_body\<close>)
                apply (subst Contexteq)
      using Ared \<open>\<Omega> = []\<close>
               apply fastforce
              apply (simp add: Atyp)
             apply (simp add: Atyp)
            apply (simp add: FunWf)
      unfolding nstate_global_restriction_def 
      using AxSat
           apply simp
      using APres \<open>\<Omega> = []\<close> \<open>all_pres = _\<close> Contexteq
          apply simp
      using Contexteq WfLocal \<open>\<Omega> = []\<close>
         apply simp
      using Contexteq WfGlobal \<open>\<Omega> = []\<close>      
         apply simp
      using UniqueConsts
        apply simp
       apply simp
      apply simp
      done
    thus "valid_configuration A (constants @ global_vars, proc_args proc @ locals @ proc_rets proc) \<Gamma> \<Omega>
        (map fst (filter (\<lambda>x. \<not> snd x) (proc_posts proc))) m' s'"
      using Contexteq \<open>\<Omega> = []\<close> \<open>checked_posts = _\<close>
      by simp
  qed
qed


end