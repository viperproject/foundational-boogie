section \<open>Helper lemmas and definitions\<close>

theory Util
imports Semantics "HOL-Eisbach.Eisbach" "HOL-Eisbach.Eisbach_Tools"
begin

lemma finterp_extract_1: "fun_interp_wf A fds \<Gamma> \<Longrightarrow> map_of fds fn = Some fd \<Longrightarrow> \<Gamma> fn = Some f \<Longrightarrow> 
  fun_interp_single_wf A fd f"
  by (metis fun_interp_wf_def option.sel)

lemma finterp_extract_2: "fun_interp_wf A fds \<Gamma> \<Longrightarrow> map_of fds fn = Some fd \<Longrightarrow> \<Gamma> fn = Some f \<Longrightarrow>
   fun_interp_single_wf_2 A fd f"
  by (metis fun_interp_wf_def option.sel)

lemma finterp_member: "fun_interp_wf A fds \<Gamma> \<Longrightarrow> map_of fds f = Some fd \<Longrightarrow> \<Gamma> f = Some (the (\<Gamma> f))"
  by (metis fun_interp_wf_def option.distinct(1) option.exhaust_sel)

lemma assert_correct:
  "\<lbrakk>A,M,\<Lambda>,\<Gamma>,\<Delta> \<turnstile> \<langle>Assert e, Normal n_s\<rangle> \<rightarrow> s; A,\<Lambda>,\<Gamma>,\<Delta> \<turnstile> \<langle>e, n_s\<rangle> \<Down> LitV (LBool True) \<rbrakk> \<Longrightarrow> s = Normal n_s"
  by (erule red_cmd.cases; simp; blast dest: expr_eval_determ(1))

(*TODO, rewrite this as an elimination rule to be consistent with other rules *)
lemma assert_correct_2:
  "\<lbrakk>A,M,\<Lambda>,\<Gamma>,\<Delta> \<turnstile> \<langle>Assert e, s\<rangle> \<rightarrow> s'; s = Normal n_s; A,\<Lambda>,\<Gamma>,\<Delta> \<turnstile> \<langle>e, n_s\<rangle> \<Down> LitV (LBool True)\<rbrakk> \<Longrightarrow> s' = Normal n_s"
  by (erule red_cmd.cases; simp; blast dest: expr_eval_determ(1))

lemma assert_ml: 
"\<lbrakk> A,M,\<Lambda>,\<Gamma>,\<Delta> \<turnstile> \<langle>(Assert e) # cs, Normal ns\<rangle> [\<rightarrow>] s';
  A,\<Lambda>,\<Gamma>,\<Delta> \<turnstile> \<langle>e, ns\<rangle> \<Down> LitV (LBool True);
  A,M,\<Lambda>,\<Gamma>,\<Delta> \<turnstile> \<langle>cs, Normal ns\<rangle> [\<rightarrow>] s' \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  apply (erule RedCmdListCons_case)
  by (blast dest: assert_correct)

lemma assert_true_cmds: 
"\<lbrakk> A,M,\<Lambda>,\<Gamma>,\<Delta> \<turnstile> \<langle>(Assert (Lit (LBool True))) # cs, Normal ns\<rangle> [\<rightarrow>] s';
  A,M,\<Lambda>,\<Gamma>,\<Delta> \<turnstile> \<langle>cs, Normal ns\<rangle> [\<rightarrow>] s' \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (auto intro: RedLit elim: assert_ml)

lemma imp_conj_assoc: "(A \<and> B) \<and> C \<longrightarrow> D \<Longrightarrow> A \<and> (B \<and> C) \<longrightarrow> D"
  by simp

lemma imp_conj_imp: "(A \<and> B) \<longrightarrow> D \<Longrightarrow> A \<longrightarrow> (B \<longrightarrow> D)"
  by simp

lemma imp_conj_elim: "A \<and> B \<longrightarrow> D \<Longrightarrow> A \<Longrightarrow> ((B \<longrightarrow> D) \<Longrightarrow> R) \<Longrightarrow> R"
  by simp

lemma imp_not_elim: "\<not>A \<Longrightarrow> A \<Longrightarrow> (False \<Longrightarrow> R) \<Longrightarrow> R"
  by simp

lemma conj_elim_2: "A \<and> B \<Longrightarrow> (B \<Longrightarrow> R) \<Longrightarrow> R"
  by simp

lemma conj_imp_elim: "(A \<and> (A \<longrightarrow> B)) \<Longrightarrow> (B \<Longrightarrow> R) \<Longrightarrow> R"
  by simp

method tryRepeatConjI = ((rule conjI)+ | tactic \<open>all_tac\<close>)

(* use opaque composition to deal with lemmas such as "\<Gamma> ''f'' = Some ((the \<circ> \<Gamma>) ''f'')", which
lead to non-terminating tactics most likely due to \<Gamma> ''f'' appearing on both sides *)
definition opaque_comp 
  where "opaque_comp f g x = f (g x)"

lemma axioms_sat_mem: "a \<in> set(as) \<Longrightarrow> axioms_sat A \<Lambda> \<Gamma> ns as \<Longrightarrow> A,\<Lambda>,\<Gamma>,[] \<turnstile> \<langle>a, ns\<rangle> \<Down> LitV (LBool (True))"
  by (simp add: axioms_sat_def expr_sat_def list_all_iff)

lemma assume_red_bool:
"A,M,\<Lambda>,\<Gamma>,\<Delta> \<turnstile> \<langle>Assume e, Normal n_s\<rangle> \<rightarrow> s \<Longrightarrow>
    \<exists>b. A,\<Lambda>,\<Gamma>,\<Delta> \<turnstile> \<langle>e, n_s\<rangle> \<Down> BoolV b"
by (erule red_cmd.cases) auto

lemma assume_cases_2: 
  "\<lbrakk>A,M,\<Lambda>,\<Gamma>,\<Delta> \<turnstile> \<langle>Assume e, Normal n_s\<rangle> \<rightarrow> s; 
    s = Magic \<Longrightarrow> P; 
    s = Normal n_s \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (erule red_cmd.cases; simp)

lemma assume_cases_ext: 
  "\<lbrakk>A,M,\<Lambda>,\<Gamma>,\<Delta> \<turnstile> \<langle>Assume e, Normal n_s\<rangle> \<rightarrow> s; 
    s = Magic \<Longrightarrow> P; 
    s = Normal n_s \<Longrightarrow> A,\<Lambda>,\<Gamma>,\<Delta> \<turnstile> \<langle>e, n_s\<rangle> \<Down> LitV (LBool True) \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (erule red_cmd.cases; simp)

lemma assume_cases_ext_2: 
  "\<lbrakk>A,M,\<Lambda>,\<Gamma>,\<Delta> \<turnstile> \<langle>Assume e, s\<rangle> \<rightarrow> s'; 
    s = Normal n_s;
    s' = Magic \<Longrightarrow> P; 
    s' = Normal n_s \<Longrightarrow> A,\<Lambda>,\<Gamma>,\<Delta> \<turnstile> \<langle>e, n_s\<rangle> \<Down> LitV (LBool True) \<Longrightarrow>  P \<rbrakk> \<Longrightarrow> P"
  by (erule red_cmd.cases; simp)

lemma assume_ml: 
  "\<lbrakk>A,M,\<Lambda>,\<Gamma>,\<Delta> \<turnstile> \<langle>(Assume e) # cs, Normal ns\<rangle> [\<rightarrow>] s';
       s' = Magic \<Longrightarrow> P;
        A,\<Lambda>,\<Gamma>,\<Delta> \<turnstile> \<langle>e, ns\<rangle> \<Down> LitV (LBool True) \<Longrightarrow> A,M,\<Lambda>,\<Gamma>,\<Delta> \<turnstile> \<langle>cs, Normal ns\<rangle> [\<rightarrow>] s' \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  apply (erule RedCmdListCons_case)
  by (metis assume_cases_ext magic_stays_cmd_list)

lemma assume_false_cmds:
  "\<lbrakk>A,M,\<Lambda>,\<Gamma>,\<Delta> \<turnstile> \<langle>(Assume (Lit (LBool False))) # cs, Normal ns\<rangle> [\<rightarrow>] s';
       s' = Magic \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  apply (erule RedCmdListCons_case)
  by (metis RedAssertFail RedLit assert_correct assume_cases_ext magic_stays_cmd_list state.distinct(1))

  (*by (metis RedLit assume_cases_ext expr_eval_determ(1) magic_stays_cmd_list val.inject(1))*)

lemma assume_true_cmds: 
  "\<lbrakk>A,M,\<Lambda>,\<Gamma>,\<Delta> \<turnstile> \<langle>(Assume e) # cs, Normal ns\<rangle> [\<rightarrow>] s';
       s' = Magic \<Longrightarrow> P;
       A,M,\<Lambda>,\<Gamma>,\<Delta> \<turnstile> \<langle>cs, Normal ns\<rangle> [\<rightarrow>] s' \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (rule assume_ml)

lemma assume_red_true:
  assumes "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>Assume e, Normal ns\<rangle> \<rightarrow> s2" and "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e, ns\<rangle> \<Down> BoolV True"
  shows "s2 = Normal ns"
  using assms
  apply cases
  by (auto dest: expr_eval_determ(1))

lemma assume_red_false:
  assumes "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>Assume e, Normal ns\<rangle> \<rightarrow> s2" and "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e, ns\<rangle> \<Down> BoolV False"
  shows "s2 = Magic"
  using assms
  apply cases
  by (auto dest: expr_eval_determ(1))

lemma assume_determ:
  assumes "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>Assume e, s1\<rangle> \<rightarrow> s2" and "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>Assume e, s1\<rangle> \<rightarrow> s3"
  shows "s2 = s3"
  using assms
proof (cases s1)
  case (Normal ns)
  then show ?thesis 
  proof (cases "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e, ns\<rangle> \<Down> BoolV True")
    case True
    then show ?thesis using assms Normal 
      using assume_red_true by blast
  next
    case False
    then show ?thesis using assms Normal 
      by (metis assume_cases_ext)
  qed
qed (auto dest: failure_stays_cmd magic_stays_cmd)

lemma single_assign_cases:
  "\<lbrakk>A,M,\<Lambda>,\<Gamma>,\<Delta> \<turnstile> \<langle>Assign x e, s\<rangle> \<rightarrow> s'; 
   s = Normal n_s;
   \<And>v. A,\<Lambda>,\<Gamma>,\<Delta> \<turnstile> \<langle>e, n_s\<rangle> \<Down> v \<Longrightarrow> s' = Normal (update_var \<Lambda> n_s x v) \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (erule red_cmd.cases; simp)

lemma assign_intro_alt:
  "\<lbrakk> lookup_var_ty \<Lambda> x = Some ty; 
     A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e, n_s\<rangle> \<Down> v;
     type_of_val A v = instantiate \<Omega> ty  \<rbrakk> \<Longrightarrow>
   A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>Assign x e, Normal n_s\<rangle> \<rightarrow>  Normal (update_var \<Lambda> n_s x v)"
  by (auto intro: RedAssign)


lemma havoc_cases_no_cond:
  "\<lbrakk>A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>Havoc x, s\<rangle> \<rightarrow> s';
    s = Normal n_s;
    lookup_var_decl \<Lambda> x = Some (ty,None);
    \<And>v. type_of_val A v = instantiate \<Omega> ty \<Longrightarrow> s' = Normal (update_var \<Lambda> n_s x v) \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (erule red_cmd.cases; simp)

lemma havoc_cases_general:
  "\<lbrakk>A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>Havoc x, s\<rangle> \<rightarrow> s';
    s = Normal n_s;
    \<And>v ty c w. lookup_var_decl \<Lambda> x = Some (ty,w) \<Longrightarrow> type_of_val A v = instantiate \<Omega> ty \<Longrightarrow> (w = Some c \<Longrightarrow> A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>c,(update_var \<Lambda> n_s x v)\<rangle> \<Down> BoolV True) \<Longrightarrow> s' = Normal (update_var \<Lambda> n_s x v) \<Longrightarrow> P;
    \<And>v ty c. lookup_var_decl \<Lambda> x = Some (ty, Some c) \<Longrightarrow> type_of_val A v = instantiate \<Omega> ty \<Longrightarrow> (A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>c,(update_var \<Lambda> n_s x v)\<rangle> \<Down> BoolV False) \<Longrightarrow> s' = Magic \<Longrightarrow> P\<rbrakk> \<Longrightarrow> 
    P"
  by (erule red_cmd.cases; auto)
  
(*
lemma havoc_cases_2:
  "\<lbrakk>A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>Havoc x, s\<rangle> \<rightarrow> s';
    s = Normal n_s;
    \<And>v w ty. lookup_var_decl \<Lambda> x = Some (ty,None) \<Longrightarrow> type_of_val A v = instantiate \<Omega> ty \<Longrightarrow> s' = Normal (update_var \<Lambda> n_s x v) \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using havoc_cases
*)

lemma type_of_val_int_elim:
  "\<lbrakk> type_of_val A v = TPrim TInt;
     \<And>i. v = LitV (LInt i) \<Longrightarrow> P
   \<rbrakk> \<Longrightarrow> P"
  apply (cases v)
   apply auto[2]
  by (metis prim_ty.distinct(1) prim_ty.distinct(5) type_of_lit.simps(1) type_of_lit.simps(3) unop_minus.cases)

lemma type_of_val_bool_elim:
  "\<lbrakk> type_of_val A v = TPrim TBool;
     \<And>b. v = LitV (LBool b) \<Longrightarrow> P
   \<rbrakk> \<Longrightarrow> P"
  apply (cases v)
   apply auto[2]
  by (metis prim_ty.distinct(1) prim_ty.distinct(3) type_of_lit.simps(2) type_of_lit.simps(3) unop_minus.cases)

lemma type_of_val_real_elim:
  "\<lbrakk> type_of_val A v = TPrim TReal;
     \<And>r. v = LitV (LReal r) \<Longrightarrow> P
   \<rbrakk> \<Longrightarrow> P"
  apply (cases v)
   apply auto[2]
  by (metis prim_ty.distinct(3) prim_ty.distinct(5) type_of_lit.simps(1) type_of_lit.simps(2) unop_minus.cases)
 
lemma val_elim [elim!]:
 "\<lbrakk> A,\<Lambda>,\<Gamma>,\<Delta> \<turnstile> \<langle>Lit l, n_s\<rangle> \<Down> v'; (LitV l) = v' \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (erule red_expr.cases; simp)

lemma cons_exp_elim :
 "A,\<Lambda>,\<Gamma>,\<Delta> \<turnstile> \<langle>e # es, n_s\<rangle> [\<Down>] vs \<Longrightarrow> (vs \<noteq> [] \<Longrightarrow> A,\<Lambda>,\<Gamma>,\<Delta> \<turnstile> \<langle>e, n_s\<rangle> \<Down> hd vs \<Longrightarrow> A,\<Lambda>,\<Gamma>,\<Delta> \<turnstile> \<langle>es, n_s\<rangle> [\<Down>] tl vs \<Longrightarrow> P) \<Longrightarrow> P"
  by (erule red_exprs.cases; simp_all)

lemma cons_exp_elim2:
  "\<lbrakk>A,\<Lambda>,\<Gamma>,\<Delta> \<turnstile> \<langle>e # es, n_s\<rangle> [\<Down>] vs;
   \<And>v vs'. vs = v # vs' \<Longrightarrow> A,\<Lambda>,\<Gamma>,\<Delta> \<turnstile> \<langle>e, n_s\<rangle> \<Down> v \<Longrightarrow> A,\<Lambda>,\<Gamma>,\<Delta> \<turnstile> \<langle>es, n_s\<rangle> [\<Down>] vs' \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P" 
  by (erule red_exprs.cases; simp_all)

lemma singleton_exp:
  "A,\<Lambda>,\<Gamma>,\<Delta> \<turnstile> \<langle>[e], n_s\<rangle> [\<Down>] vs \<Longrightarrow> A,\<Lambda>,\<Gamma>,\<Delta> \<turnstile> \<langle>e, n_s\<rangle> \<Down> hd vs"
  by (auto elim: cons_exp_elim)

lemma nil_exp_elim [elim!]:
 "\<lbrakk>A,\<Lambda>,\<Gamma>,\<Delta> \<turnstile> \<langle>[], n_s\<rangle> [\<Down>] vs; vs = [] \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
 by (erule red_exprs.cases; simp)


lemma nil_cmd_elim [elim!]:
 "\<lbrakk>A,M,\<Lambda>,\<Gamma>,\<Delta> \<turnstile> \<langle>[], s\<rangle> [\<rightarrow>] s'; s' = s \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (erule red_cmd_list.cases; simp)

lemma magic_stays_cmd_list_2:
  assumes "A,M,\<Lambda>,\<Gamma>,\<Delta> \<turnstile> \<langle>cs, s\<rangle> [\<rightarrow>] s'" and "s = Magic"
  shows   "s' = Magic"
  using assms
  by (simp add: magic_stays_cmd_list)

lemma red_cfg_multi_backwards_step:
  assumes
   Red: "A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl m, (Normal  n_s)) -n\<rightarrow>* (m', s')" and
   Block: "node_to_block G ! m = cs" and
   BlockCorrect: "\<And> s''. A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs, Normal n_s\<rangle> [\<rightarrow>] s'' \<Longrightarrow> 
            s'' \<noteq> Failure \<and> (\<forall>  n_s'. ((s'' = (Normal  n_s')) \<longrightarrow> (n_s' = n_s) \<and> vcsuc))" and
   SuccCorrect:"\<And> msuc s2 m2. List.member (out_edges(G) ! m) msuc \<Longrightarrow> A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl(msuc), Normal n_s) -n\<rightarrow>* (m2, s2) \<Longrightarrow> vcsuc \<Longrightarrow> s2 \<noteq> Failure"
shows "s' \<noteq> Failure"
  using assms
proof (cases rule: converse_rtranclpE2[OF assms(1)])
  case 1
  then show ?thesis by auto
next
  case (2 a b)
  then show ?thesis
  proof (cases rule: red_cfg.cases)
    case (RedNormalSucc cs ns' n')
    with BlockCorrect Block  have "ns' = n_s" and "vcsuc" by auto
    then show ?thesis
      using 2 SuccCorrect RedNormalSucc by blast
  next
  case (RedNormalReturn cs ns')
    then show ?thesis using 2 finished_remains by blast 
  next
    case (RedFailure cs)
  then show ?thesis using 2 BlockCorrect Block by blast
  next
    case (RedMagic cs)
  then show ?thesis using 2 finished_remains by blast 
  qed
qed

lemma red_cfg_multi_backwards_step_2:
  assumes
   Red: "A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl m, (Normal  n_s)) -n\<rightarrow>* (m', s')" and
   Block: "node_to_block G ! m = cs" and
   BlockCorrect: "\<And> s''. A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs, Normal n_s\<rangle> [\<rightarrow>] s'' \<Longrightarrow> 
            s'' \<noteq> Failure \<and> (\<forall>  n_s'. ((s'' = (Normal  n_s')) \<longrightarrow> (n_s' = n_s)))" and
   SuccCorrect:"\<And> msuc s2 m2. List.member (out_edges(G) ! m) msuc \<Longrightarrow> A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl(msuc), Normal n_s) -n\<rightarrow>* (m2, s2) \<Longrightarrow> s2 \<noteq> Failure"
 shows "s' \<noteq> Failure"
  apply (rule red_cfg_multi_backwards_step[where ?vcsuc=True])
  using assms by auto  
  

lemma red_cfg_multi_backwards_step_no_succ:
  assumes
   Red: "A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl m, (Normal  n_s)) -n\<rightarrow>* (m', s')" and
   Block: "node_to_block G ! m = cs" and
   NoSucc: "out_edges G ! m = []" and
   BlockCorrect: "\<And> s''. A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs, Normal n_s\<rangle> [\<rightarrow>] s'' \<Longrightarrow> 
            s'' \<noteq> Failure \<and> (\<forall>  n_s'. ((s'' = (Normal  n_s')) \<longrightarrow> (n_s' = n_s)))"
shows "s' \<noteq> Failure"
  using assms
proof (cases rule: converse_rtranclpE2[OF assms(1)])
  case 1
  then show ?thesis by auto
next
  case (2 a b)
  then show ?thesis
  proof (cases rule: red_cfg.cases)
    case (RedNormalSucc cs ns' n')
    then show ?thesis using NoSucc
      by (simp add: member_rec(2))  
  next
  case (RedNormalReturn cs ns')
    then show ?thesis using 2 finished_remains by blast 
  next
    case (RedFailure cs)
  then show ?thesis using 2 BlockCorrect Block by blast
  next
    case (RedMagic cs)
  then show ?thesis using 2 finished_remains by blast 
  qed
qed

lemma red_cfg_multi_backwards_step_magic:
  assumes
   Red: "A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl m, (Normal  n_s)) -n\<rightarrow>* (m', s')" and
   Block: "node_to_block G ! m = cs" and   
   BlockCorrect: "\<And> s''. A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs, Normal n_s\<rangle> [\<rightarrow>] s'' \<Longrightarrow> s'' = Magic"
shows "s' \<noteq> Failure"
  using assms
proof (cases rule: converse_rtranclpE2[OF assms(1)])
  case 1
  then show ?thesis by auto
next
  case (2 a b)
  then show ?thesis
  proof (cases rule: red_cfg.cases)
    case (RedNormalSucc cs ns' n')
    then show ?thesis using BlockCorrect Block by blast
  next
  case (RedNormalReturn cs ns')
    then show ?thesis using BlockCorrect Block by blast 
  next
    case (RedFailure cs)
  then show ?thesis using BlockCorrect Block by blast
  next
    case (RedMagic cs)
  then show ?thesis using 2 finished_remains by blast 
  qed
qed
   
lemma red_cfg_multi_backwards_step_no_succ:
  assumes
   Red: "A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl m, (Normal  n_s)) -n\<rightarrow>* (m', s')" and
   Block: "node_to_block G ! m = cs" and
   BlockCorrect: "\<And> s''. A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs, Normal n_s\<rangle> [\<rightarrow>] s'' \<Longrightarrow> 
            s'' \<noteq> Failure \<and> (\<forall>  n_s'. ((s'' = (Normal  n_s')) \<longrightarrow> (n_s' = n_s)))" and
   SuccCorrect:"\<And> msuc s2 m2. List.member (out_edges(G) ! m) msuc \<Longrightarrow> A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl(msuc), Normal n_s) -n\<rightarrow>* (m2, s2) \<Longrightarrow>  s2 \<noteq> Failure"
 shows "s' \<noteq> Failure"
  oops

lemma member_elim: 
   "List.member (x#xs) y \<Longrightarrow> (x = y \<Longrightarrow> P x) \<Longrightarrow> (List.member xs y \<Longrightarrow> P y) \<Longrightarrow> P y"
  by (metis member_rec(1))

lemma max_min_disjoint: 
  assumes "Max (set xs) < Min (set ys)"
  shows "set xs \<inter> set ys = {}"
  using assms
  by (metis Diff_Diff_Int Diff_eq_empty_iff List.finite_set Max_ge Min_le_iff disjoint_iff_not_equal inf.cobounded2 leD)

lemma max_min_disjoint_2:
  assumes "\<forall> a. a \<in> A \<longrightarrow> a \<le> a_max"
      and "\<forall> b. b \<in> B \<longrightarrow> b_min \<le> (b :: vname)"
      and "a_max < b_min"
    shows "A \<inter> B = {}"
  using assms
  by fastforce

lemma dom_map_of_2:"dom (map_of R) = set (map fst R)"
  by (simp add: Map.dom_map_of_conv_image_fst)

lemma lookup_var_global_disj: "set (map fst G) \<inter> set (map fst L) = {} \<Longrightarrow> map_of G x = Some y \<Longrightarrow> lookup_var (G,L) n_s x = global_state n_s x"
  by (metis disjoint_iff_not_equal domI domIff dom_map_of_2 lookup_var_global)

lemma lookup_var_global_no_locals: "lookup_var (G,[]) n_s x = global_state n_s x"
  unfolding lookup_var_def
  by simp

lemma globals_locals_helper:
  assumes "\<forall> a. a \<in> A \<longrightarrow> a \<le> a_max"
      and "\<forall> b. b \<in> B \<longrightarrow> b_min \<le> (b :: vname)"
      and "a_max < b_min"
    shows "A \<inter> B = {}"
  using assms
  by fastforce

lemma map_of_append:
"map_of (xs1) x = Some y \<Longrightarrow> map_of (xs1@xs2) x = Some y"
  by simp

lemma update_var_same_state:
  assumes "lookup_var \<Lambda> ns x = Some v"
  shows "update_var \<Lambda> ns x v = ns" (is "?ns' = ns")
  using assms update_var_def lookup_var_def
proof (cases "map_of (snd \<Lambda>) x")
  case None
  hence update_global:"?ns' = ns\<lparr>global_state := (global_state(ns))(x \<mapsto> v)\<rparr>"
    by (simp add: update_var_def)

  from assms have global_ns:"global_state ns x = Some v"
    by (metis None lookup_var_global prod.collapse)

  have "(global_state(ns))(x \<mapsto> v) = global_state ns"
    apply (rule HOL.ext)
    by (simp add: global_ns)
  then show ?thesis 
    using update_global
    by simp
next
  case (Some a)
  hence update_local:"?ns' = ns\<lparr>local_state := (local_state(ns))(x \<mapsto> v)\<rparr>"
    by (simp add: update_var_def)

  from assms have local_ns:"local_state ns x = Some v"
    by (metis Some lookup_var_local prod.collapse)

  have "(local_state(ns))(x \<mapsto> v) = local_state ns"
    apply (rule HOL.ext)
    by (simp add: local_ns)
  then show ?thesis 
    using update_local
    by simp
qed

lemma lookup_var_const_restr_util_1:
  assumes "set (map fst (C@G)) \<inter> set (map fst L) = {}"
          "map_of C x = Some \<tau>"
    shows "lookup_var (C@G, L) ns x = lookup_var (C,[]) ns x"
  using assms
  by (simp add: lookup_var_global_disj)

lemma lookup_var_const_restr_util_2:
  assumes "map_of C x = Some \<tau>"
  shows "lookup_var (C,[]) ns x = lookup_var (C,[]) (nstate_global_restriction ns C) x"
proof -
  let ?ns' = "nstate_global_restriction ns C"
  from assms have "lookup_var (C,[]) ns x = global_state ns x"
    by (simp add: lookup_var_global_no_locals)
  moreover from assms have "lookup_var (C, []) ?ns' x = (state_restriction (global_state ns) C) x"
    by (simp add: nstate_global_restriction_def lookup_var_global_no_locals)

  moreover from assms have "global_state ns x = (state_restriction (global_state ns) C) x"
    unfolding state_restriction_def
    by simp
  ultimately show ?thesis
    by simp
qed

lemma lookup_var_const_restr_util_ty_2:
  assumes "map_option fst (map_of C x) =  Some \<tau>"
  shows "lookup_var (C,[]) ns x = lookup_var (C,[]) (nstate_global_restriction ns C) x"
  using assms lookup_var_const_restr_util_2
  by fastforce

lemma lookup_var_const_restr:
  assumes "set (map fst (C@G)) \<inter> set (map fst L) = {}"
          "map_of C x = Some \<tau>"
        shows "lookup_var (C@G, L) ns x = lookup_var (C,[]) (nstate_global_restriction ns C) x"
  using assms lookup_var_const_restr_util_1 lookup_var_const_restr_util_2
  by metis

lemma state_typ_wf_const_restr:
  assumes "state_typ_wf  A [] (global_state n_s) (C@G)"
  shows "state_typ_wf A [] (global_state (nstate_global_restriction n_s C)) C"
  unfolding state_typ_wf_def lookup_vdecls_ty_def  
proof (rule allI, rule allI, rule impI)
  fix v t
  assume "map_option fst (map_of C v) = Some t"
  moreover from this have "map_option (type_of_val A) (global_state n_s v) = Some t"
    using assms
    unfolding state_typ_wf_def lookup_vdecls_ty_def
    by force  
  ultimately show "map_option (type_of_val A) (global_state (nstate_global_restriction n_s C) v) = Some (instantiate [] t)"    
    by (metis instantiate_nil lookup_var_const_restr_util_ty_2 lookup_var_global_no_locals)
qed

lemma helper_max:
  assumes "xs \<noteq> [] \<Longrightarrow> Max (set xs) \<le> n_max" "x \<in> set xs"
  shows "x \<le> n_max"
  using assms
  by force

lemma helper_min:
  assumes "xs \<noteq> [] \<Longrightarrow> Min (set xs) \<ge> n_min" "x \<in> set xs"
  shows "x \<ge> n_min"
  using assms
  by force

lemma red_cmd_list_append:
  assumes "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs1,s\<rangle> [\<rightarrow>] s''" and
          "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs2,s''\<rangle> [\<rightarrow>] s'"
  shows "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs1@cs2,s\<rangle> [\<rightarrow>] s'"
  using assms
  by (induction) (auto intro: red_cmd_list.RedCmdListCons)

lemma lookup_ty_pred:
  assumes "lookup_var_ty \<Lambda> x = Some \<tau>" and
          PredGlobal:"list_all (P \<circ> fst \<circ> snd) (fst \<Lambda>)" and
          PredLocal:"list_all (P \<circ> fst \<circ> snd) (snd \<Lambda>)"
  shows "P \<tau>"
proof (cases "map_of (snd \<Lambda>) x = None")
  case True  
  from this obtain w where "map_of (fst \<Lambda>) x = Some (\<tau>,w)"
    using \<open>lookup_var_ty \<Lambda> x = Some \<tau>\<close> lookup_var_ty_decl_Some lookup_var_decl_global_3 by blast
  hence "(x,(\<tau>,w)) \<in> set (fst \<Lambda>)" by (simp add: map_of_SomeD)
  then have "(x,(\<tau>,w)) \<in> set (fst \<Lambda>)" by (simp add: map_of_SomeD) 
  moreover from PredGlobal have "\<forall>r \<in> set (fst \<Lambda>). (P \<circ> fst \<circ> snd) r" by (simp add:  List.list_all_iff)
  ultimately have "(P \<circ> fst \<circ> snd) (x,(\<tau>,w))" by blast
  thus ?thesis by simp
next
  case False
  from this obtain w where "map_of (snd \<Lambda>) x = Some (\<tau>,w)"
    using \<open>lookup_var_ty \<Lambda> x = Some \<tau>\<close> lookup_var_ty_decl_Some lookup_var_decl_local
    by (metis option.exhaust_sel)
  then have "(x,(\<tau>,w)) \<in> set (snd \<Lambda>)" by (simp add: map_of_SomeD) 
  moreover from PredLocal have "\<forall>r \<in> set (snd \<Lambda>). (P \<circ> fst \<circ> snd) r" by (simp add:  List.list_all_iff)
  ultimately have "(P \<circ> fst \<circ> snd) (x,(\<tau>,w))" by blast
  thus ?thesis by simp
qed

lemma lookup_ty_pred_2:
  assumes "list_all (P \<circ> (fst \<circ> snd)) (fst \<Lambda>)" and
          "list_all (P \<circ> (fst \<circ> snd)) (snd \<Lambda>)"
  shows "\<forall>x \<tau>. lookup_var_ty \<Lambda> x = Some \<tau> \<longrightarrow> P \<tau>"
  using assms lookup_ty_pred
  unfolding comp_def
  by blast

lemma vars_min_helper:
  assumes "map fst (params_vdecls_swap @ locals_vdecls_swap) \<noteq> [] \<longrightarrow> m \<le> Min (set (map fst (params_vdecls_swap @ locals_vdecls_swap)))"
  shows "\<forall>x. x \<in> set (map fst (params_vdecls_swap @ locals_vdecls_swap)) \<longrightarrow> m \<le> x"
  using assms
  by auto

(* new version *)
method reduce_expr_full = 
        (( erule RedBinOp_case |
           erule RedFunOp_case |
           erule RedUnOp_case |
           erule val_elim |
           erule cons_exp_elim2 | 
           erule RedVar_case |
           erule nil_exp_elim))+

method assm_init_full = 
 ( erule assume_cases_ext_2,
   simp?,
  ((frule magic_stays_cmd_list_2), assumption, simp))

method handle_assume_full = ( assm_init_full, reduce_expr_full)

method reduce_assert_expr_full = 
  ((
          (rule RedVar |
          rule RedLit|
          rule RedBinOp |
          rule RedUnOp |
          rule RedFunOp |
          rule RedExpListNil |
          rule RedExpListCons)) |
  ((match conclusion in 
                       "?R = Some ?x" \<Rightarrow> \<open>fail?\<close>), (solves simp | solves fastforce) )
 (* Hack: 
    fastforce will only be executed,if match works, putting fastforce inside the match does not 
    seem to work: I guess the assumptions are not available *)
     )+

method handle_assert_full = (drule assert_correct_2, (assumption | simp)?, reduce_assert_expr_full)

(* simp is used in second subgoal if assertion is first command in list
   in that case, the goal is of the form "Normal n_s = Normal (?n_s3 s'a)", hence no assumption
   is used *)
method handle_assign_full = (erule single_assign_cases, (assumption | simp), reduce_expr_full)

method handle_havoc_full uses v_assms = 
(erule havoc_cases_no_cond, (assumption | simp), (simp only: v_assms),
 (erule type_of_val_int_elim | erule type_of_val_bool_elim)
)

method handle_cmd_list_full uses v_assms = 
(
  (( ( handle_assume_full | handle_assert_full |
        handle_assign_full | (handle_havoc_full v_assms: v_assms)),
      (erule RedCmdListCons_case | erule nil_cmd_elim) )
   )+
)

lemmas relpowp_E2_2 =
  relpowp_E2[of _ _ "(n', s')" "(n'',s'')", split_rule]

end