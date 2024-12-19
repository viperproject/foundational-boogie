section \<open>Generic lemmas used to validate AST-to-CFG phase\<close>

theory Ast_Cfg_Transformation
  imports Main Ast Semantics BackedgeElim
begin

type_synonym 'a satisfies_spec_func_type = 
  "'a absval_ty_fun \<Rightarrow> mbodyCFG proc_context \<Rightarrow> var_context \<Rightarrow> 'a fun_interp \<Rightarrow> rtype_env \<Rightarrow> expr list \<Rightarrow> expr list \<Rightarrow> ast \<Rightarrow> 'a nstate \<Rightarrow> bool"

subsection \<open>Syntactic helper relations\<close>

inductive syntactic_equiv :: "expr \<Rightarrow> expr \<Rightarrow> bool" (infixl "\<sim>" 40) 
  where
    neg_refl:   "UnOp Not e1 \<sim> UnOp Not e1"
  | neg_equiv1: "UnOp Not (Lit (LBool True)) \<sim> (Lit (LBool False))"
  | neg_equiv2: "UnOp Not (Lit (LBool False)) \<sim> (Lit (LBool True))"
  | double_neg: "UnOp Not (UnOp Not e1) \<sim> e1"
  | neg_eq:     "UnOp Not (a \<guillemotleft>Eq\<guillemotright> b) \<sim> (a \<guillemotleft>Neq\<guillemotright> b)"
  | neg_neq:    "UnOp Not (a \<guillemotleft>Neq\<guillemotright> b) \<sim> (a \<guillemotleft>Eq\<guillemotright> b)"
  | neg_lt:     "UnOp Not (a \<guillemotleft>Lt\<guillemotright> b) \<sim> (b \<guillemotleft>Le\<guillemotright> a)"
  | neg_le:     "UnOp Not (a \<guillemotleft>Le\<guillemotright> b) \<sim> (b \<guillemotleft>Lt\<guillemotright> a)"
  | neg_gt:     "UnOp Not (a \<guillemotleft>Gt\<guillemotright> b) \<sim> (b \<guillemotleft>Ge\<guillemotright> a)"
  | neg_ge:     "UnOp Not (a \<guillemotleft>Ge\<guillemotright> b) \<sim> (b \<guillemotleft>Gt\<guillemotright> a)"

inductive ast_cfg_rel :: "expr option \<Rightarrow> cmd list \<Rightarrow> bigblock \<Rightarrow> cmd list \<Rightarrow> bool"
  where 
    Rel_Guard_true:
    "\<lbrakk>bb = (BigBlock name cs1 any_str any_tr); ast_cfg_rel None [] bb cs2\<rbrakk> \<Longrightarrow>
        ast_cfg_rel (Some block_guard) [] bb ((Assume block_guard) # cs2)"
  | Rel_Guard_false:
    "\<lbrakk>bb = (BigBlock name cs1 any_str any_tr); ast_cfg_rel None [] bb cs2; (UnOp Not block_guard) \<sim> c \<rbrakk> \<Longrightarrow>
        ast_cfg_rel (Some block_guard) [] bb ((Assume c) # cs2)"
  | Rel_Invs:
    "\<lbrakk>bb = (BigBlock name [] any_str any_tr)\<rbrakk> \<Longrightarrow> ast_cfg_rel None assertions bb assertions"
  | Rel_Main_test:
    "\<lbrakk>bb = (BigBlock name cs1 any_str any_tr); cs1 = c#cs\<rbrakk> \<Longrightarrow> ast_cfg_rel None [] bb cs1"

subsection \<open>Miscellaneous helper lemmas\<close>

lemma not_true_equals_false:
  assumes "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>UnOp unop.Not expr, ns1\<rangle> \<Down> BoolV True"
  shows "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>expr, ns1\<rangle> \<Down> BoolV (False)"  
  using assms
proof cases
  case (RedUnOp v)
  from this obtain b1 where "v = LitV (LBool b1)"
    by (metis (no_types) map_option_eq_Some option.simps(3) unop_eval.simps(1) unop_eval_val.elims unop_not.elims)   
  from this RedUnOp have 
    expand1: "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>expr,ns1\<rangle> \<Down> (LitV (LBool b1))" and 
    expand2: "unop_eval_val unop.Not (LitV (LBool b1)) = Some (BoolV True)"
    by auto
  then show ?thesis by fastforce
qed

lemma not_false_equals_true:
  assumes "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>UnOp unop.Not expr, ns1\<rangle> \<Down> BoolV False"
  shows "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>expr, ns1\<rangle> \<Down> BoolV (True)"  
  using assms
proof cases
  case (RedUnOp v)
  from this obtain b1 where "v = LitV (LBool b1)"
    by (auto elim: lit_val_elim[where v=v])      
  with RedUnOp have 
    expand1: "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>expr,ns1\<rangle> \<Down> (LitV (LBool b1))" and 
    expand2: "unop_eval_val unop.Not (LitV (LBool b1)) = Some (BoolV False)"
    by auto
  then show ?thesis by fastforce
qed

lemma true_equals_not_false:
  assumes "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>expr, ns1\<rangle> \<Down> BoolV True"
  shows "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>UnOp unop.Not expr, ns1\<rangle> \<Down> BoolV (False)"
  using assms by (auto intro: RedUnOp)

lemma false_equals_not_true:
  assumes "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>expr, ns1\<rangle> \<Down> BoolV False"
  shows "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>UnOp unop.Not expr, ns1\<rangle> \<Down> BoolV (True)"
  using assms by (auto intro: RedUnOp)

lemma equiv_preserves_value:
  assumes "a \<sim> b"
    and "red_expr A \<Lambda> \<Gamma> \<Omega> a ns (BoolV boolean)"
  shows "red_expr A \<Lambda> \<Gamma> \<Omega> b ns (BoolV boolean)"
  using assms
proof cases
  case (neg_refl e1)
  then show ?thesis using assms by simp
next
  case neg_equiv1
  then show ?thesis using assms by (metis (full_types) RedLit not_true_equals_false val_elim)
next
  case neg_equiv2
  then show ?thesis using assms by (metis (full_types) RedLit not_false_equals_true val_elim)
next
  case double_neg
  then show ?thesis using assms by (metis (full_types) not_false_equals_true not_true_equals_false)
next
  case (neg_eq e1 e2)
  from this assms have unop_red: "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>UnOp unop.Not (e1 \<guillemotleft>Eq\<guillemotright> e2), ns\<rangle> \<Down> BoolV boolean" by simp
  from this obtain v1 v2 bopRes where
    redE1: "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e1, ns\<rangle> \<Down> v1" and
    redE2: "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e2, ns\<rangle> \<Down> v2" and
    binopEval: "binop_eval_val Eq v1 v2 = Some bopRes" and
    unopEval: "unop_eval_val unop.Not bopRes = Some (BoolV boolean)"
    by auto

  have bopResEq:"bopRes = BoolV (\<not>boolean)" 
    by (insert unopEval, rule lit_val_elim[where v=bopRes]) auto

  have "binop_eval_val Neq v2 v1 = Some (BoolV boolean)"
    apply (insert binopEval bopResEq)
    apply (rule lit_val_elim[where v=v2]; rule lit_val_elim[where v=v1])
    by auto

  thus ?thesis
    by (auto intro: RedBinOp redE1 redE2 simp: \<open>b = _\<close>)
next
  case (neg_neq e1 e2)
  from this assms have unop_red: "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>UnOp unop.Not (e1 \<guillemotleft>Neq\<guillemotright> e2), ns\<rangle> \<Down> BoolV boolean" by simp
  from this obtain v1 v2 bopRes where
    redE1: "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e1, ns\<rangle> \<Down> v1" and
    redE2: "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e2, ns\<rangle> \<Down> v2" and
    binopEval: "binop_eval_val Neq v1 v2 = Some bopRes" and
    unopEval: "unop_eval_val unop.Not bopRes = Some (BoolV boolean)"
    by auto

  have bopResEq:"bopRes = BoolV (\<not>boolean)" 
    by (insert unopEval, rule lit_val_elim[where v=bopRes]) auto

  have "binop_eval_val Eq v2 v1 = Some (BoolV boolean)"
    apply (insert binopEval bopResEq)
    apply (rule lit_val_elim[where v=v2]; rule lit_val_elim[where v=v1])
    by auto

  thus ?thesis
    by (auto intro: RedBinOp redE1 redE2 simp: \<open>b = _\<close>)
next
  case (neg_lt e1 e2)
  from this assms have unop_red: "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>UnOp unop.Not (e1 \<guillemotleft>Lt\<guillemotright> e2), ns\<rangle> \<Down> BoolV boolean" by simp
  from this obtain v1 v2 bopRes where
    redE1: "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e1, ns\<rangle> \<Down> v1" and
    redE2: "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e2, ns\<rangle> \<Down> v2" and
    binopEval: "binop_eval_val Lt v1 v2 = Some bopRes" and
    unopEval: "unop_eval_val unop.Not bopRes = Some (BoolV boolean)"
    by auto

  have bopResEq:"bopRes = BoolV (\<not>boolean)"     
    by (insert unopEval, rule lit_val_elim[where v=bopRes]) auto

  have "binop_eval_val Le v2 v1 = Some (BoolV boolean)"
    apply (insert binopEval bopResEq)
    apply (rule lit_val_elim[where v=v2]; rule lit_val_elim[where v=v1])
    by auto

  thus ?thesis
    by (auto intro: RedBinOp redE1 redE2 simp: \<open>b = _\<close>)
next
  case (neg_le e1 e2)
  from this assms have unop_red: "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>UnOp unop.Not (e1 \<guillemotleft>Le\<guillemotright> e2), ns\<rangle> \<Down> BoolV boolean" by simp
  from this obtain v1 v2 bopRes where
    redE1: "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e1, ns\<rangle> \<Down> v1" and
    redE2: "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e2, ns\<rangle> \<Down> v2" and
    binopEval: "binop_eval_val Le v1 v2 = Some bopRes" and
    unopEval: "unop_eval_val unop.Not bopRes = Some (BoolV boolean)"
    by auto

  have bopResEq:"bopRes = BoolV (\<not>boolean)" 
    by (insert unopEval, rule lit_val_elim[where v=bopRes]) auto

  have "binop_eval_val Lt v2 v1 = Some (BoolV boolean)"
    apply (insert binopEval bopResEq)
    apply (rule lit_val_elim[where v=v2]; rule lit_val_elim[where v=v1])
    by auto

  thus ?thesis
    by (auto intro: RedBinOp redE1 redE2 simp: \<open>b = _\<close>)
next
  case (neg_gt e1 e2)
  from this assms have unop_red: "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>UnOp unop.Not (e1 \<guillemotleft>Gt\<guillemotright> e2), ns\<rangle> \<Down> BoolV boolean" by simp
  from this obtain v1 v2 bopRes where
    redE1: "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e1, ns\<rangle> \<Down> v1" and
    redE2: "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e2, ns\<rangle> \<Down> v2" and
    binopEval: "binop_eval_val Gt v1 v2 = Some bopRes" and
    unopEval: "unop_eval_val unop.Not bopRes = Some (BoolV boolean)"
    by auto

  have bopResEq:"bopRes = BoolV (\<not>boolean)" 
    by (insert unopEval, rule lit_val_elim[where v=bopRes]) auto

  have "binop_eval_val Ge v2 v1 = Some (BoolV boolean)"
    apply (insert binopEval bopResEq)
    apply (rule lit_val_elim[where v=v2]; rule lit_val_elim[where v=v1])
    by auto

  thus ?thesis
    by (auto intro: RedBinOp redE1 redE2 simp: \<open>b = _\<close>)
next
  case (neg_ge e1 e2)
  from this assms have unop_red: "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>UnOp unop.Not (e1 \<guillemotleft>Ge\<guillemotright> e2), ns\<rangle> \<Down> BoolV boolean" by simp
  from this obtain v1 v2 bopRes where
    redE1: "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e1, ns\<rangle> \<Down> v1" and
    redE2: "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e2, ns\<rangle> \<Down> v2" and
    binopEval: "binop_eval_val Ge v1 v2 = Some bopRes" and
    unopEval: "unop_eval_val unop.Not bopRes = Some (BoolV boolean)"
    by auto

  have bopResEq:"bopRes = BoolV (\<not>boolean)" 
    by (insert unopEval, rule lit_val_elim[where v=bopRes]) auto

  have "binop_eval_val Gt v2 v1 = Some (BoolV boolean)"
    apply (insert binopEval bopResEq)
    apply (rule lit_val_elim[where v=v2]; rule lit_val_elim[where v=v1])
    by auto

  thus ?thesis
    by (auto intro: RedBinOp redE1 redE2 simp: \<open>b = _\<close>)
qed

text \<open>If all invariants hold, then the block containing the assertions corresponding to the invariants doesn't fail\<close>
lemma asserts_hold_if_invs_hold: 
  assumes "expr_all_sat A \<Lambda> \<Gamma> \<Omega> ns1 invs"
      and "assertions = map Assert invs"
    shows "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>assertions, Normal ns1\<rangle> [\<rightarrow>] Normal ns1"
  using assms
proof (induction invs arbitrary: assertions)
  case Nil
  then show ?case  by (simp add: RedCmdListNil)
next
  case (Cons e_inv invs_tail)
  from Cons(2) have prem1: "expr_all_sat A \<Lambda> \<Gamma> \<Omega> ns1 invs_tail" by (simp add: expr_all_sat_def)
  from Cons(3) have prem2: "List.tl assertions = map Assert invs_tail" by simp
  from prem1 prem2 have end2: "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>List.tl assertions,Normal ns1\<rangle> [\<rightarrow>] Normal ns1" 
    using Cons(1) by blast

  from Cons(2) have act1: "expr_sat A \<Lambda> \<Gamma> \<Omega> ns1 e_inv" by (simp add: expr_all_sat_def)
  from Cons(3) have act2: "List.hd assertions = (Assert e_inv)" by simp
  from act1 act2 have end1: "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>List.hd assertions,Normal ns1\<rangle> \<rightarrow> Normal ns1" 
    by (simp add: expr_sat_def red_cmd.intros(1))

  then show ?case using end1 end2 by (simp add: Cons.prems(2) RedCmdListCons)
qed

text \<open>If the block containing the assertions corresponding to the invariants doesn't fail, then all invariants hold\<close>
lemma invs_hold_if_asserts_reduce: 
  assumes "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>assertions, s0\<rangle> [\<rightarrow>] s1"
      and "s0 = Normal ns1"
      and "s1 \<noteq> Failure"
      and "assertions = map Assert invs"
    shows "expr_all_sat A \<Lambda> \<Gamma> \<Omega> ns1 invs"
  using assms
proof (induction arbitrary: invs rule: red_cmd_list.induct)
  case (RedCmdListNil s)
  hence "invs = []" by simp
  then show ?case by (simp add: expr_all_sat_def)
next
  case (RedCmdListCons c s s'' cs s')  
  from RedCmdListCons have "cs = map Assert (List.tl invs)" using assms by auto
  from RedCmdListCons have "c = Assert (hd invs)" by auto 

  from RedCmdListCons this \<open>s = Normal ns1\<close> show ?case
  proof cases
    case RedAssertOk thus ?thesis 
      using RedCmdListCons \<open>c = Assert (hd invs)\<close> \<open>s = Normal ns1\<close> \<open>cs = map Assert (List.tl invs)\<close> 
      by (metis RedCmdListCons.IH RedCmdListCons.prems(2)
          RedCmdListCons.prems(3) cmd.inject(1) expr_all_sat_def expr_sat_def 
          list.collapse list.discI list.map_disc_iff list_all_simps(1) state.inject)
  next
    case RedAssertFail thus ?thesis using failure_stays_cmd_list RedCmdListCons(2) RedCmdListCons(5) by blast
  qed auto
qed

text \<open>If one invariant doesn't hold, then the block containing the assert cmds corresponding to the invariants fails\<close>
lemma one_inv_fails_assertions: 
  assumes InvsEq: "invs = invs1 @ [I] @ invs2"
      and AllSat: "expr_all_sat A \<Lambda> \<Gamma> \<Omega> ns1 invs1"
      and InvFail: "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>I,ns1\<rangle> \<Down> BoolV False"
      and AssertionsEq: "assertions = map Assert invs"
    shows "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>assertions, Normal ns1\<rangle> [\<rightarrow>] Failure"
  using assms
proof -
  from InvsEq AssertionsEq obtain assum1 a_fail assum2 where
    left: "assum1 = map Assert invs1" and
    mid_fail: "a_fail = Assert I" and
    right: "assum2 = map Assert invs2" and
    concat: "assertions = assum1 @ [a_fail] @ assum2"
    by simp
  from AllSat left have left_red: "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>assum1, Normal ns1\<rangle> [\<rightarrow>] Normal ns1" using asserts_hold_if_invs_hold by simp
  from mid_fail have "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>a_fail, Normal ns1\<rangle> \<rightarrow> Failure" using red_cmd.intros(2) assms(3) by simp
  from this left_red have "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>assum1 @ [a_fail] @ assum2, Normal ns1\<rangle> [\<rightarrow>] Failure" using failure_stays_cmd_list 
    by (simp add: RedCmdListCons failure_red_cmd_list red_cmd_list_append)
  thus ?thesis using concat by auto
qed

lemma valid_config_implies_not_failure:
  assumes "Semantics.valid_configuration A \<Lambda> \<Gamma> \<Omega> posts m' s'"
  shows "s' \<noteq> Failure"
  using Semantics.valid_configuration_def assms by blast

lemma valid_config_implies_satisfied_posts:
  assumes "Semantics.valid_configuration A \<Lambda> \<Gamma> \<Omega> posts m' s'"
  shows "is_final_config (m', s') \<Longrightarrow> (\<forall>ns_end. s' = Normal ns_end \<longrightarrow> (expr_all_sat A \<Lambda> \<Gamma> \<Omega> ns_end) posts)"
  using Semantics.valid_configuration_def assms by (metis)

text \<open>If an \<^term>\<open>ast_config\<close> (bigblock, cont, state) is an ending configuration, then any corresponding cfg block is locally correct.\<close>
lemma end_static:
  assumes "A,M,\<Lambda>1_local,\<Gamma>,\<Omega>,T \<turnstile> \<langle>(BigBlock any [] None None, KStop, Normal ns1)\<rangle> \<longrightarrow> (step_bb, step_cont, step_state)"
  shows "step_state \<noteq> Failure \<and> (\<forall>ns1'. step_state = Normal ns1' \<longrightarrow> A,M,\<Lambda>0,\<Gamma>,[] \<turnstile> \<langle>any_block ,Normal ns1\<rangle> [\<rightarrow>] Normal ns1')"
  using assms
  by (cases) auto 

lemma end_return:
  assumes "A,M,\<Lambda>1_local,\<Gamma>,\<Omega>,T \<turnstile> \<langle>(BigBlock any [] None (Some Return), KStop, Normal ns1)\<rangle> \<longrightarrow> (step_bb, step_cont, step_state)"
  shows "step_state \<noteq> Failure \<and> (\<forall>ns1'. step_state = Normal ns1' \<longrightarrow> A,M,\<Lambda>0,\<Gamma>,[] \<turnstile> \<langle>[] ,Normal ns1\<rangle> [\<rightarrow>] Normal ns1')"
  using assms
  by (cases) (auto simp add: RedCmdListNil)

text \<open>If an ast configuration is final, then any transition in the ast will stay in the same configuration.\<close>
lemma final_is_static: 
  assumes "is_final ((BigBlock name [] None None), start_cont, start_state)"
  shows "\<And>A M \<Lambda> \<Gamma> \<Omega> T end_bb end_cont end_state. 
         (red_bigblock A M \<Lambda> \<Gamma> \<Omega> T ((BigBlock name [] None None), start_cont, start_state) (end_bb, end_cont, end_state)) \<Longrightarrow> 
         ((end_bb, end_cont, end_state) = ((BigBlock name [] None None), start_cont, start_state))" 
  using assms 
proof -
  fix A M \<Lambda> \<Gamma> \<Omega> T end_bb  end_cont end_state
  have cont_eq: "start_cont = KStop" using assms is_final.elims(1) by blast  
  assume prem1: "(red_bigblock A M \<Lambda> \<Gamma> \<Omega> T ((BigBlock name [] None None), start_cont, start_state) (end_bb, end_cont, end_state))"
  from prem1 show "((end_bb, end_cont, end_state) = ((BigBlock name [] None None), start_cont, start_state))" using cont_eq
  proof cases 
    case RedFailure_or_Magic thus ?thesis using cont_eq by blast
  qed auto
qed

lemma final_is_static_propagate:
  assumes "rtranclp (red_bigblock A M \<Lambda> \<Gamma> \<Omega> T) start_config end_config" 
      and "is_final start_config"
      and "start_config = ((BigBlock name [] None None), start_cont, start_state)"
    shows "end_config = ((BigBlock name [] None None), start_cont, start_state)"
  using assms
proof (induction rule: rtranclp.induct)
  case (rtrancl_refl a)
  then show ?case using assms by simp
next
  case (rtrancl_into_rtrancl a b c)
  then have inter_is_same: "b = (BigBlock name [] None None, start_cont, start_state)" and inter_is_final: "is_final b" by auto
  have "start_cont = KStop" using rtrancl_into_rtrancl(4) is_final.elims(1) rtrancl_into_rtrancl.prems(2) by blast
  from rtrancl_into_rtrancl(2) show ?case
    using inter_is_same inter_is_final \<open>start_cont = KStop\<close>
  proof cases
    case RedFailure_or_Magic 
    thus ?thesis
      using inter_is_same inter_is_final \<open>start_cont = KStop\<close> 
      by (auto simp add: RedFailure_or_Magic)
  qed auto
qed

lemma magic_propagates: 
  assumes "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (bb, cont, Magic) -n\<longrightarrow>^j (reached_bb, reached_cont, reached_state)"
  shows "reached_state = Magic"
  using assms
proof (cases j)
  case 0 
  hence "(reached_bb, reached_cont, reached_state) = (bb, cont, Magic)" using assms by fastforce
  thus ?thesis by simp
next
  case (Suc j')
  from this obtain first_inter where 
    red1: "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> \<langle>(bb, cont, Magic)\<rangle> \<longrightarrow> first_inter" and 
    red_rest: "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> first_inter -n\<longrightarrow>^j' (reached_bb, reached_cont, reached_state)"
    by (metis assms relpowp_Suc_E2)
  hence reached_conj: "((get_state first_inter) = Magic) \<and> ((is_final first_inter) = True)" 
  proof cases
    case RedFailure_or_Magic 
    thus ?thesis by simp
  qed
  hence magic_reached: "(get_state first_inter) = Magic" by simp
  have final_config: "is_final first_inter" using reached_conj by simp
  hence "\<exists> name. first_inter = ((BigBlock name [] None None), KStop, Magic)" using magic_reached
    by (metis get_state.simps is_final.elims(2))
  from this obtain name1 where concrete: "first_inter = ((BigBlock name1 [] None None), KStop, Magic)" 
    by blast 
  from red_rest show ?thesis using final_config magic_reached concrete final_is_static_propagate 
    by (metis prod.inject relpowp_imp_rtranclp)
qed 

text \<open>The following are simple helper lemmas used in the proofs that involve applying induction hypotheses to prove global correctness of loop-heads.\<close>

lemma smaller_helper: "k < j \<Longrightarrow> k < (Suc j)"
  by simp

lemma less_trans_inv: "(y :: nat) < z \<Longrightarrow> x < y \<Longrightarrow> x < z"
  using less_trans by simp

lemma eq_to_succ: "x = y \<Longrightarrow> x < (Suc y)" by simp 

lemma strictly_smaller_helper2: "j'' < j' \<Longrightarrow> j = Suc j' \<Longrightarrow> j'' < j"
  by simp

lemma strictly_smaller_helper3: "j'' < j' \<Longrightarrow> j''' < j'' \<Longrightarrow> j = Suc j' \<Longrightarrow> j''' < j"
  by simp

lemma strictly_smaller_helper4: "j' = Suc (Suc j'') \<Longrightarrow> k < j'' \<Longrightarrow> j = Suc j' \<Longrightarrow> k < j"
  by simp

lemma smaller_helper5: "j = Suc j1 \<Longrightarrow> j1 = Suc (Suc j2) \<Longrightarrow> j2 < j"
  by simp

text \<open>The following are helper lemmas related to taking steps through assume cmds in a given ast- or cfg-trace.\<close>

lemma push_through_assumption_test1: 
  assumes ExtendedCorrect: "(\<And> s2'.(red_cmd_list A M \<Lambda> \<Gamma> \<Omega> (c#cs2) (Normal ns1) s2') \<Longrightarrow> s2' \<noteq> Failure)"
      and  assume_cmd: "c = Assume guard"
      and guard_holds: "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>guard, ns1\<rangle> \<Down> LitV (LBool True)"
    shows "(\<And> s2'.(red_cmd_list A M \<Lambda> \<Gamma> \<Omega> cs2 (Normal ns1) s2') \<Longrightarrow> s2' \<noteq> Failure)"  
  using RedAssumeOk RedCmdListCons ExtendedCorrect assume_cmd guard_holds 
  by blast

lemma push_through_assumption0: 
  assumes assume_cmd: "c = Assume guard"
      and guard_holds: "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>guard, ns1\<rangle> \<Down> LitV (LBool True)"
    shows "\<And> s. (red_cmd_list A M \<Lambda> \<Gamma> \<Omega> (cs2) (Normal ns1) s) \<Longrightarrow> (red_cmd_list A M \<Lambda> \<Gamma> \<Omega> (c#cs2) (Normal ns1) s)" 
  using RedAssumeOk RedCmdListCons assume_cmd guard_holds 
  by blast

lemma push_through_assumption1: 
  assumes assume_cmd: "c = Assume not_guard"
      and NotGuardEquiv: "UnOp Not guard \<sim> not_guard"
      and guard_fails: "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>guard, ns1\<rangle> \<Down> LitV (LBool False)"
    shows "\<And> s. (red_cmd_list A M \<Lambda> \<Gamma> \<Omega> (cs2) (Normal ns1) s) \<Longrightarrow> (red_cmd_list A M \<Lambda> \<Gamma> \<Omega> (c#cs2) (Normal ns1) s)"
  by (metis NotGuardEquiv assume_cmd equiv_preserves_value false_equals_not_true guard_fails push_through_assumption0)

lemma guard_holds_push_through_assumption: 
  assumes block_correctness:  
    "reached_state \<noteq> Failure \<and> 
        (\<forall> ns1'. reached_state = Normal ns1' \<longrightarrow> (red_cmd_list A M \<Lambda> \<Gamma> \<Omega> (cs2) (Normal ns1) (Normal ns1')))"
      and assume_cmd: "c = Assume guard"
      and guard_holds: "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>guard, ns1\<rangle> \<Down> LitV (LBool True)"
    shows "reached_state \<noteq> Failure \<and> 
           (\<forall> ns1'. reached_state = Normal ns1' \<longrightarrow> (red_cmd_list A M \<Lambda> \<Gamma> \<Omega> (c#cs2) (Normal ns1) (Normal ns1')))" 
    by (simp add: assume_cmd block_correctness guard_holds push_through_assumption0)

lemma guard_holds_push_through_assumption2: 
  assumes block_correctness: 
    "reached_state \<noteq> Failure \<and> 
    (\<forall> ns1'. reached_state = Normal ns1' \<longrightarrow> (red_cmd_list A M \<Lambda> \<Gamma> \<Omega> (c#cs2) (Normal ns1) (Normal ns1')))"
      and assume_cmd: "c = Assume guard"
      and guard_holds: "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>guard, ns1\<rangle> \<Down> LitV (LBool True)"
    shows "reached_state \<noteq> Failure \<and> 
       (\<forall> ns1'. reached_state = Normal ns1' \<longrightarrow> (red_cmd_list A M \<Lambda> \<Gamma> \<Omega> (cs2) (Normal ns1) (Normal ns1')))" 
    using assume_cmd assume_true_cmds block_correctness by blast

lemma guard_fails_push_through_assumption: 
  assumes block_correctness: 
    "reached_state \<noteq> Failure \<and> 
     (\<forall> ns1'. reached_state = Normal ns1' \<longrightarrow> (red_cmd_list A M \<Lambda> \<Gamma> \<Omega> (cs2) (Normal ns1) (Normal ns1')))"
      and assume_cmd: "c = Assume not_guard"
      and NotGuardEquiv: "UnOp Not guard \<sim> not_guard"
      and guard_fails: "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>guard, ns1\<rangle> \<Down> LitV (LBool False)"
    shows "reached_state \<noteq> Failure \<and> (\<forall> ns1'. reached_state = Normal ns1' \<longrightarrow> (red_cmd_list A M \<Lambda> \<Gamma> \<Omega> (c#cs2) (Normal ns1) (Normal ns1')))" 
    using NotGuardEquiv assume_cmd block_correctness guard_fails push_through_assumption1 by blast

lemma guard_fails_push_through_assumption2: 
  assumes block_correctness: "reached_state \<noteq> Failure \<and> (\<forall> ns1'. reached_state = Normal ns1' \<longrightarrow> (red_cmd_list A M \<Lambda> \<Gamma> \<Omega> (c#cs2) (Normal ns1) (Normal ns1')))"
      and assume_cmd: "c = Assume not_guard"
      and "UnOp Not guard \<sim> not_guard" \<comment>\<open>not required for lemma, but makes lemma in sync with analogous lemma above\<close>
      and guard_fails: "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>guard, ns1\<rangle> \<Down> LitV (LBool False)"
     shows "reached_state \<noteq> Failure \<and> (\<forall> ns1'. reached_state = Normal ns1' \<longrightarrow> (red_cmd_list A M \<Lambda> \<Gamma> \<Omega> (cs2) (Normal ns1) (Normal ns1')))" 
     using assume_cmd assume_true_cmds block_correctness by blast

lemma correctness_propagates_through_assumption:
  assumes "\<forall>m s. (A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl n0, Normal ns1) -n\<rightarrow>* (m, s)) \<longrightarrow> s \<noteq> Failure"
      and "node_to_block G ! n0 = [Assume c]"
      and "UnOp Not guard \<sim> c"
      and "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>guard, ns1\<rangle> \<Down> BoolV False"
      and "List.member (out_edges G ! n0) n1"
    shows "\<And> m s. (A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl n1, Normal ns1) -n\<rightarrow>* (m, s)) \<Longrightarrow> s \<noteq> Failure"
proof -
  fix m1 s1
  have "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>c, ns1\<rangle> \<Down> BoolV True" using assms(3-4) equiv_preserves_value false_equals_not_true by blast
  then have a1: "(A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>[Assume c], Normal ns1\<rangle> [\<rightarrow>] (Normal ns1))" by (meson RedAssumeOk RedCmdListCons RedCmdListNil)
  show "(A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl n1, Normal ns1) -n\<rightarrow>* (m1, s1)) \<Longrightarrow> s1 \<noteq> Failure" 
  proof -
    assume "(A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl n1, Normal ns1) -n\<rightarrow>* (m1, s1))"
    thus "s1 \<noteq> Failure" using a1 assms(1-2) assms(5) dag_verifies_propagate by blast 
  qed
qed

lemma correctness_propagates_through_assumption2:
  assumes "\<forall>m s. (A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl n0, Normal ns1) -n\<rightarrow>* (m, s)) \<longrightarrow> s \<noteq> Failure"
      and "node_to_block G ! n0 = [Assume guard]"
      and "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>guard, ns1\<rangle> \<Down> BoolV True"
      and "List.member (out_edges G ! n0) n1"
    shows "\<And> m s. (A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl n1, Normal ns1) -n\<rightarrow>* (m, s)) \<Longrightarrow> s \<noteq> Failure"
proof -
  fix m1 s1
  have a1: "(A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>[Assume guard], Normal ns1\<rangle> [\<rightarrow>] (Normal ns1))" 
    by (meson RedAssumeOk assms(3) red_cmd_list.simps)
  show "(A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl n1, Normal ns1) -n\<rightarrow>* (m1, s1)) \<Longrightarrow> s1 \<noteq> Failure" 
  proof -
    assume "(A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl n1, Normal ns1) -n\<rightarrow>* (m1, s1))"
    thus "s1 \<noteq> Failure" using a1 assms(1-2) assms(4) dag_verifies_propagate by blast 
  qed
qed

lemma correctness_propagates_through_assumption3:
  assumes "\<forall>m s. (A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl n0, Normal ns1) -n\<rightarrow>* (m, s)) \<longrightarrow> 
                   (is_final_config (m, s) \<longrightarrow> 
                      (\<forall>ns_end. s = Normal ns_end \<longrightarrow> (expr_all_sat A \<Lambda>1_local \<Gamma> \<Omega> ns_end) posts))"
      and "node_to_block G ! n0 = [Assume c]"
      and "UnOp Not guard \<sim> c"
      and "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>guard, ns1\<rangle> \<Down> BoolV False"
      and "List.member (out_edges G ! n0) n1"
    shows "\<And> m s. (A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl n1, Normal ns1) -n\<rightarrow>* (m, s)) \<Longrightarrow> 
                   (is_final_config (m, s) \<Longrightarrow> 
                   (\<forall>ns_end. s = Normal ns_end \<longrightarrow> (expr_all_sat A \<Lambda>1_local \<Gamma> \<Omega> ns_end) posts))"
proof -
  fix m1 s1
  have "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>c, ns1\<rangle> \<Down> BoolV True" using assms(3-4) equiv_preserves_value false_equals_not_true by blast
  then have a1: "(A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>[Assume c], Normal ns1\<rangle> [\<rightarrow>] (Normal ns1))" by (meson RedAssumeOk RedCmdListCons RedCmdListNil)
  show "(A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl n1, Normal ns1) -n\<rightarrow>* (m1, s1)) \<Longrightarrow> 
          (is_final_config (m1, s1) \<Longrightarrow> 
          (\<forall>ns_end. s1 = Normal ns_end \<longrightarrow> (expr_all_sat A \<Lambda>1_local \<Gamma> \<Omega> ns_end) posts))" 
  proof -
    assume "(A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl n1, Normal ns1) -n\<rightarrow>* (m1, s1))"
    thus "(is_final_config (m1, s1) \<Longrightarrow> (\<forall>ns_end. s1 = Normal ns_end \<longrightarrow> (expr_all_sat A \<Lambda>1_local \<Gamma> \<Omega> ns_end) posts))" 
      using a1 assms by (metis RedNormalSucc converse_rtranclp_into_rtranclp)
  qed
qed

lemma correctness_propagates_through_assumption4:
  assumes "\<forall>m s. (A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl n0, Normal ns1) -n\<rightarrow>* (m, s)) \<longrightarrow> 
                 (is_final_config (m, s) \<longrightarrow> (\<forall>ns_end. s = Normal ns_end \<longrightarrow> 
                 (expr_all_sat A \<Lambda>1_local \<Gamma> \<Omega> ns_end) posts))"
      and "node_to_block G ! n0 = [Assume guard]"
      and "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>guard, ns1\<rangle> \<Down> BoolV True"
      and "List.member (out_edges G ! n0) n1"
    shows "\<And> m s. (A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl n1, Normal ns1) -n\<rightarrow>* (m, s)) \<Longrightarrow> (is_final_config (m, s) \<Longrightarrow> 
                   (\<forall>ns_end. s = Normal ns_end \<longrightarrow> (expr_all_sat A \<Lambda>1_local \<Gamma> \<Omega> ns_end) posts))"
proof -
  fix m1 s1
  have a1: "(A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>[Assume guard], Normal ns1\<rangle> [\<rightarrow>] (Normal ns1))" 
    by (meson RedAssumeOk assms(3) red_cmd_list.simps)
  show "(A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl n1, Normal ns1) -n\<rightarrow>* (m1, s1)) \<Longrightarrow> 
          (is_final_config (m1, s1) \<Longrightarrow> 
            (\<forall>ns_end. s1 = Normal ns_end \<longrightarrow> (expr_all_sat A \<Lambda>1_local \<Gamma> \<Omega> ns_end) posts))" 
  proof -
    assume "(A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl n1, Normal ns1) -n\<rightarrow>* (m1, s1))"
    thus "(is_final_config (m1, s1) \<Longrightarrow> (\<forall>ns_end. s1 = Normal ns_end \<longrightarrow> (expr_all_sat A \<Lambda>1_local \<Gamma> \<Omega> ns_end) posts))" 
      using a1 assms by (metis RedNormalSucc converse_rtranclp_into_rtranclp)
  qed
qed

lemma correctness_propagates_through_empty:
  assumes "\<forall>m s. (A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl n0, Normal ns1) -n\<rightarrow>* (m, s)) \<longrightarrow> s \<noteq> Failure"
      and "node_to_block G ! n0 = []"
      and "List.member (out_edges G ! n0) n1"
    shows "\<And> m s. (A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl n1, Normal ns1) -n\<rightarrow>* (m, s)) \<Longrightarrow> s \<noteq> Failure"
proof -
  fix m1 s1
  have a1: "(A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>[], Normal ns1\<rangle> [\<rightarrow>] (Normal ns1))" by (rule RedCmdListNil)
  show "(A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl n1, Normal ns1) -n\<rightarrow>* (m1, s1)) \<Longrightarrow> s1 \<noteq> Failure" 
  proof -
    assume "(A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl n1, Normal ns1) -n\<rightarrow>* (m1, s1))"
    thus "s1 \<noteq> Failure" by (metis a1 assms(1-3) dag_verifies_propagate)
  qed
qed

lemma correctness_propagates_through_empty2:
  assumes "\<forall>m s. (A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl n0, Normal ns1) -n\<rightarrow>* (m, s)) \<longrightarrow> 
                 (is_final_config (m, s) \<longrightarrow> 
                 (\<forall>ns_end. s = Normal ns_end \<longrightarrow> (expr_all_sat A \<Lambda>1_local \<Gamma> \<Omega> ns_end) posts))"
      and "node_to_block G ! n0 = []"
      and "List.member (out_edges G ! n0) n1"
    shows "\<And> m s. (A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl n1, Normal ns1) -n\<rightarrow>* (m, s)) \<Longrightarrow> 
                  (is_final_config (m, s) \<Longrightarrow> 
                  (\<forall>ns_end. s = Normal ns_end \<longrightarrow> (expr_all_sat A \<Lambda>1_local \<Gamma> \<Omega> ns_end) posts))"
proof -
  fix m1 s1
  have a1: "(A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>[], Normal ns1\<rangle> [\<rightarrow>] (Normal ns1))" by (meson RedAssumeOk assms(3) red_cmd_list.simps)
  show "(A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl n1, Normal ns1) -n\<rightarrow>* (m1, s1)) \<Longrightarrow> 
        (is_final_config (m1, s1) \<Longrightarrow> 
         (\<forall>ns_end. s1 = Normal ns_end \<longrightarrow> (expr_all_sat A \<Lambda>1_local \<Gamma> \<Omega> ns_end) posts))" 
  proof -
    assume "(A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl n1, Normal ns1) -n\<rightarrow>* (m1, s1))"
    thus "(is_final_config (m1, s1) \<Longrightarrow> (\<forall>ns_end. s1 = Normal ns_end \<longrightarrow> (expr_all_sat A \<Lambda>1_local \<Gamma> \<Omega> ns_end) posts))" 
      using a1 assms by (metis RedNormalSucc converse_rtranclp_into_rtranclp)
  qed
qed

subsection \<open>Pairs of helper lemma + global lemma for certain special cases.\<close>

text \<open>The following are pairs of lemmas. Each pair consists of a helper lemma and a global block lemma. 
      The helper lemma ensures that if a valid AST configuration is a starting point of a trace and 
      the configuration is such that only certain rules, which don't change the state of the configuration, 
      can be applied for the trace to continue, then either the trace will finish in a valid configuration 
      after applying them or a different valid configuration will be reached from which the trace will continue.
      The global block lemma proves the correctness of that AST trace, given the correctness of all cfg traces 
      starting in a cfg block related to the big block in the starting AST configuration.
      Note that a syntactic relation between the big block and the cfg block does not need to be shown here, as these global block lemmas are only ever applied in conjuction with
      other more generic global block lemmas, which will have already shown the syntactic relation.\<close>

text \<open>Pair 1: The starting configuration represents a point in the program after a loop, and 
              therefore the continuation needs to be adjusted.\<close>

lemma endblock_skip:
  assumes "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile>(bb0, KEndBlock cont0, Normal ns3) -n\<longrightarrow>^l (reached_bb, reached_cont, reached_state)"
      and "bb0 = BigBlock name [] None None" 
    shows "(valid_configuration A \<Lambda> \<Gamma> \<Omega> posts reached_bb reached_cont reached_state) \<or> 
            (\<exists> l1. (A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile>(bb0, cont0, Normal ns3) -n\<longrightarrow>^l1 (reached_bb, reached_cont, reached_state)) \<and> (l = Suc l1) )"
proof (cases l)
  case 0
  then show ?thesis by (metis Ast.valid_configuration_def assms(1) get_state.simps is_final.simps(6) relpowp_fun_conv state.simps(3))
next
  case 1: (Suc l1)
  then show ?thesis 
  proof -
    from 1 assms obtain inter_bb inter_cont inter_state  where
      step1: "(red_bigblock A M \<Lambda> \<Gamma> \<Omega> T (BigBlock name [] None None, KEndBlock cont0, Normal ns3) (inter_bb, inter_cont, inter_state))" and 
      rest: "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile>(inter_bb, inter_cont, inter_state) -n\<longrightarrow>^l1 (reached_bb, reached_cont, reached_state)" 
      by (metis (no_types) prod_cases3 relpowp_Suc_D2)
    from this step1 have "(inter_bb, inter_cont, inter_state) = (BigBlock name [] None None, cont0, Normal ns3)"
      by (cases) auto
    then show ?thesis using "1" assms(2) rest by blast
  qed
qed

lemma ending_after_skipping_endblock:
  assumes "j = Suc j'" 
      and "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile>(bb, KEndBlock cont0, Normal ns1'') -n\<longrightarrow>^j' (reached_bb, reached_cont, reached_state)" 
      and "bb = BigBlock None [] None None"
      and "\<And>m3 s3. (A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl n, Normal ns1'') -n\<rightarrow>* (m3, s3)) \<Longrightarrow> s3 \<noteq> Failure"
      and "\<And>m' s'. (A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl n, Normal ns1'') -n\<rightarrow>* (m', s')) \<Longrightarrow>
           is_final_config (m', s') \<Longrightarrow> \<forall>ns_end. s' = Normal ns_end \<longrightarrow> (expr_all_sat A \<Lambda>1_local \<Gamma> \<Omega> ns_end) posts"
      and "(cont_guard = Some guard) \<Longrightarrow> (A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>guard,ns1''\<rangle> \<Down> BoolV False)" 
      and "\<And> j''. 
            j' = Suc j'' \<Longrightarrow>                           
            A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile>(bb, cont0, Normal ns1'') -n\<longrightarrow>^j'' (reached_bb, reached_cont, reached_state) \<Longrightarrow>
           (\<And>m' s'. A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl n, Normal ns1'') -n\<rightarrow>* (m', s') \<Longrightarrow> s' \<noteq> Failure) \<Longrightarrow>
           (\<And>m' s'. (A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl n, Normal ns1'') -n\<rightarrow>* (m', s')) \<Longrightarrow>
           is_final_config (m', s') \<Longrightarrow> \<forall>ns_end. s' = Normal ns_end \<longrightarrow> (expr_all_sat A \<Lambda>1_local \<Gamma> \<Omega> ns_end) posts) \<Longrightarrow>
           ((cont_guard = Some guard) \<Longrightarrow> (A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>guard,ns1''\<rangle> \<Down> BoolV False)) \<Longrightarrow> (valid_configuration A \<Lambda> \<Gamma> \<Omega> posts reached_bb reached_cont reached_state)"
    shows "valid_configuration A \<Lambda> \<Gamma> \<Omega> posts reached_bb reached_cont reached_state"
proof -
  from assms(2-3) have disj_a:
    "(valid_configuration A \<Lambda> \<Gamma> \<Omega> posts reached_bb reached_cont reached_state) \<or> 
       (\<exists> l2. (A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile>(bb, cont0, Normal ns1'') -n\<longrightarrow>^l2 (reached_bb, reached_cont, reached_state)) \<and> (j' = Suc l2) )" 
    by (simp add: endblock_skip)
  thus ?thesis
  proof cases
    assume "(valid_configuration A \<Lambda> \<Gamma> \<Omega> posts reached_bb reached_cont reached_state)" thus ?thesis by simp
  next 
    assume "\<not> ((valid_configuration A \<Lambda> \<Gamma> \<Omega> posts reached_bb reached_cont reached_state))"
    hence "(\<exists> l2. (A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile>(bb, cont0, Normal ns1'') -n\<longrightarrow>^l2 (reached_bb, reached_cont, reached_state)) \<and> (j' = Suc l2) )" 
      using disj_a by blast
    thus ?thesis
    proof -
      obtain l2_conc where conc_trace: "(A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile>(bb, cont0, Normal ns1'') -n\<longrightarrow>^l2_conc (reached_bb, reached_cont, reached_state))" and 
        succ_rel: "(j' = Suc l2_conc)"
        using \<open>\<exists>l2. (A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile>(bb, cont0, Normal ns1'') -n\<longrightarrow>^l2 (reached_bb, reached_cont, reached_state)) \<and> j' = Suc l2\<close> by blast
      show ?thesis
        apply (rule assms(7))
        apply (rule succ_rel)
        apply (rule conc_trace)
        apply (rule assms(4))
        apply (simp)
        apply (rule assms(5))
        apply assumption+
        using assms(6) false_equals_not_true 
        by blast
    qed
  qed
qed

text \<open>Pair 2: The starting configuration represents a point in the program after a loop and the 
              continuation needs to be adjusted and subsequently entered.
              (This could be replaced by a simpler lemma.)\<close>
lemma endblock_skip2:
  assumes "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile>(bb0, KEndBlock (KSeq bb_next cont0), Normal ns3) -n\<longrightarrow>^l (reached_bb, reached_cont, reached_state)"
    and "bb0 = BigBlock None [] None None" 
  shows "(valid_configuration A \<Lambda> \<Gamma> \<Omega> posts reached_bb reached_cont reached_state) \<or> 
            (\<exists> l2. (A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile>(bb_next, cont0, Normal ns3) -n\<longrightarrow>^l2 (reached_bb, reached_cont, reached_state)) \<and> (l = Suc (Suc l2)) )"
  using assms
proof (cases l)
  case 0
  then show ?thesis by (metis Ast.valid_configuration_def assms(1) get_state.simps is_final.simps(6) relpowp_fun_conv state.simps(3))
next
  case 1: (Suc l1)
  then show ?thesis 
  proof (cases l1)
    case 0
    from 1 assms this have "(red_bigblock A M \<Lambda> \<Gamma> \<Omega> T (BigBlock None [] None None, KEndBlock (KSeq bb_next cont0), Normal ns3) (reached_bb, reached_cont, reached_state))"
      by fastforce
    then show ?thesis
    proof cases
      case RedSkipEndBlock thus ?thesis by (simp add: Ast.valid_configuration_def)
    qed auto
  next
    case 2: (Suc l2)
    from 2 1 have "l = Suc (Suc l2)" by auto
    from 2 1 assms obtain inter_bb inter_cont inter_state inter_bb2 inter_cont2 inter_state2 where
      step1: "(red_bigblock A M \<Lambda> \<Gamma> \<Omega> T (BigBlock None [] None None, KEndBlock (KSeq bb_next cont0), Normal ns3) (inter_bb, inter_cont, inter_state))" and 
      step2: "(red_bigblock A M \<Lambda> \<Gamma> \<Omega> T (inter_bb, inter_cont, inter_state) (inter_bb2, inter_cont2, inter_state2))" and
      rest: "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile>(inter_bb2, inter_cont2, inter_state2) -n\<longrightarrow>^l2 (reached_bb, reached_cont, reached_state)" 
      by (metis (no_types) prod_cases3 relpowp_Suc_D2)
    from this step1 have "(inter_bb, inter_cont, inter_state) = (BigBlock None [] None None, (KSeq bb_next cont0), Normal ns3)"
    proof cases
      case RedSkipEndBlock thus ?thesis 
        by blast
    qed auto
    from step2 this have "(inter_bb2, inter_cont2, inter_state2) = (bb_next, cont0, Normal ns3)" 
    proof cases 
      case RedSkip 
      thus ?thesis  
        using \<open>(inter_bb, inter_cont, inter_state) = (BigBlock None [] None None, KSeq bb_next cont0, Normal ns3)\<close> 
        by fastforce
    qed auto
    hence "(A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile>(bb_next, cont0, Normal ns3) -n\<longrightarrow>^l2 (reached_bb, reached_cont, reached_state)) \<and> (l = Suc (Suc l2))" 
      using rest \<open>l = Suc (Suc l2)\<close> 
      by simp
    then show ?thesis by blast
  qed
qed

lemma ending_after_skipping_endblock2:
  assumes "j = Suc j'" 
      and "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile>(bb, KEndBlock (KSeq bigblock_next cont0), Normal ns1'') -n\<longrightarrow>^j' (reached_bb, reached_cont, reached_state)" 
      and "bb = BigBlock None [] None None"
      and "\<And>m3 s3. (A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl n, Normal ns1'') -n\<rightarrow>* (m3, s3)) \<Longrightarrow> s3 \<noteq> Failure"
      and "\<And>m' s'. (A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl n, Normal ns1'') -n\<rightarrow>* (m', s')) \<Longrightarrow>
           is_final_config (m', s') \<Longrightarrow> \<forall>ns_end. s' = Normal ns_end \<longrightarrow> (expr_all_sat A \<Lambda>1_local \<Gamma> \<Omega> ns_end) posts"
      and "(cont_guard = Some guard) \<Longrightarrow> (A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>guard,ns1''\<rangle> \<Down> BoolV False)"
      and "\<And> j''. 
            j' = Suc (Suc j'') \<Longrightarrow>
            A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile>(bigblock_next, cont0, Normal ns1'') -n\<longrightarrow>^j'' (reached_bb, reached_cont, reached_state) \<Longrightarrow>
           (\<And>m' s'. A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl n, Normal ns1'') -n\<rightarrow>* (m', s') \<Longrightarrow> s' \<noteq> Failure) \<Longrightarrow>
           (\<And>m' s'. (A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl n, Normal ns1'') -n\<rightarrow>* (m', s')) \<Longrightarrow>
           is_final_config (m', s') \<Longrightarrow> \<forall>ns_end. s' = Normal ns_end \<longrightarrow> (expr_all_sat A \<Lambda>1_local \<Gamma> \<Omega> ns_end) posts) \<Longrightarrow>
           ((cont_guard = Some guard) \<Longrightarrow> (A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>guard,ns1''\<rangle> \<Down> BoolV False)) \<Longrightarrow> 
           valid_configuration A \<Lambda> \<Gamma> \<Omega> posts reached_bb reached_cont reached_state"
    shows "valid_configuration A \<Lambda> \<Gamma> \<Omega> posts reached_bb reached_cont reached_state"
proof -
  from assms(2-3) have disj_a:
    "(valid_configuration A \<Lambda> \<Gamma> \<Omega> posts reached_bb reached_cont reached_state) \<or> 
       (\<exists> l2. (A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile>(bigblock_next, cont0, Normal ns1'') -n\<longrightarrow>^l2 (reached_bb, reached_cont, reached_state)) \<and> 
              (j' = Suc (Suc l2)) )" 
    by (simp add: endblock_skip2)
  thus ?thesis
  proof cases
    assume "(valid_configuration A \<Lambda> \<Gamma> \<Omega> posts reached_bb reached_cont reached_state)" thus ?thesis by simp
  next 
    assume "\<not> ((valid_configuration A \<Lambda> \<Gamma> \<Omega> posts reached_bb reached_cont reached_state))"
    hence "(\<exists> l2. (A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile>(bigblock_next, cont0, Normal ns1'') -n\<longrightarrow>^l2 (reached_bb, reached_cont, reached_state)) \<and> 
                  (j' = Suc (Suc l2)) )" 
      using disj_a by blast
    thus ?thesis
    proof -
      obtain l2_conc where conc_trace: "(A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile>(bigblock_next, cont0, Normal ns1'') -n\<longrightarrow>^l2_conc (reached_bb, reached_cont, reached_state))" and 
        succ_rel: "(j' = Suc (Suc l2_conc))"
        using \<open>\<exists>l2. (A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile>(bigblock_next, cont0, Normal ns1'') -n\<longrightarrow>^l2 (reached_bb, reached_cont, reached_state)) \<and> j' = Suc (Suc l2)\<close>
        by blast
      show ?thesis
        apply (rule assms(7))
        apply (rule succ_rel)
        apply (rule conc_trace)
        apply (rule assms(4))
        apply (simp)
        apply (rule assms(5))
        apply simp+
        using assms(6) false_equals_not_true 
        by blast
    qed
  qed
qed

text \<open>Pair 3: The starting configuration represents a point in the program before a loop and, more 
              specifically, before the loop has been 'unwrapped'.
              The 'wrapper' construct exists to accomodate the handling of breaks, which this theory 
              doesn't currently cover.\<close>

lemma wrapper_to_endblock:
  assumes "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile>(bb0, cont0, Normal ns) -n\<longrightarrow>^l (reached_bb, reached_cont, reached_state)"
      and "bb0 = BigBlock name [] (Some (WhileWrapper loop)) None"
    shows "(valid_configuration A \<Lambda> \<Gamma> \<Omega> posts reached_bb reached_cont reached_state) \<or> 
              (\<exists> l1. (A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile>((BigBlock name [] (Some loop) None), KEndBlock cont0, Normal ns) -n\<longrightarrow>^l1 
                     (reached_bb, reached_cont, reached_state)) \<and> (l = Suc l1))"
  using assms
proof (cases l)
  case 0
  hence "(reached_bb, reached_cont, reached_state) = (bb0, cont0, Normal ns)" using assms(1) by simp
  then show ?thesis by (simp add: Ast.valid_configuration_def assms(2))
next
  case 1: (Suc l1)
  then show ?thesis 
  proof -
    from 1 assms obtain inter_bb inter_cont inter_state where
      step1: "(red_bigblock A M \<Lambda> \<Gamma> \<Omega> T (bb0, cont0, Normal ns) (inter_bb, inter_cont, inter_state))" and 
      rest: "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile>(inter_bb, inter_cont, inter_state) -n\<longrightarrow>^l1 (reached_bb, reached_cont, reached_state)" 
      by (metis (no_types) prod_cases3 relpowp_Suc_D2)
    from this have "(inter_bb, inter_cont, inter_state) = (BigBlock name [] (Some loop) None, KEndBlock cont0, Normal ns)"
    proof cases
      case RedParsedWhileWrapper thus ?thesis using assms(2) by auto
    qed (auto simp add: assms(2))
    hence "(A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile>(BigBlock name [] (Some loop) None, KEndBlock cont0, Normal ns) -n\<longrightarrow>^l1 (reached_bb, reached_cont, reached_state)) \<and> (l = Suc l1)" 
      using rest \<open>l = Suc l1\<close> assms(2) by simp
    then show ?thesis by blast
  qed
qed

lemma ending_after_unwrapping:
  assumes "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile>(bb, cont0, Normal ns1'') -n\<longrightarrow>^j (reached_bb, reached_cont, reached_state)" 
      and "bb = BigBlock name [] (Some (WhileWrapper loop)) None"
      and "\<And>m3 s3. (A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl n, Normal ns1'') -n\<rightarrow>* (m3, s3)) \<Longrightarrow> s3 \<noteq> Failure"
      and "\<And>m' s'. (A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl n, Normal ns1'') -n\<rightarrow>* (m', s')) \<Longrightarrow>
           is_final_config (m', s') \<Longrightarrow> \<forall>ns_end. s' = Normal ns_end \<longrightarrow> (expr_all_sat A \<Lambda>1_local \<Gamma> \<Omega> ns_end) posts"
      and "\<And> j''. 
            j = Suc j'' \<Longrightarrow>
            A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile>(BigBlock name [] (Some loop) None, KEndBlock cont0, Normal ns1'') -n\<longrightarrow>^j'' (reached_bb, reached_cont, reached_state) \<Longrightarrow>
           (\<And>m' s'. A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl n, Normal ns1'') -n\<rightarrow>* (m', s') \<Longrightarrow> s' \<noteq> Failure) \<Longrightarrow>
           (\<And>m' s'. (A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl n, Normal ns1'') -n\<rightarrow>* (m', s')) \<Longrightarrow>
           is_final_config (m', s') \<Longrightarrow> \<forall>ns_end. s' = Normal ns_end \<longrightarrow> (expr_all_sat A \<Lambda>1_local \<Gamma> \<Omega> ns_end) posts) \<Longrightarrow>
           (valid_configuration A \<Lambda> \<Gamma> \<Omega> posts reached_bb reached_cont reached_state)"
    shows "valid_configuration A \<Lambda> \<Gamma> \<Omega> posts reached_bb reached_cont reached_state"
proof -
  from assms(1-2) have disj_a:
    "(valid_configuration A \<Lambda> \<Gamma> \<Omega> posts reached_bb reached_cont reached_state) \<or> 
       (\<exists> l1. (A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile>(BigBlock name [] (Some loop) None, KEndBlock cont0, Normal ns1'') -n\<longrightarrow>^l1 (reached_bb, reached_cont, reached_state)) \<and> (j = Suc l1) )" 
    by (simp add: wrapper_to_endblock)
  thus ?thesis
  proof cases
    assume "(valid_configuration A \<Lambda> \<Gamma> \<Omega> posts reached_bb reached_cont reached_state)" thus ?thesis by simp
  next 
    assume "\<not> ((valid_configuration A \<Lambda> \<Gamma> \<Omega> posts reached_bb reached_cont reached_state))"
    hence "(\<exists> l2. (A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile>(BigBlock name [] (Some loop) None, KEndBlock cont0, Normal ns1'') -n\<longrightarrow>^l2 (reached_bb, reached_cont, reached_state)) \<and> (j = Suc l2) )" 
      using disj_a by blast
    thus ?thesis
    proof -
      obtain l2_conc where conc_trace: "(A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile>(BigBlock name [] (Some loop) None, KEndBlock cont0, Normal ns1'') -n\<longrightarrow>^l2_conc (reached_bb, reached_cont, reached_state))" and 
        succ_rel: "(j = Suc l2_conc)"
        using \<open>\<exists>l2. (A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile>(BigBlock name [] (Some loop) None, KEndBlock cont0, Normal ns1'') -n\<longrightarrow>^l2 (reached_bb, reached_cont, reached_state)) \<and> j = Suc l2\<close> by blast
      show ?thesis
        apply (rule assms(5))
        apply (rule succ_rel)
        apply (rule conc_trace)
        apply (rule assms(3))
        apply (simp)
        apply (rule assms(4))
        apply simp+
        done
    qed
  qed
qed

text \<open>Pair 4: The starting configuration represents a point in the program after a loop and before a consecutive 'unwrapped' loop.
              (This is potentially redundant but I couldn't conclude one example proof without it)\<close>
lemma endblock_skip_wrapper:
  assumes "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (bb0, KEndBlock (KSeq (BigBlock name [] (Some (WhileWrapper str)) tr) cont0), Normal ns3) -n\<longrightarrow>^l 
                          (reached_bb, reached_cont, reached_state)"
      and "bb0 = BigBlock None [] None None"
    shows "(valid_configuration A \<Lambda> \<Gamma> \<Omega> posts reached_bb reached_cont reached_state) \<or> 
           (\<exists> l3. (A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile>((BigBlock name [] (Some str) tr), KEndBlock cont0, Normal ns3) -n\<longrightarrow>^l3 (reached_bb, reached_cont, reached_state)) \<and>
                  l = Suc (Suc (Suc l3)) )"
  using assms
proof (cases l)
  case 0
  then show ?thesis by (metis Ast.valid_configuration_def assms(1) get_state.simps is_final.simps(6) relpowp_fun_conv state.simps(3))
next
  case 1: (Suc l1)
  then show ?thesis 
  proof (cases l1)
    case 0
    from 1 assms this have 
      "(red_bigblock A M \<Lambda> \<Gamma> \<Omega> T (BigBlock None [] None None, KEndBlock (KSeq (BigBlock name [] (Some (WhileWrapper str)) tr) cont0), Normal ns3) (reached_bb, reached_cont, reached_state))"
      by fastforce
    then show ?thesis
    proof cases
      case RedSkipEndBlock thus ?thesis by (simp add: Ast.valid_configuration_def)
    qed auto
  next
    case 2: (Suc l2)
    then show ?thesis
    proof (cases l2)
      case 0 
      from 2 1 have "l = Suc (Suc l2)" by auto
      from 2 1 assms obtain inter_bb inter_cont inter_state  where
        step1: "(red_bigblock A M \<Lambda> \<Gamma> \<Omega> T (BigBlock None [] None None, KEndBlock (KSeq (BigBlock name [] (Some (WhileWrapper str)) tr) cont0), Normal ns3) (inter_bb, inter_cont, inter_state))" and 
        step2: "(red_bigblock A M \<Lambda> \<Gamma> \<Omega> T (inter_bb, inter_cont, inter_state) (reached_bb, reached_cont, reached_state))" 
        using "0" by auto
      from this step1 have "(inter_bb, inter_cont, inter_state) = (BigBlock None [] None None, (KSeq (BigBlock name [] (Some (WhileWrapper str)) tr) cont0), Normal ns3)"
      proof cases
        case RedSkipEndBlock thus ?thesis 
          by blast
      qed auto
      from step2 this have "(reached_bb, reached_cont, reached_state) = ((BigBlock name [] (Some (WhileWrapper str)) tr), cont0, Normal ns3)" 
      proof cases 
        case RedSkip thus ?thesis  using \<open>(inter_bb, inter_cont, inter_state) = (BigBlock None [] None None, (KSeq (BigBlock name [] (Some (WhileWrapper str)) tr) cont0), Normal ns3)\<close> by fastforce
      qed auto
      then show ?thesis by (simp add: Ast.valid_configuration_def)
    next
      case 3: (Suc l3)
      from 3 2 1 have "l = Suc (Suc (Suc l3))" by auto
      from 3 2 1 assms obtain inter_bb inter_cont inter_state inter_bb2 inter_cont2 inter_state2 inter_bb3 inter_cont3 inter_state3 where
        step1: "(red_bigblock A M \<Lambda> \<Gamma> \<Omega> T (BigBlock None [] None None, KEndBlock (KSeq (BigBlock name [] (Some (WhileWrapper str)) tr) cont0), Normal ns3) (inter_bb, inter_cont, inter_state))" and 
        step2: "(red_bigblock A M \<Lambda> \<Gamma> \<Omega> T (inter_bb, inter_cont, inter_state) (inter_bb2, inter_cont2, inter_state2))" and 
        step3: "(red_bigblock A M \<Lambda> \<Gamma> \<Omega> T (inter_bb2, inter_cont2, inter_state2) (inter_bb3, inter_cont3, inter_state3))" and
        rest: "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (inter_bb3, inter_cont3, inter_state3) -n\<longrightarrow>^l3 (reached_bb, reached_cont, reached_state)" 
        by (metis (no_types) get_state.cases relpowp_Suc_D2)

      from this step1 have "(inter_bb, inter_cont, inter_state) = (BigBlock None [] None None, (KSeq (BigBlock name [] (Some (WhileWrapper str)) tr) cont0), Normal ns3)"
      proof cases
        case RedSkipEndBlock thus ?thesis 
          by blast
      qed auto
      from step2 this have "(inter_bb2, inter_cont2, inter_state2) = ((BigBlock name [] (Some (WhileWrapper str)) tr), cont0, Normal ns3)" 
      proof cases 
        case RedSkip thus ?thesis  using \<open>(inter_bb, inter_cont, inter_state) = (BigBlock None [] None None, (KSeq (BigBlock name [] (Some (WhileWrapper str)) tr) cont0), Normal ns3)\<close> by fastforce
      qed auto
      from step3 this have "(inter_bb3, inter_cont3, inter_state3) = ((BigBlock name [] (Some str) tr), KEndBlock cont0, Normal ns3)"
      proof cases
        case RedParsedWhileWrapper thus ?thesis using \<open>(inter_bb2, inter_cont2, inter_state2) = (BigBlock name [] (Some (WhileWrapper str)) tr, cont0, Normal ns3)\<close> by fastforce 
      qed auto
      hence "(A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile>((BigBlock name [] (Some str) tr), KEndBlock cont0, Normal ns3) -n\<longrightarrow>^l3 (reached_bb, reached_cont, reached_state)) \<and> (l = Suc (Suc (Suc l3)))" 
        using \<open>l = Suc (Suc (Suc l3))\<close> rest by blast
      thus ?thesis by blast
    qed
  qed
qed

lemma ending_after_skipping_endblock_and_unwrapping:
  assumes "j = Suc j'"
      and "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile>(bb,
                      KEndBlock (KSeq (BigBlock None [] (Some (WhileWrapper (ParsedWhile next_guard next_invs (next_body_bb#body_bbs)))) None) cont1),
                      Normal ns1'') -n\<longrightarrow>^j'
           (reached_bb, reached_cont, reached_state)"
      and "bb = BigBlock None [] None None"
      and corr: "\<forall>m3 s3. (A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl n, Normal ns1'') -n\<rightarrow>* (m3, s3)) \<longrightarrow> s3 \<noteq> Failure"
      and "\<And>m' s'. (A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl n, Normal ns1'') -n\<rightarrow>* (m', s')) \<Longrightarrow>
           is_final_config (m', s') \<Longrightarrow> \<forall>ns_end. s' = Normal ns_end \<longrightarrow> (expr_all_sat A \<Lambda>1_local \<Gamma> \<Omega> ns_end) posts"
      and guard_false: "(cont_guard = Some guard) \<Longrightarrow> (A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>guard,ns1''\<rangle> \<Down> BoolV False)"
      and "node_to_block G ! n = [Assume c]" 
      and "(UnOp Not guard) \<sim> c"
      and "List.member (out_edges(G) ! n) n1"
      and "\<And> j'''.
          j' = Suc (Suc (Suc j''')) \<Longrightarrow>
          node_to_block G ! n = [Assume c] \<Longrightarrow>
          (UnOp Not guard) \<sim> c \<Longrightarrow>
          List.member (out_edges(G) ! n) n1 \<Longrightarrow>
          A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile>((BigBlock None [] (Some (ParsedWhile next_guard next_invs (next_body_bb#body_bbs))) None), KEndBlock cont1, Normal ns1'') -n\<longrightarrow>^j''' 
              (reached_bb, reached_cont, reached_state) \<Longrightarrow>
          (\<And>m' s'. A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl n, Normal ns1'') -n\<rightarrow>* (m', s') \<Longrightarrow> s' \<noteq> Failure) \<Longrightarrow>
          (\<And>m' s'. (A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl n, Normal ns1'') -n\<rightarrow>* (m', s')) \<Longrightarrow>
           is_final_config (m', s') \<Longrightarrow> \<forall>ns_end. s' = Normal ns_end \<longrightarrow> (expr_all_sat A \<Lambda>1_local \<Gamma> \<Omega> ns_end) posts) \<Longrightarrow> 
          (Ast.valid_configuration A \<Lambda> \<Gamma> \<Omega> posts reached_bb reached_cont reached_state)"
    shows "(Ast.valid_configuration A \<Lambda> \<Gamma> \<Omega> posts reached_bb reached_cont reached_state)"
  using assms
proof -
  from assms(2-3) have disj_a:
    "(valid_configuration A \<Lambda> \<Gamma> \<Omega> posts reached_bb reached_cont reached_state) \<or> 
       (\<exists> l3. (A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> ((BigBlock None [] (Some (ParsedWhile next_guard next_invs (next_body_bb#body_bbs))) None), KEndBlock cont1, Normal ns1'') 
              -n\<longrightarrow>^l3 (reached_bb, reached_cont, reached_state)) \<and> (j' = Suc (Suc (Suc l3))) )"
    by (simp add: endblock_skip_wrapper)
  thus ?thesis
  proof cases
    assume "(valid_configuration A \<Lambda> \<Gamma> \<Omega> posts reached_bb reached_cont reached_state)" thus ?thesis by simp
  next 
    assume "\<not> ((valid_configuration A \<Lambda> \<Gamma> \<Omega> posts reached_bb reached_cont reached_state))"
    hence skipped_endblock: 
      "(\<exists> l3. (A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile>((BigBlock None [] (Some (ParsedWhile next_guard next_invs (next_body_bb#body_bbs))) None), KEndBlock cont1, Normal ns1'') 
                   -n\<longrightarrow>^l3 (reached_bb, reached_cont, reached_state)) \<and> (j' = Suc (Suc (Suc l3))) )" 
      using disj_a by blast
    thus ?thesis
    proof -
      obtain l3_conc where 
        conc_trace: "(A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile>((BigBlock None [] (Some (ParsedWhile next_guard next_invs (next_body_bb#body_bbs))) None), KEndBlock cont1, Normal ns1'') 
                        -n\<longrightarrow>^l3_conc (reached_bb, reached_cont, reached_state))" and 
        succ_rel: "(j' = Suc (Suc (Suc l3_conc))) " 
        using skipped_endblock by blast
      show ?thesis
        apply (rule assms(10))
        apply (rule succ_rel)
        apply (simp add: assms)
        apply (rule assms(8))
        apply (rule assms(9))
        apply (rule conc_trace)
        apply (simp add: corr)
        apply (rule assms(5))
        apply blast+
        done
    qed
  qed
qed

subsection \<open>Local block lemmas\<close>
text \<open>The following are lemmas proving local relations between various kinds of ast-bigblocks and cfg-blocks\<close>

text \<open>Local relation between an ast-bigblock starting with a non-empty set of simple commands and a cfg-block containing the same simple commands\<close>
lemma block_local_rel_generic:
  assumes block_rel: "ast_cfg_rel guard invs bb cs2"
      and "guard = None"
      and "invs = []"
      and Red_bb_to: "red_bigblock A M \<Lambda> \<Gamma> \<Omega> T (bb, cont0, (Normal ns1)) (reached_bb, reached_cont, reached_state)" 
      and Red_impl: "(\<And> s2'.((red_cmd_list A M \<Lambda> \<Gamma> \<Omega> cs2 (Normal ns1) s2') \<Longrightarrow> (s2' \<noteq> Failure)))"
      and "bb = (BigBlock name cs1 any_str any_tr)"
      and "cs1 \<noteq> Nil"
      and "cs2 \<noteq> Nil"
    shows "reached_state \<noteq> Failure  \<and>
           (\<forall>ns1'. reached_state = Normal ns1' \<longrightarrow> (A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs2, Normal ns1\<rangle> [\<rightarrow>] Normal ns1'))" 
  using assms
proof (induction arbitrary: ns1)
  case (Rel_Main_test bb name cs1 any_str any_tr)
  thus ?case
  proof (cases cs1)
    case Nil
    then show ?thesis using \<open>cs1 \<noteq> Nil\<close> by simp
  next
    case (Cons a list)
    then have "red_bigblock A M \<Lambda> \<Gamma> \<Omega> T ((BigBlock name (a#list) any_str any_tr), cont0, (Normal ns1)) (reached_bb, reached_cont, reached_state)" 
      using Rel_Main_test by blast
    then have "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(a#list), Normal ns1\<rangle> [\<rightarrow>] reached_state" using Rel_Main_test(5) 
    proof cases
      case RedSimpleCmds thus ?thesis by blast
    qed
    then have "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs1, Normal ns1\<rangle> [\<rightarrow>] reached_state" using Cons by simp

    then show ?thesis using Rel_Main_test by auto
  qed 
qed (auto)

text \<open>Local relation between a loop-only(no simple commands) ast-bigblock and a corresponding cfg-block containing assertions of the loop invariants\<close>
lemma block_local_rel_loop_head:
  assumes block_rel: "ast_cfg_rel None assert_invs bb assertions"
      and "bb =  (BigBlock name [] (Some (ParsedWhile loop_guard invs (bb0#body_bbs))) any_tr)"
      and "assert_invs = map Assert invs"
      and Red_bb: "red_bigblock A M \<Lambda> \<Gamma> \<Omega> T (bb, cont0, (Normal ns1)) (reached_bb, reached_cont, reached_state)" 
      and Red_impl: "(\<And> s2'.((red_cmd_list A M \<Lambda> \<Gamma> \<Omega> assertions (Normal ns1) s2') \<Longrightarrow> (s2' \<noteq> Failure)))"
    shows "reached_state \<noteq> Failure  \<and>
           (\<forall>ns1'. reached_state = Normal ns1' \<longrightarrow> (A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>assertions, Normal ns1\<rangle> [\<rightarrow>] Normal ns1'))" 
  using assms
proof cases
  case Rel_Invs
  hence "assertions = map Assert invs" using assms(3) by simp
  from Red_bb show ?thesis
  proof cases
    case RedParsedWhileTrue 
    thus ?thesis using \<open>assertions = (map Assert invs)\<close>  
      by (simp add: asserts_hold_if_invs_hold assms(2))
  next
    case RedParsedWhileFalse 
    thus ?thesis using \<open>assertions = (map Assert invs)\<close>
      by (simp add: asserts_hold_if_invs_hold assms(2))
  next
    case RedParsedWhile_InvFail 
    thus ?thesis 
      using Red_impl \<open>assertions = map Assert invs\<close> one_inv_fails_assertions assms(2) 
      by blast
  qed (auto simp add: assms(2))
next
  case Rel_Main_test
  hence "assertions = map Assert invs" 
    using assms(2-3) by simp
  from Red_bb show ?thesis
  proof cases
    case RedParsedWhileTrue 
    thus ?thesis using \<open>assertions = (map Assert invs)\<close>  
      by (simp add: asserts_hold_if_invs_hold assms(2))
  next
    case RedParsedWhileFalse 
    thus ?thesis using \<open>assertions = (map Assert invs)\<close> 
      by (simp add: asserts_hold_if_invs_hold assms(2))
  next
    case RedParsedWhile_InvFail 
    thus ?thesis using Red_impl \<open>assertions = map Assert invs\<close> one_inv_fails_assertions assms(2)
      by blast
  qed (auto simp add: assms(2))
qed

subsection \<open>Global block lemmas\<close>

text \<open>The following are lemmas proving global relations between various kinds of ast-bigblocks and cfg-blocks\<close>

text \<open>Global lemma for a big block, which concludes the program.\<close>
lemma generic_ending_block_global_rel:
  assumes syn_rel: "ast_cfg_rel None [] bb cs2"
      and j_step_ast_trace: "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (bb, cont0, (Normal ns1)) -n\<longrightarrow>^j (reached_bb, reached_cont, reached_state)"
      and "bb = (BigBlock name cs1 None any_tr)"
      and "((any_tr = None)) \<or> (any_tr = (Some Return))"
      and ending: "any_tr = None \<Longrightarrow> cont0 = KStop"
      and node_to_block_assm: "node_to_block(G) ! n = related_block"
      and block_id:
          "(related_block = cs2) \<or> 
           (related_block = c#cs2) \<and> c = Assume guard \<and> (red_expr A \<Lambda> \<Gamma> \<Omega> guard ns1 (BoolV True)) \<or> 
           (related_block = c#cs2) \<and> c = Assume not_guard \<and> (UnOp Not guard \<sim> not_guard) \<and> (red_expr A \<Lambda> \<Gamma> \<Omega> guard ns1 (BoolV False))"
      and "out_edges G ! n = []"
      and cfg_reaches_not_failure: "\<And> m' s'. (red_cfg_multi A M \<Lambda> \<Gamma> \<Omega> G ((Inl n),(Normal ns1)) (m',s')) \<Longrightarrow> (s' \<noteq> Failure)"
      and cfg_satisfies_posts: "\<And> m' s'. (red_cfg_multi A M \<Lambda> \<Gamma> \<Omega> G ((Inl n),(Normal ns1)) (m',s')) \<Longrightarrow> 
                                      is_final_config (m',s') \<Longrightarrow> (\<forall> ns_end. s' = Normal ns_end \<longrightarrow> (expr_all_sat A \<Lambda> \<Gamma> \<Omega> ns_end) post_invs)"
      and local_rel: "\<And> step_bb step_cont step_state. 
                    red_bigblock A M \<Lambda> \<Gamma> \<Omega> T (bb, KStop, (Normal ns1)) (step_bb, step_cont, step_state) \<Longrightarrow> 
                    (\<And> s2'.((red_cmd_list A M \<Lambda> \<Gamma> \<Omega> (node_to_block(G) ! n) (Normal ns1) s2') \<Longrightarrow> (s2' \<noteq> Failure))) \<Longrightarrow>
                    step_state \<noteq> Failure  \<and>
                    (\<forall>ns1'. step_state = Normal ns1' \<longrightarrow> (A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>node_to_block(G) ! n, Normal ns1\<rangle> [\<rightarrow>] Normal ns1'))"
    shows "(valid_configuration A \<Lambda> \<Gamma> \<Omega> post_invs reached_bb reached_cont reached_state)"
  using assms
proof (cases cs2)
  case Nil 
  hence "cs1 = []" using ast_cfg_rel.cases syn_rel assms(3) by blast 
  thus ?thesis
  proof (cases any_tr)
    case None thus ?thesis
    proof -
      have complete: "(red_cfg_multi A M \<Lambda> \<Gamma> \<Omega> G ((Inl n),(Normal ns1)) (Inr (), Normal ns1))" 
        using block_id \<open>out_edges G ! n = []\<close> Nil node_to_block_assm
        by (metis RedCmdListNil RedNormalReturn push_through_assumption0 push_through_assumption1 r_into_rtranclp)
      hence "(expr_all_sat A \<Lambda> \<Gamma> \<Omega> ns1) post_invs" using cfg_satisfies_posts 
        using is_final_config.simps(2) by blast
      thus ?thesis using complete Ast.valid_configuration_def
        by (metis None Pair_inject \<open>cs1 = []\<close> assms(3) cfg_satisfies_posts ending final_is_static_propagate is_final.simps(1) is_final_config.simps(2) j_step_ast_trace relpowp_imp_rtranclp state.distinct(1))
    qed
  next
    case (Some a)
    then show ?thesis
    proof (cases j)
      case 0
      from this j_step_ast_trace assms(3) 
      have "(reached_bb, reached_cont, reached_state) = ((BigBlock name [] None (Some Return)), cont0, (Normal ns1))" 
        using \<open>cs1 = []\<close> Some assms(4) by simp
      then show ?thesis by (simp add: valid_configuration_def)
    next
      case (Suc j')
      thus ?thesis 
      proof (cases a)
        case (Return) 
        from Suc j_step_ast_trace assms(3) obtain inter_bb inter_cont inter_state where
          step0: "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> \<langle>((BigBlock name cs1 None any_tr), cont0, (Normal ns1))\<rangle> \<longrightarrow> (inter_bb, inter_cont, inter_state)" and
          rest0: "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (inter_bb, inter_cont, inter_state) -n\<longrightarrow>^j' (reached_bb, reached_cont, reached_state)"
          by (metis prod_cases3 relpowp_Suc_D2) 
        from cfg_reaches_not_failure have 
          cfg_local: "(\<And> s2'.((red_cmd_list A M \<Lambda> \<Gamma> \<Omega> (node_to_block(G) ! n) (Normal ns1) s2') \<Longrightarrow> (s2' \<noteq> Failure)))"
          using assms(5) dag_verifies_propagate_2 by blast

        from step0 Return assms(3) Some Nil syn_rel have
          inter_state_resolution: "inter_state = Normal ns1"
        proof cases
          case RedReturn 
          thus ?thesis by (simp add: RedReturn)
        qed (auto simp add: \<open>cs1 = []\<close>)            

        from this cfg_local step0 have 
          "inter_state \<noteq> Failure  \<and>
            (\<forall>ns1'. inter_state = Normal ns1' \<longrightarrow> (A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>node_to_block(G) ! n, Normal ns1\<rangle> [\<rightarrow>] Normal ns1'))"
          using assms by (metis RedReturn \<open>cs1 = []\<close>)

        from step0 have inter_conc: "(inter_bb, inter_cont, inter_state) = ((BigBlock name [] None None), KStop, Normal ns1)" 
          using \<open>cs1 = []\<close> Return Some
          by (cases) auto

        hence "(red_cfg A M \<Lambda> \<Gamma> \<Omega> G ((Inl n),(Normal ns1)) (Inr (), Normal ns1))"
          by (simp add: RedNormalReturn 
              \<open>inter_state \<noteq> Failure \<and> (\<forall>ns1'. inter_state = Normal ns1' \<longrightarrow> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>node_to_block G ! n,Normal ns1\<rangle> [\<rightarrow>] Normal ns1')\<close> 
              assms(8))

        hence "(red_cfg_multi A M \<Lambda> \<Gamma> \<Omega> G ((Inl n),(Normal ns1)) (Inr (), Normal ns1))" by simp
        hence "(expr_all_sat A \<Lambda> \<Gamma> \<Omega> ns1) post_invs" 
          using cfg_satisfies_posts is_final_config.simps(2) by blast
        then have "is_final (inter_bb, inter_cont, inter_state)"
          using inter_conc is_final.simps(1) by blast
        then have "(valid_configuration A \<Lambda> \<Gamma> \<Omega> post_invs inter_bb inter_cont inter_state)" 
          unfolding valid_configuration_def
          apply (simp only: get_state.simps)
          apply (simp add: inter_conc)
          using \<open>(expr_all_sat A \<Lambda> \<Gamma> \<Omega> ns1) post_invs\<close> expr_all_sat_def inter_conc by blast
        then show ?thesis
          by (metis \<open>is_final (inter_bb, inter_cont, inter_state)\<close> final_is_static_propagate inter_conc prod.sel(1) prod.sel(2) relpowp_imp_rtranclp rest0)
      next
        case (Goto x3)
        thus ?thesis using assms(4) Some by blast
      qed
    qed
  qed
next
  case (Cons) 
  hence "cs1 \<noteq> []" using ast_cfg_rel.simps syn_rel assms(3) by blast
  thus ?thesis
  proof (cases j)
    case 0
    from this j_step_ast_trace assms(3) 
    have eq: "(reached_bb, reached_cont, reached_state) = ((BigBlock name cs1 None any_tr), cont0, (Normal ns1))" by simp
    then show ?thesis 
    proof (cases any_tr)
      case None
      then show ?thesis using eq \<open>cs1 \<noteq> []\<close> Ast.valid_configuration_def get_state.simps
        by (metis is_final.simps(2) list.collapse state.distinct(1))
    next
      case (Some a)
      then show ?thesis 
      proof (cases a)
        case (Goto x1)
        then show ?thesis using Some assms(4) by blast
      next
        case Return
        then show ?thesis using eq Some by (simp add: Ast.valid_configuration_def) 
      qed
    qed
  next
    case (Suc j')
    from this j_step_ast_trace assms(3) obtain inter_bb inter_cont inter_state where
      step: "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> \<langle>((BigBlock name cs1 None any_tr), cont0, (Normal ns1))\<rangle> \<longrightarrow> (inter_bb, inter_cont, inter_state)" and
      rest: "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (inter_bb, inter_cont, inter_state) -n\<longrightarrow>^j' (reached_bb, reached_cont, reached_state)"
      by (metis prod_cases3 relpowp_Suc_D2) 
    then show ?thesis 
    proof (cases any_tr)
      case None
      from step this have concrete_inter: "(inter_bb, inter_cont, inter_state) = (BigBlock name [] None None, cont0, inter_state)"
        by (cases) (auto simp add: RedSimpleCmds ending)

      have Red_impl: "(\<And> s2'.((red_cmd_list A M \<Lambda> \<Gamma> \<Omega> (node_to_block(G) ! n) (Normal ns1) s2') \<Longrightarrow> (s2' \<noteq> Failure)))"
        using assms(5) cfg_reaches_not_failure dag_verifies_propagate_2 by blast

      have "cont0 = KStop" using None by (simp add: ending)

      from step \<open>cont0 = KStop\<close> have local_corr:
        "inter_state \<noteq> Failure  \<and>
            (\<forall>ns1'. inter_state = Normal ns1' \<longrightarrow> (A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>node_to_block(G) ! n, Normal ns1\<rangle> [\<rightarrow>] Normal ns1'))"
        using Red_impl block_local_rel_generic local.Cons local.step syn_rel assms by (cases) blast+

      hence "(\<forall>ns1'. inter_state = Normal ns1' \<longrightarrow> red_cfg A M \<Lambda> \<Gamma> \<Omega> G ((Inl n),(Normal ns1)) (Inr (), Normal ns1'))"
        by (simp add: RedCmdListNil RedNormalReturn assms(7-8) local.Cons)

      hence "(\<forall>ns1'. inter_state = Normal ns1' \<longrightarrow> red_cfg_multi A M \<Lambda> \<Gamma> \<Omega> G ((Inl n),(Normal ns1)) (Inr (), Normal ns1'))" 
        by blast
      hence posts_sat: "\<forall>ns1'. inter_state = Normal ns1' \<longrightarrow> (expr_all_sat A \<Lambda> \<Gamma> \<Omega> ns1') post_invs" 
        using cfg_satisfies_posts is_final_config.simps(2) by blast

      have "is_final (inter_bb, inter_cont, inter_state)" using concrete_inter ending \<open>cont0 = KStop\<close> by simp 

      hence valid_inter: "(valid_configuration A \<Lambda> \<Gamma> \<Omega> post_invs inter_bb inter_cont inter_state)" 
        unfolding valid_configuration_def
        using posts_sat local_corr by auto

      then show ?thesis 
        by (metis Pair_inject \<open>is_final (inter_bb, inter_cont, inter_state)\<close> concrete_inter final_is_static_propagate relpowp_imp_rtranclp rest)
    next
      case (Some transfer)
      then show ?thesis
      proof (cases transfer)
        case (Goto x1)
        then show ?thesis using Some assms(4) by blast
      next
        case (Return)
        from step this Some have concrete_inter: "(inter_bb, inter_cont, inter_state) = (BigBlock name [] None (Some Return), cont0, inter_state)"
        proof cases
          case RedSimpleCmds thus ?thesis using Return Some by blast
        qed (auto simp add: \<open>cs1 \<noteq> []\<close>)

        have Red_impl: "(\<And> s2'.((red_cmd_list A M \<Lambda> \<Gamma> \<Omega> (node_to_block(G) ! n) (Normal ns1) s2') \<Longrightarrow> (s2' \<noteq> Failure)))" 
          using dag_verifies_propagate_2  assms(5) cfg_reaches_not_failure by blast

        from step have local_corr:
          "inter_state \<noteq> Failure  \<and>
              (\<forall>ns1'. inter_state = Normal ns1' \<longrightarrow> (A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>node_to_block(G) ! n, Normal ns1\<rangle> [\<rightarrow>] Normal ns1'))"
          using Red_impl \<open>cs1 \<noteq> []\<close> assms(3) block_id block_local_rel_generic list.distinct(1) 
            local.Cons node_to_block_assm push_through_assumption0 push_through_assumption1 syn_rel
          by metis

        hence "(\<forall>ns1'. inter_state = Normal ns1' \<longrightarrow> red_cfg A M \<Lambda> \<Gamma> \<Omega> G ((Inl n),(Normal ns1)) (Inr (), Normal ns1'))"
          by (simp add: RedCmdListNil RedNormalReturn assms(7-8) local.Cons)

        hence "(\<forall>ns1'. inter_state = Normal ns1' \<longrightarrow> red_cfg_multi A M \<Lambda> \<Gamma> \<Omega> G ((Inl n),(Normal ns1)) (Inr (), Normal ns1'))" by blast
        hence posts_sat: "\<forall>ns1'. inter_state = Normal ns1' \<longrightarrow> (expr_all_sat A \<Lambda> \<Gamma> \<Omega> ns1') post_invs" 
          using cfg_satisfies_posts is_final_config.simps(2) by blast

        from step have "inter_state \<noteq> Failure" using Red_impl block_local_rel_generic local.Cons assms
          using local_corr by fastforce

        then show ?thesis
        proof (cases inter_state)
          case (Normal x1)
          then show ?thesis
          proof (cases j')
            case 0
            then show ?thesis using concrete_inter 
              by (metis Ast.valid_configuration_def \<open>inter_state \<noteq> Failure\<close> get_state.simps is_final.simps(4) relpowp_0_E rest)
          next
            case (Suc j'')
            from this rest obtain inter_bb2 inter_cont2 inter_state2 where
              snd_step: "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> \<langle>(inter_bb, inter_cont, inter_state)\<rangle> \<longrightarrow> (inter_bb2, inter_cont2, inter_state2)" and
              snd_rest: "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (inter_bb2, inter_cont2, inter_state2) -n\<longrightarrow>^j'' (reached_bb, reached_cont, reached_state)"
              by (metis get_state.cases relpowp_Suc_E2)
            then have inter2_conc: "(inter_bb2, inter_cont2, inter_state2) = ((BigBlock name [] None None), KStop, inter_state)" 
              using concrete_inter \<open>inter_state \<noteq> Failure\<close> Normal
              by (cases) blast+
            hence "is_final (inter_bb2, inter_cont2, inter_state2)" by simp
            hence valid_inter: "(valid_configuration A \<Lambda> \<Gamma> \<Omega> post_invs inter_bb2 inter_cont2 inter_state2)" 
              using Ast.valid_configuration_def \<open>inter_state \<noteq> Failure\<close> inter2_conc posts_sat by blast
            then show ?thesis
              by (metis \<open>is_final (inter_bb2, inter_cont2, inter_state2)\<close> final_is_static_propagate inter2_conc prod.inject relpowp_imp_rtranclp snd_rest)
          qed
        next
          case Failure
          then show ?thesis using \<open>inter_state \<noteq> Failure\<close> by simp
        next
          case Magic
          then show ?thesis by (metis valid_configuration_def \<open>inter_state \<noteq> Failure\<close>  magic_propagates rest state.simps(5))
        qed
      qed
    qed
  qed
qed

text \<open>Global lemma for a big block with a non-empty set of simple commands that enters a loop after it executes its simple cmds.\<close>
lemma block_global_rel_while_successor:
  assumes j_step_ast_trace: 
           "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (bb, cont1, Normal ns1) -n\<longrightarrow>^j (reached_bb, reached_cont, reached_state)"
      and syn_rel: "ast_cfg_rel None [] bb cmds"
      and "bb = (BigBlock name cmds (Some (WhileWrapper (ParsedWhile guard invs (body_bb0#body_bbs)))) None)"
      and "cmds \<noteq> []"
      and "node_to_block(G) ! n = related_block"
      and block_id:
    "(related_block = cmds) \<or> 
       (related_block = c#cmds) \<and> c = Assume entry_guard \<and> (red_expr A \<Lambda> \<Gamma> \<Omega> entry_guard ns1 (BoolV True)) \<or> 
       (related_block = c#cmds) \<and> c = Assume not_guard \<and> (UnOp Not entry_guard \<sim> not_guard) \<and> (red_expr A \<Lambda> \<Gamma> \<Omega> entry_guard ns1 (BoolV False))"
      and cfg_is_correct: "\<And> m' s'. (red_cfg_multi A M \<Lambda> \<Gamma> \<Omega> G ((Inl n),(Normal ns1)) (m',s')) \<Longrightarrow> (s' \<noteq> Failure)"
      and cfg_satisfies_posts: "\<And> m' s'. (red_cfg_multi A M \<Lambda> \<Gamma> \<Omega> G ((Inl n),(Normal ns1)) (m',s')) \<Longrightarrow> 
                                      is_final_config (m',s') \<Longrightarrow> (\<forall> ns_end. s' = Normal ns_end \<longrightarrow> (expr_all_sat A \<Lambda> \<Gamma> \<Omega> ns_end) posts)"
      and block_local_rel:
    "\<And> reached_bb_inter reached_cont_inter reached_state_inter. 
    (red_bigblock A M \<Lambda> \<Gamma> \<Omega> T (bb, cont1, (Normal ns1)) (reached_bb_inter, reached_cont_inter, reached_state_inter)) \<Longrightarrow> 
    (\<And> s2'.((red_cmd_list A M \<Lambda> \<Gamma> \<Omega> (node_to_block G ! n) (Normal ns1) s2') \<Longrightarrow> (s2' \<noteq> Failure))) \<Longrightarrow>   
    (reached_state_inter \<noteq> Failure  \<and> (\<forall>ns1'. reached_state_inter = Normal ns1' \<longrightarrow> (A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(node_to_block G ! n), Normal ns1\<rangle> [\<rightarrow>] Normal ns1')))"
      and global_rel_succ:
       "\<And> ns2 k.
         k < j \<Longrightarrow>
         (\<forall>msuc2. List.member (out_edges(G) ! n) msuc2 \<longrightarrow> (\<forall>m3 s3. (A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl msuc2, Normal ns2) -n\<rightarrow>* (m3, s3)) \<longrightarrow> s3 \<noteq> Failure)) \<Longrightarrow>
         (\<forall>msuc2. List.member (out_edges(G) ! n) msuc2 \<longrightarrow> (\<forall>m' s'. (A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl msuc2, Normal ns2) -n\<rightarrow>* (m', s')) \<longrightarrow>
                                                             is_final_config (m', s') \<longrightarrow> 
                                                             (\<forall>ns_end. s' = Normal ns_end \<longrightarrow> (expr_all_sat A \<Lambda> \<Gamma> \<Omega> ns_end) posts))) \<Longrightarrow>
         A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> ((BigBlock name [] (Some (ParsedWhile guard invs (body_bb0#body_bbs))) None), KEndBlock cont1, Normal ns2) -n\<longrightarrow>^k 
                      (reached_bb, reached_cont, reached_state) \<Longrightarrow> 
         (valid_configuration A \<Lambda> \<Gamma> \<Omega> posts reached_bb reached_cont reached_state)"
    shows "(valid_configuration A \<Lambda> \<Gamma> \<Omega> posts reached_bb reached_cont reached_state)"
  using assms
proof cases
  assume "j = 0"
  then have "(reached_bb, reached_cont, reached_state) = 
             ((BigBlock name cmds (Some (WhileWrapper (ParsedWhile guard invs (body_bb0#body_bbs)))) None), cont1, Normal ns1)" using j_step_ast_trace assms(3) by auto
  thus ?thesis by (simp add: valid_configuration_def)
next
  assume "j \<noteq> 0"
  from this obtain j' where "j = Suc j'" using not0_implies_Suc by blast
  from this j_step_ast_trace assms(3) obtain inter_bb inter_cont inter_state where
    first_step: "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> \<langle>((BigBlock name cmds (Some (WhileWrapper (ParsedWhile guard invs (body_bb0#body_bbs)))) None), cont1, Normal ns1)\<rangle> \<longrightarrow> (inter_bb, inter_cont, inter_state)" and 
    rest: "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (inter_bb, inter_cont, inter_state) -n\<longrightarrow>^j' (reached_bb, reached_cont, reached_state)"
    by (metis (no_types) get_state.cases relpowp_Suc_D2)
  from this have a1: "(inter_bb, inter_cont, inter_state) = ((BigBlock name [] (Some (WhileWrapper (ParsedWhile guard invs (body_bb0#body_bbs)))) None), cont1, inter_state)"
  proof cases
    case RedSimpleCmds thus ?thesis by blast
  qed (auto simp add: \<open>cmds \<noteq> []\<close>)
  have Red_impl: "(\<And> s2'.((red_cmd_list A M \<Lambda> \<Gamma> \<Omega> (node_to_block G ! n) (Normal ns1) s2') \<Longrightarrow> (s2' \<noteq> Failure)))" using dag_verifies_propagate_2 cfg_is_correct assms(5) 
    by blast
  have local_conclusion: "inter_state \<noteq> Failure  \<and> (\<forall>ns1'. inter_state = Normal ns1' \<longrightarrow> (A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(node_to_block G ! n), Normal ns1\<rangle> [\<rightarrow>] Normal ns1'))" 
    using Red_impl first_step assms(3-4) block_local_rel_generic syn_rel block_local_rel by blast
  show ?thesis 
  proof (cases inter_state)
    case (Normal x1)
    hence "(A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(node_to_block G ! n), Normal ns1\<rangle> [\<rightarrow>] inter_state)" using local_conclusion by blast
    then show ?thesis
    proof (cases j')
      case 0
      then show ?thesis 
        by (metis Normal a1 nat.discI rest wrapper_to_endblock)
    next
      case 2: (Suc j'')
      hence Red_cfg_conc: 
        "(\<forall>msuc2. List.member (out_edges(G) ! n) msuc2 \<longrightarrow> (\<forall>m3 s3. (A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl msuc2, inter_state) -n\<rightarrow>* (m3, s3)) \<longrightarrow> s3 \<noteq> Failure))" 
        using dag_verifies_propagate Normal \<open>A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(node_to_block G ! n),Normal ns1\<rangle> [\<rightarrow>] inter_state\<close> assms(5) cfg_is_correct 
        by blast

      hence Red_cfg_sat_conc: 
        "(\<forall>msuc2. List.member (out_edges(G) ! n) msuc2 \<longrightarrow> (\<forall>m' s'. (A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl msuc2, inter_state) -n\<rightarrow>* (m', s')) \<longrightarrow>
                                                             is_final_config (m', s') \<longrightarrow> 
                                                             (\<forall>ns_end. s' = Normal ns_end \<longrightarrow> (expr_all_sat A \<Lambda> \<Gamma> \<Omega> ns_end) posts)))" 
        by (metis (no_types) Normal RedNormalSucc cfg_satisfies_posts converse_rtranclp_into_rtranclp local_conclusion)

      from 2 j_step_ast_trace assms(3) obtain inter_bb2 inter_cont2 inter_state2 where
        first_step_2: "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> \<langle>(inter_bb, inter_cont, inter_state)\<rangle> \<longrightarrow> (inter_bb2, inter_cont2, inter_state2)" and 
        rest_2: "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (inter_bb2, inter_cont2, inter_state2) -n\<longrightarrow>^j'' (reached_bb, reached_cont, reached_state)"
        by (metis get_state.cases relpowp_Suc_E2 rest)
      from this have a3: "(inter_bb2, inter_cont2, inter_state2) = 
                          ((BigBlock name [] (Some (ParsedWhile guard invs (body_bb0#body_bbs))) None), KEndBlock cont1, inter_state)"
        using a1 Normal
      proof cases
        case RedParsedWhileWrapper 
        thus ?thesis using a1 by fastforce
      qed auto 

      have "j'' < j" by (simp add: "2" \<open>j = Suc j'\<close>)
      then show ?thesis using a3 rest_2 Normal Red_cfg_conc assms(9) cfg_satisfies_posts Red_cfg_sat_conc global_rel_succ 
        by fastforce
    qed
  next
    case Failure
    then show ?thesis using local_conclusion by blast
  next
    case Magic
    then show ?thesis by (metis valid_configuration_def local_conclusion magic_propagates rest state.simps(5))
  qed
qed

text \<open>Global lemma for a big block that's the head of a loop. 
      This means that it is a big block with a while-loop as its structured command and its set of simple commands is empty. 
      The body of the loop is required to be non-empty.\<close>
lemma block_global_rel_loop_head:
  assumes block_rel: "ast_cfg_rel None assertions bb assertions"
      and ast_trace: "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (bb, cont0, (Normal ns1)) -n\<longrightarrow>^j (reached_bb, reached_cont, reached_state)"
      and cfg_correct: "(\<And> m2 s2. ((red_cfg_multi A M \<Lambda> \<Gamma> \<Omega> G (Inl n, Normal ns1) (m2, s2)) \<Longrightarrow> (s2 \<noteq> Failure)))"
      and cfg_satisfies_post: "(\<And> m2 s2. (red_cfg_multi A M \<Lambda> \<Gamma> \<Omega> G (Inl n, Normal ns1) (m2, s2)) \<Longrightarrow>
                                        is_final_config (m2, s2) \<Longrightarrow> \<forall>ns_end. s2 = Normal ns_end \<longrightarrow> (expr_all_sat A \<Lambda> \<Gamma> \<Omega> ns_end) posts)"
      and "bb = (BigBlock name [] any_str any_tr)"
      and bb_successor_while: "any_str = Some (ParsedWhile cont_guard invs (bb0#body_bbs))"
      and block_local_rel:
      "\<And> reached_bb_inter reached_cont_inter reached_state_inter.
       (red_bigblock A M \<Lambda> \<Gamma> \<Omega> T (bb, cont0, (Normal ns1)) (reached_bb_inter, reached_cont_inter, reached_state_inter)) \<Longrightarrow> 
       (\<And> s2'.((red_cmd_list A M \<Lambda> \<Gamma> \<Omega> assertions (Normal ns1) s2') \<Longrightarrow> 
       (s2' \<noteq> Failure))) \<Longrightarrow>   
       reached_state_inter \<noteq> Failure \<and> 
       (\<forall>ns1'. reached_state_inter = Normal ns1' \<longrightarrow> (A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>assertions, Normal ns1\<rangle> [\<rightarrow>] Normal ns1'))"
      and "node_to_block(G) ! n = assertions"
      and "cont0 = KEndBlock cont1"
      and succ_correct: 
    "\<And> ns1'' loop_guard j'. 
    j = Suc j' \<Longrightarrow>
    (\<forall>msuc2.  List.member (out_edges(G) ! n) msuc2 \<longrightarrow> (\<forall>m3 s3. ((A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl(msuc2), Normal ns1'') -n\<rightarrow>* (m3, s3)) \<longrightarrow> s3 \<noteq> Failure))) \<Longrightarrow>
    (\<forall>msuc2.  List.member (out_edges(G) ! n) msuc2 \<longrightarrow> (\<forall>m' s'. ((A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl (msuc2), Normal ns1'') -n\<rightarrow>* (m', s')) \<longrightarrow>
                                                        is_final_config (m', s') \<longrightarrow> 
                                                        (\<forall>ns_end. s' = Normal ns_end \<longrightarrow> (expr_all_sat A \<Lambda> \<Gamma> \<Omega> ns_end) posts)))) \<Longrightarrow>
    ((cont_guard = Some loop_guard) \<and> 
      (red_expr A \<Lambda> \<Gamma> \<Omega> loop_guard ns1'' (BoolV True)) \<and> 
      A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (bb0, convert_list_to_cont (( body_bbs)@[bb]) (KEndBlock cont1), (Normal ns1'')) -n\<longrightarrow>^j' (reached_bb, reached_cont, reached_state)) \<or> 
    ((cont_guard = Some loop_guard) \<and> 
      (red_expr A \<Lambda> \<Gamma> \<Omega> loop_guard ns1'' (BoolV False)) \<and> 
      A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> ((BigBlock name [] None None), KEndBlock cont1, (Normal ns1'')) -n\<longrightarrow>^j' (reached_bb, reached_cont, reached_state)) \<or>
    ((cont_guard = None) \<and> 
     ((A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> ((BigBlock name [] None None), KEndBlock cont1, (Normal ns1'')) -n\<longrightarrow>^j' (reached_bb, reached_cont, reached_state)) \<or>
      (A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (bb0, convert_list_to_cont (( body_bbs)@[bb]) (KEndBlock cont1), (Normal ns1'')) -n\<longrightarrow>^j' (reached_bb, reached_cont, reached_state))))  \<Longrightarrow>  
    (Ast.valid_configuration A \<Lambda> \<Gamma> \<Omega> posts reached_bb reached_cont reached_state)"
    shows "(Ast.valid_configuration A \<Lambda> \<Gamma> \<Omega> posts reached_bb reached_cont reached_state)" 
  using assms cases
proof -
  show ?thesis 
  proof cases
    assume "j = 0"
    hence "(reached_bb, reached_cont, reached_state) = ((BigBlock name [] any_str any_tr), cont0, (Normal ns1))" using ast_trace assms(5) by simp 
    thus ?thesis by (simp add: Ast.valid_configuration_def \<open>cont0 = KEndBlock cont1\<close>)
  next
    assume "j \<noteq> 0" 
    from this obtain j' where "j = Suc j'" using not0_implies_Suc by blast

    from ast_trace this assms(5) obtain inter_bb inter_cont inter_state where
      first_step: "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> \<langle>((BigBlock name [] any_str any_tr), cont0, (Normal ns1))\<rangle> \<longrightarrow> (inter_bb, inter_cont, inter_state)" and
      rest: "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (inter_bb, inter_cont, inter_state) -n\<longrightarrow>^j' (reached_bb, reached_cont, reached_state)"
      by (metis prod_cases3 relpowp_Suc_D2)

    show ?thesis
    proof (cases cont_guard)
      case None
      from first_step show ?thesis using bb_successor_while
      proof cases
        case RedParsedWhileTrue
        hence concrete_inter1: "(inter_bb, inter_cont, inter_state) = (bb0, convert_list_to_cont (( body_bbs)@[(BigBlock name [] any_str any_tr)]) cont0, (Normal ns1))"
          using bb_successor_while None by blast

        from first_step
        have succ_cfg_correct: "(\<forall>msuc2.  List.member (out_edges(G) ! n) msuc2 \<longrightarrow> (\<forall>m3 s3. ((A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl(msuc2), inter_state) -n\<rightarrow>* (m3, s3)) \<longrightarrow> s3 \<noteq> Failure)))"
          by (metis Pair_inject assms(5) assms(8) block_local_rel cfg_correct concrete_inter1 dag_verifies_propagate dag_verifies_propagate_2)

        from first_step
        have succ_cfg_satisfies_post: 
          "(\<forall>msuc2.  List.member (out_edges(G) ! n) msuc2 \<longrightarrow> 
                                                        (\<forall>m' s'. ((A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl (msuc2), inter_state) -n\<rightarrow>* (m', s')) \<longrightarrow>
                                                        is_final_config (m', s') \<longrightarrow> 
                                                        (\<forall>ns_end. s' = Normal ns_end \<longrightarrow> (expr_all_sat A \<Lambda> \<Gamma> \<Omega> ns_end) posts))) )"
          using cfg_satisfies_post 
          by (metis (no_types) RedNormalSucc assms(5) assms(8) block_local_rel cfg_correct converse_rtranclp_into_rtranclp dag_verifies_propagate_2 local.RedParsedWhileTrue(4))

        show ?thesis using \<open>j = Suc j'\<close> succ_cfg_correct succ_cfg_satisfies_post None rest concrete_inter1 succ_correct assms(5) \<open>cont0 = KEndBlock cont1\<close> by blast 
      next 
        case RedParsedWhileFalse
        hence concrete_inter2: "(inter_bb, inter_cont, inter_state) = ((BigBlock name [] None None), cont0, (Normal ns1))" by simp

        from first_step
        have succ_cfg_correct: "(\<forall>msuc2.  List.member (out_edges(G) ! n) msuc2 \<longrightarrow> (\<forall>m3 s3. ((A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl(msuc2), inter_state) -n\<rightarrow>* (m3, s3)) \<longrightarrow> s3 \<noteq> Failure)))"
          by (metis assms(5) assms(8) block_local_rel cfg_correct dag_verifies_propagate dag_verifies_propagate_2 local.RedParsedWhileFalse(5))

        from first_step
        have succ_cfg_satisfies_post: 
          "(\<forall>msuc2.  List.member (out_edges(G) ! n) msuc2 \<longrightarrow> 
                                                        (\<forall>m' s'. ((A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl (msuc2), inter_state) -n\<rightarrow>* (m', s')) \<longrightarrow>
                                                        is_final_config (m', s') \<longrightarrow> 
                                                        (\<forall>ns_end. s' = Normal ns_end \<longrightarrow> (expr_all_sat A \<Lambda> \<Gamma> \<Omega> ns_end) posts))) )"
          using cfg_satisfies_post 
          by (metis (no_types) RedNormalSucc assms(5) assms(8) block_local_rel cfg_correct converse_rtranclp_into_rtranclp dag_verifies_propagate_2 local.RedParsedWhileFalse(5))

        show ?thesis using \<open>j = Suc j'\<close> succ_cfg_correct succ_cfg_satisfies_post None rest concrete_inter2 succ_correct \<open>cont0 = KEndBlock cont1\<close>  by blast
      next 
        case RedParsedWhile_InvFail thus ?thesis using assms(8) block_local_rel cfg_correct dag_verifies_propagate_2 first_step assms(5) by blast
      qed auto
    next
      case (Some concrete_loop_guard)
      then show ?thesis 
      proof cases
        assume guard_true: "(red_expr A \<Lambda> \<Gamma> \<Omega> concrete_loop_guard ns1 (BoolV True))"
        hence guard_not_false: "\<not> (red_expr A \<Lambda> \<Gamma> \<Omega> concrete_loop_guard ns1 (BoolV False))" using expr_eval_determ by blast

        from first_step show ?thesis 
        proof cases
          case RedParsedWhileTrue
          hence concrete_inter3: "(inter_bb, inter_cont, inter_state) = (bb0, convert_list_to_cont (( body_bbs)@[(BigBlock name [] any_str any_tr)]) (cont0), (Normal ns1))"
            using bb_successor_while Some by blast

          from first_step
          have succ_cfg_correct: "(\<forall>msuc2.  List.member (out_edges(G) ! n) msuc2 \<longrightarrow> (\<forall>m3 s3. ((A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl(msuc2), inter_state) -n\<rightarrow>* (m3, s3)) \<longrightarrow> s3 \<noteq> Failure)))"
            by (metis Pair_inject assms(5) assms(8) block_local_rel cfg_correct concrete_inter3 dag_verifies_propagate dag_verifies_propagate_2)

          from first_step
          have succ_cfg_satisfies_post: 
            "(\<forall>msuc2.  List.member (out_edges(G) ! n) msuc2 \<longrightarrow> 
                                                          (\<forall>m' s'. ((A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl (msuc2), inter_state) -n\<rightarrow>* (m', s')) \<longrightarrow>
                                                          is_final_config (m', s') \<longrightarrow> 
                                                          (\<forall>ns_end. s' = Normal ns_end \<longrightarrow> (expr_all_sat A \<Lambda> \<Gamma> \<Omega> ns_end) posts))) )"
            using cfg_satisfies_post 
            by (metis (no_types) RedNormalSucc assms(5) assms(8) block_local_rel cfg_correct converse_rtranclp_into_rtranclp dag_verifies_propagate_2 local.RedParsedWhileTrue(4))

          show ?thesis using \<open>j = Suc j'\<close> succ_cfg_correct succ_cfg_satisfies_post Some guard_true rest concrete_inter3 succ_correct assms(5) \<open>cont0 = KEndBlock cont1\<close>  by blast 
        next 
          case RedParsedWhile_InvFail thus ?thesis using assms(8) block_local_rel cfg_correct dag_verifies_propagate_2 first_step assms(5) by blast
        qed (auto simp add: bb_successor_while Some guard_not_false)
      next
        assume guard_not_true: "\<not> (red_expr A \<Lambda> \<Gamma> \<Omega> concrete_loop_guard ns1 (BoolV True))"
        thus ?thesis 
        proof cases
          assume guard_false: "(red_expr A \<Lambda> \<Gamma> \<Omega> concrete_loop_guard ns1 (BoolV False))"

          from first_step show ?thesis 
          proof cases
            case RedParsedWhileFalse
            hence concrete_inter4: "(inter_bb, inter_cont, inter_state) = ((BigBlock name [] None None), cont0, (Normal ns1))" by simp

            from first_step
            have succ_cfg_correct: "(\<forall>msuc2.  List.member (out_edges(G) ! n) msuc2 \<longrightarrow> (\<forall>m3 s3. ((A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl(msuc2), inter_state) -n\<rightarrow>* (m3, s3)) \<longrightarrow> s3 \<noteq> Failure)))"
              by (metis assms(5) assms(8) block_local_rel cfg_correct dag_verifies_propagate dag_verifies_propagate_2 local.RedParsedWhileFalse(5))

            from first_step
            have succ_cfg_satisfies_post: 
              "(\<forall>msuc2.  List.member (out_edges(G) ! n) msuc2 \<longrightarrow> 
                                                        (\<forall>m' s'. (((A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl (msuc2), inter_state) -n\<rightarrow>* (m', s'))) \<longrightarrow>
                                                        is_final_config (m', s') \<longrightarrow> 
                                                        (\<forall>ns_end. s' = Normal ns_end \<longrightarrow> (expr_all_sat A \<Lambda> \<Gamma> \<Omega> ns_end) posts))) )"
              using cfg_satisfies_post 
              by (metis (no_types) RedNormalSucc assms(5) assms(8) block_local_rel cfg_correct converse_rtranclp_into_rtranclp dag_verifies_propagate_2 local.RedParsedWhileFalse(5))

            show ?thesis using \<open>j = Suc j'\<close> succ_cfg_correct succ_cfg_satisfies_post Some guard_false rest concrete_inter4 succ_correct \<open>cont0 = KEndBlock cont1\<close> by blast
          next
            case RedParsedWhile_InvFail thus ?thesis using Some bb_successor_while guard_not_true by blast
          qed (auto simp add: bb_successor_while Some guard_not_true)
        next
          assume guard_not_false: "\<not> (red_expr A \<Lambda> \<Gamma> \<Omega> concrete_loop_guard ns1 (BoolV False))"
          from first_step show ?thesis
          proof cases
            case RedParsedWhile_InvFail thus ?thesis using Some bb_successor_while guard_not_true by blast
          qed (auto simp add: bb_successor_while Some guard_not_true guard_not_false)
        qed
      qed
    qed
  qed
qed 

text \<open>Global lemma for a big block, which enters an if-statement after executing its simple cmds (if there are any).\<close>
lemma block_global_rel_if_successor:
  assumes block_rel: "ast_cfg_rel None [] bb cs2"
      and ast_trace: "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (bb, cont0, (Normal ns1)) -n\<longrightarrow>^j (reached_bb, reached_cont, reached_state)"
      and "bb = (BigBlock name cs1 any_str any_tr)"
      and "node_to_block(G) ! n  = related_block"
      and block_id:
       "(related_block = cs2) \<or> 
       (related_block = c#cs2) \<and> c = Assume guard \<and> (red_expr A \<Lambda> \<Gamma> \<Omega> guard ns1 (BoolV True)) \<or> 
       (related_block = c#cs2) \<and> c = Assume not_guard \<and> (UnOp Not guard \<sim> not_guard) \<and> (red_expr A \<Lambda> \<Gamma> \<Omega> guard ns1 (BoolV False))"
      and cfg_correct: "(\<And> m2 s2. ((red_cfg_multi A M \<Lambda> \<Gamma> \<Omega> G (Inl n, Normal ns1) (m2, s2)) \<Longrightarrow> (s2 \<noteq> Failure)))"
      and cfg_satisfies_post: "(\<And> m2 s2. (red_cfg_multi A M \<Lambda> \<Gamma> \<Omega> G (Inl n, Normal ns1) (m2, s2)) \<Longrightarrow>
                                        is_final_config (m2, s2) \<Longrightarrow> \<forall>ns_end. s2 = Normal ns_end \<longrightarrow> (expr_all_sat A \<Lambda> \<Gamma> \<Omega> ns_end) posts)"
      and bb_successor_if: "any_str = Some (ParsedIf cont_guard (then0#then_bbs) (else0#else_bbs))"
      and block_local_rel:
        "\<And> reached_bb_inter reached_cont_inter reached_state_inter. (red_bigblock A M \<Lambda> \<Gamma> \<Omega> T ((BigBlock name cs1 any_str any_tr), cont0, (Normal ns1)) (reached_bb_inter, reached_cont_inter, reached_state_inter)) \<Longrightarrow> 
        (\<And> s2'.((red_cmd_list A M \<Lambda> \<Gamma> \<Omega> (node_to_block(G) ! n) (Normal ns1) s2') \<Longrightarrow> (s2' \<noteq> Failure))) \<Longrightarrow> 
        cs1 \<noteq> [] \<Longrightarrow> cs2 \<noteq> [] \<Longrightarrow>  
        (reached_state_inter \<noteq> Failure  \<and> (\<forall>ns1'. reached_state_inter = Normal ns1' \<longrightarrow> (A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(node_to_block(G) ! n), Normal ns1\<rangle> [\<rightarrow>] Normal ns1')))"
      and succ_correct: 
        "\<And> ns1'' block_guard k.
         k < j \<Longrightarrow> 
        (\<forall>msuc2.  List.member (out_edges(G) ! n) msuc2 \<longrightarrow> (\<forall>m3 s3. ((A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl(msuc2), Normal ns1'') -n\<rightarrow>* (m3, s3)) \<longrightarrow> s3 \<noteq> Failure))) \<Longrightarrow>
        (\<forall>msuc2.  List.member (out_edges(G) ! n) msuc2 \<longrightarrow> (\<forall>m' s'. ((A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl (msuc2), Normal ns1'') -n\<rightarrow>* (m', s')) \<longrightarrow>
                                                            is_final_config (m', s') \<longrightarrow> 
                                                            (\<forall>ns_end. s' = Normal ns_end \<longrightarrow> (expr_all_sat A \<Lambda> \<Gamma> \<Omega> ns_end) posts)))) \<Longrightarrow>
        ( (cont_guard = Some block_guard) \<and> 
          (red_expr A \<Lambda> \<Gamma> \<Omega> block_guard ns1'' (BoolV True)) \<and> 
          A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (then0, convert_list_to_cont ( then_bbs) cont0, (Normal ns1'')) -n\<longrightarrow>^k (reached_bb, reached_cont, reached_state) ) \<or> 
        ( (cont_guard = Some block_guard) \<and> 
          (red_expr A \<Lambda> \<Gamma> \<Omega> block_guard ns1'' (BoolV False)) \<and>
          A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (else0, convert_list_to_cont ( else_bbs) cont0, (Normal ns1'')) -n\<longrightarrow>^k (reached_bb, reached_cont, reached_state) ) \<or>
        ( (cont_guard = None) \<and> 
          ((A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (then0, convert_list_to_cont ( then_bbs) cont0, (Normal ns1'')) -n\<longrightarrow>^k (reached_bb, reached_cont, reached_state)) \<or>
           (A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (else0, convert_list_to_cont ( else_bbs) cont0, (Normal ns1'')) -n\<longrightarrow>^k (reached_bb, reached_cont, reached_state)) ) ) \<Longrightarrow>  
        (Ast.valid_configuration A \<Lambda> \<Gamma> \<Omega> posts reached_bb reached_cont reached_state)"
    shows "(Ast.valid_configuration A \<Lambda> \<Gamma> \<Omega> posts reached_bb reached_cont reached_state)" 
    using assms cases
proof cases
  case Rel_Main_test
  have not_end: "(cont0 \<noteq> KStop) \<or> any_str \<noteq> None \<or> any_tr \<noteq> None" using bb_successor_if by simp
  show ?thesis
  proof (cases cs2)
    case Nil hence \<open>cs1 = []\<close> by (simp add: local.Rel_Main_test(2)) 
    thus ?thesis using local.Nil local.Rel_Main_test(2) by auto
  next
    case (Cons) 
    hence "cs1 \<noteq> []" using assms(3) local.Rel_Main_test by auto
    thus ?thesis
    proof (cases j)
      case 0
      hence "(reached_bb, reached_cont, reached_state) = ((BigBlock name cs1 any_str any_tr), cont0, (Normal ns1))" using ast_trace assms(3) by auto
      then show ?thesis by (simp add: Ast.valid_configuration_def bb_successor_if) 
    next
      case 1: (Suc j')
      from this assms(3) obtain inter_bb inter_cont inter_state where
        first_step: "red_bigblock A M \<Lambda> \<Gamma> \<Omega> T ((BigBlock name cs1 any_str any_tr), cont0, (Normal ns1)) (inter_bb, inter_cont, inter_state)" and
        rest_of_steps: "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (inter_bb, inter_cont, inter_state) -n\<longrightarrow>^j' (reached_bb, reached_cont, reached_state)" 
        by (metis ast_trace get_state.cases relpowp_Suc_E2)

      from cfg_correct Cons block_id
      have local_rel_corr: "(\<And> s2'.((red_cmd_list A M \<Lambda> \<Gamma> \<Omega> (cs2) (Normal ns1) s2') \<Longrightarrow> (s2' \<noteq> Failure)))"
        using dag_verifies_propagate_2 
        by (metis push_through_assumption0 push_through_assumption1 \<open>node_to_block(G) ! n = related_block\<close>)

      from local_rel_corr first_step Cons
      have a2: "(inter_state \<noteq> Failure  \<and> (\<forall>ns1'. inter_state = Normal ns1' \<longrightarrow> (A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(node_to_block G ! n), Normal ns1\<rangle> [\<rightarrow>] Normal ns1')))" 
        using block_local_rel local.Rel_Main_test assms(3) 
        by (metis \<open>cs1 \<noteq> []\<close> assume_ml bigblock.inject block_id state.simps(7) \<open>node_to_block(G) ! n = related_block\<close>)

      from first_step Cons \<open>cs1 \<noteq> []\<close>
      have a1: "(inter_bb, inter_cont, inter_state) = ((BigBlock name [] any_str any_tr), cont0, inter_state)"
      proof cases
        case RedSimpleCmds then show ?thesis by (auto simp add: RedSimpleCmds)
      qed auto

      show ?thesis 
      proof (cases inter_state)
        case 2: (Normal x1)
        from rest_of_steps show ?thesis 
        proof (cases j')
          case 0
          then show ?thesis 
            by (metis Ast.valid_configuration_def a1 a2 bb_successor_if get_state.simps is_final.simps(3) relpowp_0_E rest_of_steps) 
        next
          case 3: (Suc j'')
          from this rest_of_steps obtain snd_inter_bb snd_inter_cont snd_inter_state where
            snd_step: "red_bigblock A M \<Lambda> \<Gamma> \<Omega> T ((BigBlock name [] any_str any_tr), cont0, inter_state)  (snd_inter_bb, snd_inter_cont, snd_inter_state)" and
            snd_rest_of_steps: "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (snd_inter_bb, snd_inter_cont, snd_inter_state) -n\<longrightarrow>^j'' (reached_bb, reached_cont, reached_state)"
            by (metis a1 get_state.cases relpowp_Suc_D2)

          thus ?thesis 
          proof (cases cont_guard)
            case None
            from snd_step this show ?thesis
            proof cases
              case RedParsedIfTrue
              hence eq: "(snd_inter_bb, snd_inter_cont, snd_inter_state) = (then0, convert_list_to_cont ( then_bbs) cont0, inter_state)" using None bb_successor_if 1 by auto

              from first_step 
              have succ_cfg_correct: "(\<forall>msuc2.  List.member (out_edges(G) ! n) msuc2 \<longrightarrow> (\<forall>m3 s3. ((A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl(msuc2), inter_state) -n\<rightarrow>* (m3, s3)) \<longrightarrow> s3 \<noteq> Failure)))"
              proof cases
                case RedSimpleCmds show ?thesis using 2 RedSimpleCmds(3) dag_verifies_propagate assms(3-4) Rel_Main_test(1) cfg_correct a2 by blast
              qed (auto simp add: \<open>cs1 \<noteq> Nil\<close>)

              have succ_cfg_sat: "(\<forall>msuc2.  List.member (out_edges(G) ! n) msuc2 \<longrightarrow> (\<forall>m' s'. ((A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl (msuc2), inter_state) -n\<rightarrow>* (m', s')) \<longrightarrow>
                                                        is_final_config (m', s') \<longrightarrow> 
                                                        (\<forall>ns_end. s' = Normal ns_end \<longrightarrow> (expr_all_sat A \<Lambda> \<Gamma> \<Omega> ns_end) posts))))"
                using cfg_satisfies_post cfg_correct local.Cons
                by (metis (no_types) "2" RedNormalSucc a2 converse_rtranclp_into_rtranclp)

              have "j'' < j" using 1 3 using Suc_lessD by blast

              thus ?thesis using eq snd_rest_of_steps succ_correct None 2 succ_cfg_correct succ_cfg_sat by blast
            next
              case (RedParsedIfFalse)
              hence eq: "(snd_inter_bb, snd_inter_cont, snd_inter_state) = (else0, convert_list_to_cont ( else_bbs) cont0, inter_state)" using None bb_successor_if 1 by auto

              from first_step 
              have succ_cfg_correct: "(\<forall>msuc2.  List.member (out_edges(G) ! n) msuc2 \<longrightarrow> (\<forall>m3 s3. ((A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl(msuc2), inter_state) -n\<rightarrow>* (m3, s3)) \<longrightarrow> s3 \<noteq> Failure)))"
              proof cases
                case RedSimpleCmds show ?thesis using 2 RedSimpleCmds(3) dag_verifies_propagate assms(3-4) Rel_Main_test(1) cfg_correct a2 by blast
              qed (auto simp add: \<open>cs1 \<noteq> Nil\<close>)

              have succ_cfg_sat: "(\<forall>msuc2.  List.member (out_edges(G) ! n) msuc2 \<longrightarrow> (\<forall>m' s'. ((A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl (msuc2), inter_state) -n\<rightarrow>* (m', s')) \<longrightarrow>
                                                        is_final_config (m', s') \<longrightarrow> 
                                                        (\<forall>ns_end. s' = Normal ns_end \<longrightarrow> (expr_all_sat A \<Lambda> \<Gamma> \<Omega> ns_end) posts))))"
                using cfg_satisfies_post cfg_correct local.Cons
                by (metis (no_types) "2" RedNormalSucc a2 converse_rtranclp_into_rtranclp)

              have "j'' < j" using 1 3 using Suc_lessD by blast

              thus ?thesis using eq snd_rest_of_steps succ_correct None 2 succ_cfg_correct succ_cfg_sat by blast
            qed (auto simp add: bb_successor_if 2)
          next
            case (Some block_guard)
            then show ?thesis 
            proof cases
              assume guard_true: "(red_expr A \<Lambda> \<Gamma> \<Omega> block_guard x1 (BoolV True))"
              hence guard_not_false: "\<not> (red_expr A \<Lambda> \<Gamma> \<Omega> block_guard x1 (BoolV False))" using expr_eval_determ by blast
              from snd_step have eq: "(snd_inter_bb, snd_inter_cont, snd_inter_state) = (then0, convert_list_to_cont ( then_bbs) cont0, inter_state)" 
              proof cases
                case RedParsedIfTrue thus ?thesis using guard_true bb_successor_if by (simp add: RedParsedIfTrue)
              qed (auto simp add: guard_not_false bb_successor_if 2 Some)

              from first_step 
              have succ_cfg_correct: "(\<forall>msuc2.  List.member (out_edges(G) ! n) msuc2 \<longrightarrow> (\<forall>m3 s3. ((A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl(msuc2), inter_state) -n\<rightarrow>* (m3, s3)) \<longrightarrow> s3 \<noteq> Failure)))"
              proof cases
                case RedSimpleCmds show ?thesis using 2 eq RedSimpleCmds(3) dag_verifies_propagate assms(3-4) Rel_Main_test(1) cfg_correct a2 by blast
              qed (auto simp add: \<open>cs1 \<noteq> Nil\<close>)

              have succ_cfg_sat: "(\<forall>msuc2.  List.member (out_edges(G) ! n) msuc2 \<longrightarrow> (\<forall>m' s'. ((A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl (msuc2), inter_state) -n\<rightarrow>* (m', s')) \<longrightarrow>
                                                        is_final_config (m', s') \<longrightarrow> 
                                                        (\<forall>ns_end. s' = Normal ns_end \<longrightarrow> (expr_all_sat A \<Lambda> \<Gamma> \<Omega> ns_end) posts))))"
                using cfg_satisfies_post cfg_correct local.Cons
                by (metis (no_types) "2" RedNormalSucc a2 converse_rtranclp_into_rtranclp)

              have "j'' < j" using 1 3 using Suc_lessD by blast

              thus ?thesis using eq guard_true snd_rest_of_steps succ_correct Some succ_cfg_correct 2 succ_cfg_sat by blast
            next
              assume guard_not_true: "\<not> (red_expr A \<Lambda> \<Gamma> \<Omega> block_guard x1 (BoolV True))"
              thus ?thesis 
              proof cases
                assume guard_false: "(red_expr A \<Lambda> \<Gamma> \<Omega> block_guard x1 (BoolV False))"
                from snd_step have eq: "(snd_inter_bb, snd_inter_cont, snd_inter_state) = (else0, convert_list_to_cont ( else_bbs) cont0, inter_state)"
                proof cases
                  case RedParsedIfFalse thus ?thesis using guard_false bb_successor_if by (simp add: RedParsedIfFalse)
                qed (auto simp add: guard_not_true bb_successor_if 2 Some)

                from first_step 
                have succ_cfg_correct: "(\<forall>msuc2.  List.member (out_edges(G) ! n) msuc2 \<longrightarrow> (\<forall>m3 s3. ((A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl(msuc2), inter_state) -n\<rightarrow>* (m3, s3)) \<longrightarrow> s3 \<noteq> Failure)))"
                proof cases
                  case RedSimpleCmds show ?thesis using 2 RedSimpleCmds(3) dag_verifies_propagate assms(3-4) Rel_Main_test(1) cfg_correct a2 by blast
                qed (auto simp add: \<open>cs1 \<noteq> Nil\<close>)

                have succ_cfg_sat: "(\<forall>msuc2.  List.member (out_edges(G) ! n) msuc2 \<longrightarrow> (\<forall>m' s'. ((A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl (msuc2), inter_state) -n\<rightarrow>* (m', s')) \<longrightarrow>
                                                          is_final_config (m', s') \<longrightarrow> 
                                                          (\<forall>ns_end. s' = Normal ns_end \<longrightarrow> (expr_all_sat A \<Lambda> \<Gamma> \<Omega> ns_end) posts))))"
                  using cfg_satisfies_post cfg_correct local.Cons
                  by (metis (no_types) "2" RedNormalSucc a2 converse_rtranclp_into_rtranclp)

                have "j'' < j" using 1 3 using Suc_lessD by blast

                thus ?thesis using eq guard_false snd_rest_of_steps succ_correct Some 2 succ_cfg_correct succ_cfg_sat by blast
              next
                assume guard_not_false2: "(\<not> (red_expr A \<Lambda> \<Gamma> \<Omega> block_guard x1 (BoolV False)))" and  
                  guard_not_true2: "(\<not> (red_expr A \<Lambda> \<Gamma> \<Omega> block_guard x1 (BoolV True)))"
                thus ?thesis
                proof -
                  from snd_step have False using guard_not_false2 guard_not_true2 bb_successor_if Some 2 
                    by (cases) auto
                  thus ?thesis by simp
                qed
              qed  
            qed 
          qed
        qed
      next
        case Failure
        then show ?thesis
          using \<open>inter_state \<noteq> Failure \<and> (\<forall>ns1'. inter_state = Normal ns1' \<longrightarrow> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(node_to_block G ! n),Normal ns1\<rangle> [\<rightarrow>] Normal ns1')\<close> 
          by linarith
      next
        case Magic
        then show ?thesis by (metis Ast.valid_configuration_def a2 magic_propagates rest_of_steps state.distinct(3))
      qed
    qed
  qed
next
  case Rel_Invs
  hence "cs2 = []" by simp
  have not_end: "(cont0 \<noteq> KStop) \<or> any_str \<noteq> None \<or> any_tr \<noteq> None" using bb_successor_if by simp
  show ?thesis
  proof (cases cs2)
    case Nil 
    thus ?thesis
    proof (cases j)
      case 0
      hence "(reached_bb, reached_cont, reached_state) = ((BigBlock name cs1 any_str any_tr), cont0, (Normal ns1))" using ast_trace assms(3) by auto
      then show ?thesis by (simp add: Ast.valid_configuration_def bb_successor_if) 
    next
      case 1: (Suc j')
      from this assms(3) obtain snd_inter_bb snd_inter_cont snd_inter_state where
        snd_step: "red_bigblock A M \<Lambda> \<Gamma> \<Omega> T ((BigBlock name [] any_str any_tr), cont0, (Normal ns1))  (snd_inter_bb, snd_inter_cont, snd_inter_state)" and
        snd_rest_of_steps: "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (snd_inter_bb, snd_inter_cont, snd_inter_state) -n\<longrightarrow>^j' (reached_bb, reached_cont, reached_state)" 
        using Rel_Invs
        by (metis ast_trace bigblock.inject local.Rel_Invs(1) relpowp_Suc_E2 surj_pair)

      thus ?thesis 
      proof (cases cont_guard)
        case None
        from snd_step this show ?thesis
        proof cases
          case RedParsedIfTrue
          hence eq: "(snd_inter_bb, snd_inter_cont, snd_inter_state) = (then0, convert_list_to_cont ( then_bbs) cont0, (Normal ns1))" using None bb_successor_if 1 by auto

          have succ_cfg_correct: "(\<forall>msuc2.  List.member (out_edges(G) ! n) msuc2 \<longrightarrow> (\<forall>m3 s3. ((A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl(msuc2), (Normal ns1)) -n\<rightarrow>* (m3, s3)) \<longrightarrow> s3 \<noteq> Failure)))"
            using assms(5) cfg_correct correctness_propagates_through_empty local.Nil \<open>node_to_block(G) ! n = related_block\<close>
            by (metis (full_types) correctness_propagates_through_assumption correctness_propagates_through_assumption2)

          have succ_cfg_sat: "\<And>msuc2 m' s' ns_end.  List.member (out_edges(G) ! n) msuc2 \<Longrightarrow> (A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl (msuc2), Normal ns1) -n\<rightarrow>* (m', s')) \<Longrightarrow>
                                                      is_final_config (m', s') \<Longrightarrow> 
                                                      (s' = Normal ns_end) \<longrightarrow> (expr_all_sat A \<Lambda> \<Gamma> \<Omega> ns_end) posts"
          proof
            fix msuc2 m' s' ns_end
            assume a: "List.member (out_edges G ! n) msuc2" and
              b: "A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl msuc2, Normal ns1) -n\<rightarrow>* (m', s')" and
              c: "is_final_config (m', s')" and 
              d: "(s' = Normal ns_end)"
            have one_block_advance: "A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl n, Normal ns1) -n\<rightarrow> (Inl msuc2, Normal ns1)" 
              using local.Nil \<open>node_to_block(G) ! n = related_block\<close> assms(5) 
                a b c
              by (metis RedCmdListNil RedNormalSucc push_through_assumption0 push_through_assumption1)  
            show "(expr_all_sat A \<Lambda> \<Gamma> \<Omega> ns_end) posts" using cfg_satisfies_post b c a succ_cfg_correct one_block_advance 
              by (meson converse_rtranclp_into_rtranclp d) 
          qed  
          have "j' < j" using 1 using Suc_lessD by blast
          thus ?thesis using eq snd_rest_of_steps succ_correct None succ_cfg_correct succ_cfg_sat by blast
        next
          case (RedParsedIfFalse)
          hence eq: "(snd_inter_bb, snd_inter_cont, snd_inter_state) = (else0, convert_list_to_cont ( else_bbs) cont0, Normal ns1)" using None bb_successor_if 1 by auto

          from snd_step 
          have succ_cfg_correct: "(\<forall>msuc2.  List.member (out_edges(G) ! n) msuc2 \<longrightarrow> (\<forall>m3 s3. ((A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl(msuc2), (Normal ns1)) -n\<rightarrow>* (m3, s3)) \<longrightarrow> s3 \<noteq> Failure)))"
            using assms(5) cfg_correct correctness_propagates_through_empty local.Nil \<open>node_to_block(G) ! n = related_block\<close>
            by (metis (full_types) correctness_propagates_through_assumption correctness_propagates_through_assumption2)

          have succ_cfg_sat: "\<And>msuc2 m' s' ns_end.  List.member (out_edges(G) ! n) msuc2 \<Longrightarrow> (A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl (msuc2), Normal ns1) -n\<rightarrow>* (m', s')) \<Longrightarrow>
                                                      is_final_config (m', s') \<Longrightarrow> 
                                                      (s' = Normal ns_end) \<longrightarrow> (expr_all_sat A \<Lambda> \<Gamma> \<Omega> ns_end) posts"
          proof
            fix msuc2 m' s' ns_end
            assume a: "List.member (out_edges G ! n) msuc2" and
              b: "A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl msuc2, Normal ns1) -n\<rightarrow>* (m', s')" and
              c: "is_final_config (m', s')" and 
              d: "(s' = Normal ns_end)"
            have one_block_advance: "A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl n, Normal ns1) -n\<rightarrow> (Inl msuc2, Normal ns1)" 
              using local.Nil \<open>node_to_block(G) ! n = related_block\<close> assms(5) 
                a b c
              by (metis RedCmdListNil RedNormalSucc push_through_assumption0 push_through_assumption1)  
            show "(expr_all_sat A \<Lambda> \<Gamma> \<Omega> ns_end) posts" using cfg_satisfies_post b c a succ_cfg_correct one_block_advance 
              by (meson converse_rtranclp_into_rtranclp d) 
          qed

          have "j' < j" using 1 using Suc_lessD by blast

          thus ?thesis using eq snd_rest_of_steps succ_correct None succ_cfg_correct succ_cfg_sat by blast
        qed (auto simp add: bb_successor_if)
      next
        case (Some block_guard)
        then show ?thesis 
        proof cases
          assume guard_true: "(red_expr A \<Lambda> \<Gamma> \<Omega> block_guard ns1 (BoolV True))"
          hence guard_not_false: "\<not> (red_expr A \<Lambda> \<Gamma> \<Omega> block_guard ns1 (BoolV False))" using expr_eval_determ by blast
          from snd_step have eq: "(snd_inter_bb, snd_inter_cont, snd_inter_state) = (then0, convert_list_to_cont ( then_bbs) cont0, Normal ns1)" 
          proof cases
            case RedParsedIfTrue thus ?thesis using guard_true bb_successor_if by (simp add: RedParsedIfTrue)
          qed (auto simp add: guard_not_false bb_successor_if Some)

          from snd_step 
          have succ_cfg_correct: "(\<forall>msuc2.  List.member (out_edges(G) ! n) msuc2 \<longrightarrow> (\<forall>m3 s3. ((A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl(msuc2), Normal ns1) -n\<rightarrow>* (m3, s3)) \<longrightarrow> s3 \<noteq> Failure)))"
            using assms(5) cfg_correct correctness_propagates_through_empty local.Nil \<open>node_to_block(G) ! n = related_block\<close>
            by (metis (full_types) correctness_propagates_through_assumption correctness_propagates_through_assumption2)

          have succ_cfg_sat: "\<And>msuc2 m' s' ns_end.  List.member (out_edges(G) ! n) msuc2 \<Longrightarrow> (A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl (msuc2), Normal ns1) -n\<rightarrow>* (m', s')) \<Longrightarrow>
                                                      is_final_config (m', s') \<Longrightarrow> 
                                                      (s' = Normal ns_end) \<longrightarrow> (expr_all_sat A \<Lambda> \<Gamma> \<Omega> ns_end) posts"
          proof
            fix msuc2 m' s' ns_end
            assume a: "List.member (out_edges G ! n) msuc2" and
              b: "A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl msuc2, Normal ns1) -n\<rightarrow>* (m', s')" and
              c: "is_final_config (m', s')" and 
              d: "(s' = Normal ns_end)"
            have one_block_advance: "A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl n, Normal ns1) -n\<rightarrow> (Inl msuc2, Normal ns1)" 
              using local.Nil \<open>node_to_block(G) ! n = related_block\<close> assms(5) 
                a b c
              by (metis RedCmdListNil RedNormalSucc push_through_assumption0 push_through_assumption1)  
            show "(expr_all_sat A \<Lambda> \<Gamma> \<Omega> ns_end) posts" using cfg_satisfies_post b c a succ_cfg_correct one_block_advance 
              by (meson converse_rtranclp_into_rtranclp d) 
          qed

          have "j' < j" using 1 using Suc_lessD by blast

          thus ?thesis using eq guard_true snd_rest_of_steps succ_correct Some succ_cfg_correct succ_cfg_sat by blast
        next
          assume guard_not_true: "\<not> (red_expr A \<Lambda> \<Gamma> \<Omega> block_guard ns1 (BoolV True))"
          thus ?thesis 
          proof cases
            assume guard_false: "(red_expr A \<Lambda> \<Gamma> \<Omega> block_guard ns1 (BoolV False))"
            from snd_step have eq: "(snd_inter_bb, snd_inter_cont, snd_inter_state) = (else0, convert_list_to_cont ( else_bbs) cont0, Normal ns1)"
            proof cases
              case RedParsedIfFalse thus ?thesis using guard_false bb_successor_if by (simp add: RedParsedIfFalse)
            qed (auto simp add: guard_not_true bb_successor_if Some)

            from snd_step 
            have succ_cfg_correct: "(\<forall>msuc2.  List.member (out_edges(G) ! n) msuc2 \<longrightarrow> (\<forall>m3 s3. ((A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl(msuc2), Normal ns1) -n\<rightarrow>* (m3, s3)) \<longrightarrow> s3 \<noteq> Failure)))"
              using assms(5) cfg_correct correctness_propagates_through_empty local.Nil \<open>node_to_block(G) ! n = related_block\<close>
              by (metis (full_types) correctness_propagates_through_assumption correctness_propagates_through_assumption2) 

            have succ_cfg_sat: "\<And>msuc2 m' s' ns_end.  List.member (out_edges(G) ! n) msuc2 \<Longrightarrow> (A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl (msuc2), Normal ns1) -n\<rightarrow>* (m', s')) \<Longrightarrow>
                                                      is_final_config (m', s') \<Longrightarrow> 
                                                      (s' = Normal ns_end) \<longrightarrow> (expr_all_sat A \<Lambda> \<Gamma> \<Omega> ns_end) posts"
            proof
              fix msuc2 m' s' ns_end
              assume a: "List.member (out_edges G ! n) msuc2" and
                b: "A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl msuc2, Normal ns1) -n\<rightarrow>* (m', s')" and
                c: "is_final_config (m', s')" and 
                d: "(s' = Normal ns_end)"
              have one_block_advance: "A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl n, Normal ns1) -n\<rightarrow> (Inl msuc2, Normal ns1)" 
                using local.Nil \<open>node_to_block(G) ! n = related_block\<close> assms(5) 
                  a b c
                by (metis RedCmdListNil RedNormalSucc push_through_assumption0 push_through_assumption1)  
              show "(expr_all_sat A \<Lambda> \<Gamma> \<Omega> ns_end) posts" using cfg_satisfies_post b c a succ_cfg_correct one_block_advance 
                by (meson converse_rtranclp_into_rtranclp d) 
            qed

            have "j' < j" using 1 using Suc_lessD by blast

            thus ?thesis using eq guard_false snd_rest_of_steps succ_correct Some succ_cfg_correct succ_cfg_sat by blast
          next
            assume guard_not_false2: "(\<not> (red_expr A \<Lambda> \<Gamma> \<Omega> block_guard ns1 (BoolV False)))" and  
              guard_not_true2: "(\<not> (red_expr A \<Lambda> \<Gamma> \<Omega> block_guard ns1 (BoolV True)))"
            thus ?thesis
            proof -
              from snd_step have False using guard_not_false2 guard_not_true2 bb_successor_if Some 
                by (cases) auto
              thus ?thesis by simp
            qed
          qed  
        qed 
      qed
    qed
  next
    case Cons
    thus ?thesis using \<open>cs2 = []\<close> by simp
  qed
qed

text \<open>Global lemma for a generic big block. This means that neither a loop, nor an if-statement is entered after its simple commands are executed.\<close>
lemma block_global_rel_generic:
  assumes block_rel: "ast_cfg_rel None [] bb cs2"
      and ast_trace: "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (bb, cont0, (Normal ns1)) -n\<longrightarrow>^j (reached_bb, reached_cont, reached_state)"
      and "bb = (BigBlock name cs1 any_str any_tr)"
      and node_to_block_assm: "node_to_block(G) ! n = related_block"
      and block_id:
    "(related_block = cs2) \<or> 
       (related_block = c#cs2) \<and> c = Assume guard \<and> (red_expr A \<Lambda> \<Gamma> \<Omega> guard ns1 (BoolV True)) \<or> 
       (related_block = c#cs2) \<and> c = Assume not_guard \<and> (UnOp Not guard \<sim> not_guard) \<and> (red_expr A \<Lambda> \<Gamma> \<Omega> guard ns1 (BoolV False))"
      and cfg_correct: "(\<And> m2 s2. ((red_cfg_multi A M \<Lambda> \<Gamma> \<Omega> G (Inl n, Normal ns1) (m2, s2)) \<Longrightarrow> (s2 \<noteq> Failure)))"
      and cfg_satisfies_post: "(\<And> m2 s2. (red_cfg_multi A M \<Lambda> \<Gamma> \<Omega> G (Inl n, Normal ns1) (m2, s2)) \<Longrightarrow>
                                        is_final_config (m2, s2) \<Longrightarrow> \<forall>ns_end. s2 = Normal ns_end \<longrightarrow> expr_all_sat A \<Lambda> \<Gamma> \<Omega> ns_end posts)"
      and trivial_bb_successor: "(cont0 = KSeq bb1 cont1) \<and> any_str = None \<and> any_tr = None"
      and block_local_rel: 
        "\<And> reached_bb_inter reached_cont_inter reached_state_inter. 
          (red_bigblock A M \<Lambda> \<Gamma> \<Omega> T (bb, cont0, (Normal ns1)) (reached_bb_inter, reached_cont_inter, reached_state_inter)) \<Longrightarrow> 
          (\<And> s2'.((red_cmd_list A M \<Lambda> \<Gamma> \<Omega> (node_to_block(G) ! n) (Normal ns1) s2') \<Longrightarrow> (s2' \<noteq> Failure))) \<Longrightarrow>   
           cs1 \<noteq> [] \<Longrightarrow> 
           cs2 \<noteq> [] \<Longrightarrow>
          reached_state_inter \<noteq> Failure \<and> 
          (\<forall>ns1'. reached_state_inter = Normal ns1' \<longrightarrow> (A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(node_to_block(G) ! n), Normal ns1\<rangle> [\<rightarrow>] Normal ns1'))"
      and succ_correct: 
    "\<And>  ns1'' k.
        k < j \<Longrightarrow> 
        \<forall>msuc2.  List.member (out_edges(G) ! n) msuc2 \<longrightarrow> (\<forall>m3 s3. ((A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl(msuc2), Normal ns1'') -n\<rightarrow>* (m3, s3)) \<longrightarrow> s3 \<noteq> Failure)) \<Longrightarrow>
        \<forall>msuc2.  List.member (out_edges(G) ! n) msuc2 \<longrightarrow> (\<forall>m' s'. ((A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl (msuc2), Normal ns1'') -n\<rightarrow>* (m', s')) \<longrightarrow>
                                                            is_final_config (m', s') \<longrightarrow> 
                                                            (\<forall>ns_end. s' = Normal ns_end \<longrightarrow> expr_all_sat A \<Lambda> \<Gamma> \<Omega> ns_end posts))) \<Longrightarrow>
        A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (bb1, cont1, (Normal ns1'')) -n\<longrightarrow>^k (reached_bb, reached_cont, reached_state) \<Longrightarrow> 
        (Ast.valid_configuration A \<Lambda> \<Gamma> \<Omega> posts reached_bb reached_cont reached_state)"
    shows "(Ast.valid_configuration A \<Lambda> \<Gamma> \<Omega> posts reached_bb reached_cont reached_state)" 
  using assms cases
proof cases
  case Rel_Main_test
  have not_end: "(cont0 \<noteq> KStop) \<or> any_str \<noteq> None \<or> any_tr \<noteq> None" using trivial_bb_successor by simp
  from ast_trace show ?thesis
  proof (cases cs2)
    case Nil hence \<open>cs1 = []\<close> by (simp add: local.Rel_Main_test(2))
    thus ?thesis using local.Nil local.Rel_Main_test(2) by blast
  next
    case (Cons)
    hence "cs1 \<noteq> Nil" using assms(3) local.Rel_Main_test by blast
    from ast_trace this show ?thesis
    proof (cases j)
      case 0
      hence "(reached_bb, reached_cont, reached_state) = ((BigBlock name cs1 any_str any_tr), cont0, (Normal ns1))" using ast_trace assms(3) by auto
      then show ?thesis unfolding Ast.valid_configuration_def by (simp add: trivial_bb_successor)
    next
      case succ_0: (Suc j')
      from this assms(3) obtain inter_bb inter_cont inter_state where
        first_step: "red_bigblock A M \<Lambda> \<Gamma> \<Omega> T ((BigBlock name cs1 any_str any_tr), cont0, (Normal ns1)) (inter_bb, inter_cont, inter_state)" and
        rest_of_steps: "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (inter_bb, inter_cont, inter_state) -n\<longrightarrow>^j' (reached_bb, reached_cont, reached_state)"
        by (metis ast_trace get_state.cases relpowp_Suc_D2)

      from cfg_correct Cons block_id node_to_block_assm
      have local_rel_corr: "(\<And> s2'.((red_cmd_list A M \<Lambda> \<Gamma> \<Omega> cs2 (Normal ns1) s2') \<Longrightarrow> (s2' \<noteq> Failure)))"
        apply (simp)
        apply (rule disjE)
        apply simp
        apply (rule dag_verifies_propagate_2)
        apply blast
        apply assumption
        apply simp
        apply (rule disjE)
        apply simp
        apply (metis dag_verifies_propagate_2 push_through_assumption0)
        apply (metis dag_verifies_propagate_2 push_through_assumption1)
        done

      from local_rel_corr first_step 
      have a2: "(inter_state \<noteq> Failure  \<and> (\<forall>ns1'. inter_state = Normal ns1' \<longrightarrow> (A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(node_to_block G ! n), Normal ns1\<rangle> [\<rightarrow>] Normal ns1')))" 
        using block_local_rel assms(3) \<open>cs1 \<noteq> []\<close> Cons 
        by (metis bigblock.inject cfg_correct dag_verifies_propagate_2 local.Rel_Main_test(1))

      from first_step \<open>cs1 \<noteq> Nil\<close> 
      have a1: "(inter_bb, inter_cont, inter_state) = ((BigBlock name [] any_str any_tr), cont0, inter_state)"
      proof cases
        case RedSimpleCmds then show ?thesis by (auto simp add: RedSimpleCmds)
      qed auto

      show ?thesis 
      proof (cases inter_state)
        case 1: (Normal x1)
        from rest_of_steps show ?thesis 
        proof (cases j')
          case 0
          then show ?thesis 
            by (metis valid_configuration_def a1 a2 get_state.simps is_final.simps(5) relpowp_0_E rest_of_steps trivial_bb_successor)
        next
          case 2: (Suc j'')
          from this rest_of_steps obtain snd_inter_bb snd_inter_cont snd_inter_state where
            snd_step: "red_bigblock A M \<Lambda> \<Gamma> \<Omega> T ((BigBlock name [] any_str any_tr), cont0, inter_state)  (snd_inter_bb, snd_inter_cont, snd_inter_state)" and
            snd_rest_of_steps: "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (snd_inter_bb, snd_inter_cont, snd_inter_state) -n\<longrightarrow>^j'' (reached_bb, reached_cont, reached_state)"
            by (metis a1 get_state.cases relpowp_Suc_D2)

          from snd_step have snd_step_equiv: "(snd_inter_bb, snd_inter_cont, snd_inter_state) = (bb1, cont1, inter_state)"
          proof cases
            case RedSkip thus ?thesis using trivial_bb_successor by (simp add: RedSkip)
          qed (auto simp add: trivial_bb_successor "1")

          from first_step 
          have succ_cfg_correct: "(\<forall>msuc2.  List.member (out_edges(G) ! n) msuc2 \<longrightarrow> (\<forall>m3 s3. ((A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl(msuc2), inter_state) -n\<rightarrow>* (m3, s3)) \<longrightarrow> s3 \<noteq> Failure)))"
          proof cases
            case RedSimpleCmds show ?thesis 
              using 1 snd_step_equiv  RedSimpleCmds(3) dag_verifies_propagate Rel_Main_test(1) cfg_correct assms(3-5) a2 
              by blast
          qed (auto simp add: \<open>cs1 \<noteq> Nil\<close>) 

          have succ_cfg_sat: "(\<forall>msuc2.  List.member (out_edges(G) ! n) msuc2 \<longrightarrow> (\<forall>m' s'. ((A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl (msuc2), inter_state) -n\<rightarrow>* (m', s')) \<longrightarrow>
                                                    is_final_config (m', s') \<longrightarrow> 
                                                    (\<forall>ns_end. s' = Normal ns_end \<longrightarrow> expr_all_sat A \<Lambda> \<Gamma> \<Omega> ns_end posts))))"
            using cfg_satisfies_post cfg_correct local.Cons
            by (metis (no_types) "1" RedNormalSucc a2 converse_rtranclp_into_rtranclp)

          have "j'' < j" using succ_0 2 by simp

          then show ?thesis using expr_all_sat_def snd_step_equiv succ_correct snd_rest_of_steps "1" succ_cfg_correct succ_cfg_sat by auto
        qed
      next
        case Failure
        then show ?thesis
          using \<open>inter_state \<noteq> Failure \<and> (\<forall>ns1'. inter_state = Normal ns1' \<longrightarrow> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>node_to_block(G) ! n,Normal ns1\<rangle> [\<rightarrow>] Normal ns1')\<close> 
          by linarith
      next
        case Magic
        then show ?thesis by (metis valid_configuration_def a2  magic_propagates rest_of_steps state.distinct(3))
      qed
    qed 
  qed
next
  case Rel_Invs
  have not_end: "(cont0 \<noteq> KStop) \<or> any_str \<noteq> None \<or> any_tr \<noteq> None" using trivial_bb_successor by simp
  from ast_trace show ?thesis
  proof (cases cs2)
    case Nil
    thus ?thesis
    proof (cases j)
      case 0
      hence "(reached_bb, reached_cont, reached_state) = ((BigBlock name cs1 any_str any_tr), cont0, (Normal ns1))" using ast_trace assms(3) by auto
      then show ?thesis by (simp add: Ast.valid_configuration_def trivial_bb_successor) 
    next
      case 1: (Suc j')
      from this assms(3) obtain snd_inter_bb snd_inter_cont snd_inter_state where
        snd_step: "red_bigblock A M \<Lambda> \<Gamma> \<Omega> T ((BigBlock name [] any_str any_tr), cont0, (Normal ns1))  (snd_inter_bb, snd_inter_cont, snd_inter_state)" and
        snd_rest_of_steps: "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (snd_inter_bb, snd_inter_cont, snd_inter_state) -n\<longrightarrow>^j' (reached_bb, reached_cont, reached_state)"
        by (metis ast_trace bigblock.inject local.Nil local.Rel_Invs relpowp_Suc_E2 surj_pair)

      hence eq: "(snd_inter_bb, snd_inter_cont, snd_inter_state) = (bb1,  cont1, (Normal ns1))" using trivial_bb_successor 1 
        by (cases) auto 

      have succ_cfg_correct: "(\<forall>msuc2.  List.member (out_edges(G) ! n) msuc2 \<longrightarrow> (\<forall>m3 s3. ((A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl(msuc2), (Normal ns1)) -n\<rightarrow>* (m3, s3)) \<longrightarrow> s3 \<noteq> Failure)))"
        using assms(4-5) cfg_correct correctness_propagates_through_empty local.Nil
        by (metis (no_types) correctness_propagates_through_assumption correctness_propagates_through_assumption2)

      have succ_cfg_sat: "\<And>msuc2 m' s' ns_end.  List.member (out_edges(G) ! n) msuc2 \<Longrightarrow> (A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl (msuc2), Normal ns1) -n\<rightarrow>* (m', s')) \<Longrightarrow>
                                                  is_final_config (m', s') \<Longrightarrow> 
                                                  (s' = Normal ns_end) \<longrightarrow> (expr_all_sat A \<Lambda> \<Gamma> \<Omega> ns_end) posts"
      proof
        fix msuc2 m' s' ns_end
        assume a: "List.member (out_edges G ! n) msuc2" and
          b: "A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl msuc2, Normal ns1) -n\<rightarrow>* (m', s')" and
          c: "is_final_config (m', s')" and 
          d: "(s' = Normal ns_end)"
        have one_block_advance: "A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl n, Normal ns1) -n\<rightarrow> (Inl msuc2, Normal ns1)" 
          using local.Nil \<open>node_to_block(G) ! n = related_block\<close> assms(5) 
            a b c
          by (metis RedCmdListNil RedNormalSucc push_through_assumption0 push_through_assumption1)  
        show "(expr_all_sat A \<Lambda> \<Gamma> \<Omega> ns_end) posts" using cfg_satisfies_post b c a succ_cfg_correct one_block_advance 
          by (meson converse_rtranclp_into_rtranclp d) 
      qed

      have "j' < j" using 1 using Suc_lessD by blast

      thus ?thesis using eq snd_rest_of_steps succ_correct succ_cfg_correct succ_cfg_sat by blast
    qed
  next
    case (Cons)
    hence "cs1 \<noteq> Nil" using assms(3) local.Rel_Invs by blast
    from ast_trace this show ?thesis
      using local.Cons local.Rel_Invs(1) by fastforce
  qed
qed

definition loop_IH 
  where "loop_IH j A M \<Lambda> \<Gamma> \<Omega> T bb0 cont0 G block_index posts reached_bb reached_cont reached_state \<equiv> 
          (\<forall>k ns1. k < j \<longrightarrow>
                    (A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile>(bb0, cont0, Normal ns1) -n\<longrightarrow>^k (reached_bb, reached_cont, reached_state)) \<longrightarrow>
                    (\<forall>m' s'. (red_cfg_multi A M \<Lambda> \<Gamma> \<Omega> G ((Inl block_index),(Normal ns1)) (m',s')) \<longrightarrow> (s' \<noteq> Failure)) \<longrightarrow>
                    (\<forall>m' s'.  (A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl block_index, Normal ns1) -n\<rightarrow>* (m', s')) \<longrightarrow>
                               is_final_config (m', s') \<longrightarrow> (\<forall>ns_end. s' = Normal ns_end \<longrightarrow> (expr_all_sat A \<Lambda> \<Gamma> \<Omega> ns_end) posts)) \<longrightarrow>
                    (Ast.valid_configuration A \<Lambda> \<Gamma> \<Omega> posts reached_bb reached_cont reached_state))"

lemma loop_IH_prove:
  assumes "\<And> k ns1. k < j \<Longrightarrow>
                    (A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile>(bb0, cont0, Normal ns1) -n\<longrightarrow>^k (reached_bb, reached_cont, reached_state)) \<Longrightarrow>
                    (\<forall>m' s'. (red_cfg_multi A M \<Lambda> \<Gamma> \<Omega> G ((Inl block_index),(Normal ns1)) (m',s')) \<longrightarrow> (s' \<noteq> Failure)) \<Longrightarrow>
                    (\<forall>m' s'.  (A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl block_index, Normal ns1) -n\<rightarrow>* (m', s')) \<longrightarrow>
                               is_final_config (m', s') \<longrightarrow> (\<forall>ns_end. s' = Normal ns_end \<longrightarrow> (expr_all_sat A \<Lambda> \<Gamma> \<Omega> ns_end) posts)) \<Longrightarrow>
                    (Ast.valid_configuration A \<Lambda> \<Gamma> \<Omega> posts reached_bb reached_cont reached_state)"
  shows "loop_IH j A M \<Lambda> \<Gamma> \<Omega> T bb0 cont0 G block_index posts reached_bb reached_cont reached_state"
  using assms
  unfolding loop_IH_def
  by blast

lemma loop_IH_apply:
  assumes "loop_IH j A M \<Lambda> \<Gamma> \<Omega> T bb0 cont0 G block_index posts reached_bb reached_cont reached_state"
      and "k < j"
      and "(A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile>(bb0, cont0, Normal ns1) -n\<longrightarrow>^k (reached_bb, reached_cont, reached_state))"
      and "(\<forall>m' s'. (red_cfg_multi A M \<Lambda> \<Gamma> \<Omega> G ((Inl block_index),(Normal ns1)) (m',s')) \<longrightarrow> (s' \<noteq> Failure))"
      and "(\<forall>m' s'.  (A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl block_index, Normal ns1) -n\<rightarrow>* (m', s')) \<longrightarrow>
                               is_final_config (m', s') \<longrightarrow> (\<forall>ns_end. s' = Normal ns_end \<longrightarrow> (expr_all_sat A \<Lambda> \<Gamma> \<Omega> ns_end posts)))"
    shows "(Ast.valid_configuration A \<Lambda> \<Gamma> \<Omega> posts reached_bb reached_cont reached_state)"
  using assms
  unfolding loop_IH_def 
  by blast

subsection \<open>Procedure correctness\<close>

text \<open>The main lemma used to complete proof of the correctness of an \<^term>\<open>ast_procedure\<close>.\<close>
lemma end_to_end_util2:
  assumes AExpanded: "\<And> \<Gamma> end_bb end_cont end_state ns (M::mbodyCFG proc_context).
           rtranclp (red_bigblock B M \<Lambda> \<Gamma> [] ast) (init_ast ast ns) (end_bb, end_cont, end_state) \<Longrightarrow>
           (\<And> v. (closed ((type_of_val B) v))) \<Longrightarrow>
           (\<And> t. ((closed t) \<Longrightarrow> (\<exists> v. (((type_of_val B) v) = t)))) \<Longrightarrow>
           (fun_interp_wf B fun_decls \<Gamma>) \<Longrightarrow>
           (axiom_assm B \<Gamma> constants (ns::(('a)nstate)) axioms) \<Longrightarrow>
           (expr_all_sat B \<Lambda> \<Gamma> [] ns all_pres) \<Longrightarrow>
           (state_typ_wf B [] (local_state ns) (snd \<Lambda>)) \<Longrightarrow>
           (state_typ_wf B [] (global_state ns) (fst \<Lambda>)) \<Longrightarrow>
           (unique_constants_distinct (global_state ns) unique_consts) \<Longrightarrow>
           ((global_state ns) = (old_global_state ns)) \<Longrightarrow>
           ((binder_state ns) = Map.empty) \<Longrightarrow> 
           (Ast.valid_configuration B \<Lambda> \<Gamma> [] checked_posts end_bb end_cont end_state)"
      and "all_pres = proc_all_pres proc_ast"
      and "checked_posts = proc_checked_posts proc_ast"
      and ABody: "procedure.proc_body proc_ast = Some (locals, ast)"
      and AVarContext:"\<Lambda> = (constants@global_vars, (proc_args proc_ast)@locals)"
      and ARets:"proc_rets proc_ast = []"
      and "proc_ty_args proc_ast = 0"   
    shows "proc_is_correct B fun_decls constants unique_consts global_vars axioms proc_ast 
             (Ast.proc_body_satisfies_spec :: 'a absval_ty_fun \<Rightarrow> mbodyCFG proc_context \<Rightarrow> var_context \<Rightarrow> 'a fun_interp \<Rightarrow> rtype_env \<Rightarrow> expr list \<Rightarrow> expr list \<Rightarrow> ast \<Rightarrow> 'a nstate \<Rightarrow> bool)"
proof -
  show "proc_is_correct B fun_decls constants unique_consts global_vars axioms proc_ast (Ast.proc_body_satisfies_spec :: 'a absval_ty_fun \<Rightarrow> mbodyCFG proc_context \<Rightarrow> var_context \<Rightarrow> 'a fun_interp \<Rightarrow> rtype_env \<Rightarrow> expr list \<Rightarrow> expr list \<Rightarrow> ast \<Rightarrow> 'a nstate \<Rightarrow> bool)"
  proof( (simp only: proc_is_correct.simps), subst ABody, simp split: option.split, (rule allI | rule impI)+,
      unfold proc_body_satisfies_spec_def,(rule allI | rule impI)+)  
    fix \<Gamma> \<Omega> gs ls end_bb end_cont end_state
    assume Atyp:"(\<forall>t. closed t \<longrightarrow> (\<exists>v. type_of_val B v = t)) \<and> (\<forall>v. closed (type_of_val B v))" and
      FunWf:"fun_interp_wf B fun_decls \<Gamma>" and
      ARenv: "list_all closed \<Omega> \<and> length \<Omega> = proc_ty_args proc_ast" and
      WfGlobal: "state_typ_wf B \<Omega> gs (constants @ global_vars)" and
      WfLocal: "state_typ_wf B \<Omega> ls (proc_args proc_ast @ locals @ proc_rets proc_ast)" and
      UniqueConsts: "unique_constants_distinct gs unique_consts" and
      AxSat: "axioms_sat B (constants, []) \<Gamma>
        \<lparr>old_global_state = Map.empty, global_state = state_restriction gs constants, local_state = Map.empty, binder_state = Map.empty\<rparr>
        axioms" and
      APres:  "expr_all_sat B (constants @ global_vars, proc_args proc_ast @ locals @ proc_rets proc_ast) \<Gamma> \<Omega>
        \<lparr>old_global_state = gs, global_state = gs, local_state = ls, binder_state = Map.empty\<rparr> (map fst (proc_pres proc_ast))" and
      Ared: "rtranclp 
               (red_bigblock 
                B ([]::mbodyCFG proc_context) (constants @ global_vars,
                proc_args proc_ast @
                locals @
                proc_rets
                 proc_ast) \<Gamma> \<Omega> ast) (init_ast ast \<lparr>old_global_state = gs, global_state = gs, local_state = ls, binder_state = Map.empty\<rparr>)
       (end_bb, end_cont, end_state)"
    have Contexteq:"\<Lambda> = (constants @ global_vars, proc_args proc_ast @ locals @ proc_rets proc_ast)"
      using AVarContext ARets by simp
    from ARenv \<open>proc_ty_args proc_ast = 0\<close> have "\<Omega> = []" by simp
    have "Ast.valid_configuration B \<Lambda> \<Gamma> [] checked_posts end_bb end_cont end_state"
      apply (rule AExpanded)
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
    thus "Ast.valid_configuration B (constants @ global_vars, proc_args proc_ast @ locals @ proc_rets proc_ast) \<Gamma> \<Omega>
        (map fst (filter (\<lambda>x. \<not> snd x) (proc_posts proc_ast))) end_bb end_cont end_state"
      using Contexteq \<open>\<Omega> = []\<close> \<open>checked_posts = _\<close>
      by simp
  qed
qed

end