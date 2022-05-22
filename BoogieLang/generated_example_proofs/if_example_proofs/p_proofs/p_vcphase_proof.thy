theory p_vcphase_proof
imports Boogie_Lang.Semantics Boogie_Lang.Util Boogie_Lang.VCHints Boogie_Lang.VCPhaseML p_passive_prog p_before_passive_prog
begin
locale vc
begin

definition vc_anon3
  where
    "vc_anon3 x_1 = (x_1 > (0::int))"
definition vc_anon4_Then
  where
    "vc_anon4_Then x_0 x_1 = (((x_0 > (5::int)) \<and> (x_1 = (10::int))) \<longrightarrow> (vc_anon3 x_1))"
definition vc_anon4_Else
  where
    "vc_anon4_Else x_0 x_1 = ((((5::int) \<ge> x_0) \<and> (x_1 = (1::int))) \<longrightarrow> (vc_anon3 x_1))"
definition vc_anon0
  where
    "vc_anon0 x_0 x_1 = ((vc_anon4_Then x_0 x_1) \<and> (vc_anon4_Else x_0 x_1))"

end

locale passification = 
fixes A :: "(('a)absval_ty_fun)" and \<Lambda> :: "(var_context)" and \<Gamma> :: "(('a)fun_interp)" and n_s :: "(('a)nstate)" and vc_x :: "int" and vc_x_0 :: "int" and vc_x_1 :: "int"
assumes 
G0: "((lookup_var \<Lambda> n_s 0) = (Some (IntV vc_x)))" and 
G1: "((lookup_var \<Lambda> n_s 1) = (Some (IntV vc_x_0)))" and 
G2: "((lookup_var \<Lambda> n_s 2) = (Some (IntV vc_x_1)))" and 
G3: "(\<And> v. (closed ((type_of_val A) v)))"
begin

lemmas global_assms = G0 G1 G2 G3
lemmas forall_poly_thm = forall_vc_type[OF G3]
lemmas exists_poly_thm = exists_vc_type[OF G3]
declare Nat.One_nat_def[simp del]

ML\<open>
val block_anon3_hints = [
(AssertNoConj,NONE)]
\<close>
lemma block_anon3AA0:
shows "((red_cmd_list A M \<Lambda> \<Gamma> \<Omega> p_passive_prog.block_0 (Normal n_s) s') \<Longrightarrow> ((vc.vc_anon3 vc_x_1) \<Longrightarrow> ((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (n_s' = n_s))))))"
unfolding p_passive_prog.block_0_def vc.vc_anon3_def
apply (tactic \<open> boogie_vc_tac @{context} @{thms global_assms} (@{thm forall_poly_thm}, @{thm exists_poly_thm}) block_anon3_hints \<close>)
by (auto?)

ML\<open>
val block_anon4_Then_hints = [
(AssumeConjR 1,NONE), 
(AssumeConjR 0,NONE)]
\<close>
lemma block_anon4_ThenAA0:
shows "((red_cmd_list A M \<Lambda> \<Gamma> \<Omega> p_passive_prog.block_1 (Normal n_s) s') \<Longrightarrow> ((vc.vc_anon4_Then vc_x_0 vc_x_1) \<Longrightarrow> ((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> ((n_s' = n_s) \<and> (vc.vc_anon3 vc_x_1)))))))"
unfolding p_passive_prog.block_1_def vc.vc_anon4_Then_def
apply (tactic \<open> boogie_vc_tac @{context} @{thms global_assms} (@{thm forall_poly_thm}, @{thm exists_poly_thm}) block_anon4_Then_hints \<close>)
by (auto?)

ML\<open>
val block_anon4_Else_hints = [
(AssumeConjR 1,NONE), 
(AssumeConjR 0,NONE)]
\<close>
lemma block_anon4_ElseAA0:
shows "((red_cmd_list A M \<Lambda> \<Gamma> \<Omega> p_passive_prog.block_2 (Normal n_s) s') \<Longrightarrow> ((vc.vc_anon4_Else vc_x_0 vc_x_1) \<Longrightarrow> ((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> ((n_s' = n_s) \<and> (vc.vc_anon3 vc_x_1)))))))"
unfolding p_passive_prog.block_2_def vc.vc_anon4_Else_def
apply (tactic \<open> boogie_vc_tac @{context} @{thms global_assms} (@{thm forall_poly_thm}, @{thm exists_poly_thm}) block_anon4_Else_hints \<close>)
by (auto?)

lemma block_anon0:
assumes 
"(red_cmd_list A M \<Lambda> \<Gamma> \<Omega> p_passive_prog.block_3 (Normal n_s) s')" and 
"((vc.vc_anon4_Then vc_x_0 vc_x_1) \<and> (vc.vc_anon4_Else vc_x_0 vc_x_1))"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> ((n_s' = n_s) \<and> ((vc.vc_anon4_Then vc_x_0 vc_x_1) \<and> (vc.vc_anon4_Else vc_x_0 vc_x_1))))))"
using assms
unfolding p_passive_prog.block_3_def
apply cases
by auto

lemma block_0:
assumes 
"(red_cmd_list A M \<Lambda> \<Gamma> \<Omega> p_passive_prog.block_4 (Normal n_s) s')" and 
"((vc.vc_anon4_Then vc_x_0 vc_x_1) \<and> (vc.vc_anon4_Else vc_x_0 vc_x_1))"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> ((n_s' = n_s) \<and> ((vc.vc_anon4_Then vc_x_0 vc_x_1) \<and> (vc.vc_anon4_Else vc_x_0 vc_x_1))))))"
using assms
unfolding p_passive_prog.block_4_def
apply cases
by auto

lemma block_anon0AA0:
shows "((red_cmd_list A M \<Lambda> \<Gamma> \<Omega> p_passive_prog.block_5 (Normal n_s) s') \<Longrightarrow> ((vc.vc_anon0 vc_x_0 vc_x_1) \<Longrightarrow> ((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> ((n_s' = n_s) \<and> ((vc.vc_anon4_Then vc_x_0 vc_x_1) \<and> (vc.vc_anon4_Else vc_x_0 vc_x_1))))))))"
apply (erule red_cmd_list.cases)
using global_assms
unfolding p_passive_prog.block_5_def vc.vc_anon0_def
apply (handle_cmd_list_full?)
by (auto?)

lemma cfg_block_anon3:
assumes 
"(red_cfg_multi A M \<Lambda> \<Gamma> \<Omega> p_passive_prog.proc_body ((Inl 0),(Normal n_s)) (m',s'))" and 
"(vc.vc_anon3 vc_x_1)"
shows "(s' \<noteq> Failure)"
apply (rule converse_rtranclpE2[OF assms(1)], fastforce)
apply (rule red_cfg_multi_backwards_step_no_succ[OF assms(1) p_passive_prog.node_0 p_passive_prog.outEdges_0])
using block_anon3AA0[OF _ assms(2)] by blast

lemma cfg_block_anon4_Then:
assumes 
"(red_cfg_multi A M \<Lambda> \<Gamma> \<Omega> p_passive_prog.proc_body ((Inl 1),(Normal n_s)) (m',s'))" and 
"(vc.vc_anon4_Then vc_x_0 vc_x_1)"
shows "(s' \<noteq> Failure)"
apply (rule converse_rtranclpE2[OF assms(1)], fastforce)
apply (rule red_cfg_multi_backwards_step[OF assms(1) p_passive_prog.node_1])
apply (erule block_anon4_ThenAA0[OF _ assms(2)])
apply ((simp add:p_passive_prog.outEdges_1))
apply (erule member_elim, simp)
apply (erule cfg_block_anon3, simp?)
by (simp add: member_rec(2))

lemma cfg_block_anon4_Else:
assumes 
"(red_cfg_multi A M \<Lambda> \<Gamma> \<Omega> p_passive_prog.proc_body ((Inl 2),(Normal n_s)) (m',s'))" and 
"(vc.vc_anon4_Else vc_x_0 vc_x_1)"
shows "(s' \<noteq> Failure)"
apply (rule converse_rtranclpE2[OF assms(1)], fastforce)
apply (rule red_cfg_multi_backwards_step[OF assms(1) p_passive_prog.node_2])
apply (erule block_anon4_ElseAA0[OF _ assms(2)])
apply ((simp add:p_passive_prog.outEdges_2))
apply (erule member_elim, simp)
apply (erule cfg_block_anon3, simp?)
by (simp add: member_rec(2))

lemma cfg_block_anon0:
assumes 
"(red_cfg_multi A M \<Lambda> \<Gamma> \<Omega> p_passive_prog.proc_body ((Inl 3),(Normal n_s)) (m',s'))" and 
"((vc.vc_anon4_Then vc_x_0 vc_x_1) \<and> (vc.vc_anon4_Else vc_x_0 vc_x_1))"
shows "(s' \<noteq> Failure)"
apply (rule converse_rtranclpE2[OF assms(1)], fastforce)
apply (rule red_cfg_multi_backwards_step[OF assms(1) p_passive_prog.node_3])
apply (erule block_anon0[OF _ assms(2)])
apply ((simp add:p_passive_prog.outEdges_3))
apply (erule member_elim, simp)
apply (erule cfg_block_anon4_Then, simp?)
apply (erule member_elim, simp)
apply (erule cfg_block_anon4_Else, simp?)
by (simp add: member_rec(2))

lemma cfg_block_0:
assumes 
"(red_cfg_multi A M \<Lambda> \<Gamma> \<Omega> p_passive_prog.proc_body ((Inl 4),(Normal n_s)) (m',s'))" and 
"((vc.vc_anon4_Then vc_x_0 vc_x_1) \<and> (vc.vc_anon4_Else vc_x_0 vc_x_1))"
shows "(s' \<noteq> Failure)"
apply (rule converse_rtranclpE2[OF assms(1)], fastforce)
apply (rule red_cfg_multi_backwards_step[OF assms(1) p_passive_prog.node_4])
apply (erule block_0[OF _ assms(2)])
apply ((simp add:p_passive_prog.outEdges_4))
apply (erule member_elim, simp)
apply (erule cfg_block_anon0, simp?)
by (simp add: member_rec(2))

lemma cfg_PreconditionGeneratedEntry:
assumes 
"(red_cfg_multi A M \<Lambda> \<Gamma> \<Omega> p_passive_prog.proc_body ((Inl 5),(Normal n_s)) (m',s'))" and 
"(vc.vc_anon0 vc_x_0 vc_x_1)"
shows "(s' \<noteq> Failure)"
apply (rule converse_rtranclpE2[OF assms(1)], fastforce)
apply (rule red_cfg_multi_backwards_step[OF assms(1) p_passive_prog.node_5])
apply (erule block_anon0AA0[OF _ assms(2)])
apply ((simp add:p_passive_prog.outEdges_5))
apply (erule member_elim, simp)
apply (erule cfg_block_0, simp?)
by (simp add: member_rec(2))


end

locale axioms = 
fixes A :: "(('a)absval_ty_fun)" and \<Lambda> :: "(var_context)" and \<Gamma> :: "(('a)fun_interp)" and n_s :: "(('a)nstate)"
assumes 
G0: "(\<And> v. (closed ((type_of_val A) v)))"
begin

lemmas global_assms = G0
lemmas forall_poly_thm = forall_vc_type[OF G0]
lemmas exists_poly_thm = exists_vc_type[OF G0]
declare Nat.One_nat_def[simp del]


end

definition ctor_list
  where
    "ctor_list  = []"
fun ctor :: "((closed_ty) => int)"
  where
    "ctor (TConC s _) = (the (map_of ctor_list s))"
declare One_nat_def[simp del]

lemma end_to_end:
assumes 
Red: "(red_cfg_multi A M ((append global_data.constants_vdecls global_data.globals_vdecls),(append p_passive_prog.params_vdecls p_passive_prog.locals_vdecls)) \<Gamma> [] p_passive_prog.proc_body ((Inl 5),(Normal n_s)) (m',s'))" and 
VC: "(\<And> (vc_x::int) (vc_x_0::int) (vc_x_1::int). (vc.vc_anon0 vc_x_0 vc_x_1))" and 
Closed: "(\<And> v. (closed ((type_of_val A) v)))" and 
NonEmptyTypes: "(\<And> t. ((closed t) \<Longrightarrow> (\<exists> v. (((type_of_val A) v) = t))))" and 
FInterp: "(fun_interp_wf A global_data.fdecls \<Gamma>)" and 
Axioms: "(axiom_assm A \<Gamma> global_data.constants_vdecls (n_s::(('a)nstate)) global_data.axioms)" and 
ParamsLocal: "(state_typ_wf A [] (local_state n_s) (append p_passive_prog.params_vdecls p_passive_prog.locals_vdecls))" and 
ConstsGlobal: "(state_typ_wf A [] (global_state n_s) (append global_data.constants_vdecls global_data.globals_vdecls))"
shows "(s' \<noteq> Failure)"
proof -
let ?n_s_c = "(nstate_global_restriction n_s global_data.constants_vdecls)"
let ?\<Lambda> = "((append global_data.constants_vdecls global_data.globals_vdecls),(append p_passive_prog.params_vdecls p_passive_prog.locals_vdecls))"
let ?\<Lambda>c = "((global_data.constants_vdecls,[])::(var_context))"
from ParamsLocal have sc_x:"(((lookup_var ?\<Lambda> n_s 0) = (Some (IntV (convert_val_to_int (the (lookup_var ?\<Lambda> n_s 0)))))) \<and> (((type_of_val A) (the (lookup_var ?\<Lambda> n_s 0))) = (TPrim TInt)))"
apply (simp only:state_typ_wf_def)
apply (erule allE, erule allE, erule impE, rule map_of_lookup_vdecls_ty[OF p_passive_prog.m_x])
apply (subst lookup_var_local[OF p_passive_prog.m_x])+
by (fastforce dest: tint_intv tbool_boolv)
from ParamsLocal have sc_x_0:"(((lookup_var ?\<Lambda> n_s 1) = (Some (IntV (convert_val_to_int (the (lookup_var ?\<Lambda> n_s 1)))))) \<and> (((type_of_val A) (the (lookup_var ?\<Lambda> n_s 1))) = (TPrim TInt)))"
apply (simp only:state_typ_wf_def)
apply (erule allE, erule allE, erule impE, rule map_of_lookup_vdecls_ty[OF p_passive_prog.m_x_0])
apply (subst lookup_var_local[OF p_passive_prog.m_x_0])+
by (fastforce dest: tint_intv tbool_boolv)
from ParamsLocal have sc_x_1:"(((lookup_var ?\<Lambda> n_s 2) = (Some (IntV (convert_val_to_int (the (lookup_var ?\<Lambda> n_s 2)))))) \<and> (((type_of_val A) (the (lookup_var ?\<Lambda> n_s 2))) = (TPrim TInt)))"
apply (simp only:state_typ_wf_def)
apply (erule allE, erule allE, erule impE, rule map_of_lookup_vdecls_ty[OF p_passive_prog.m_x_1])
apply (subst lookup_var_local[OF p_passive_prog.m_x_1])+
by (fastforce dest: tint_intv tbool_boolv)
show "(s' \<noteq> Failure)"
apply (rule passification.cfg_PreconditionGeneratedEntry[OF _ Red])
apply (simp only:passification_def)
apply (intro conjI)?
apply (rule HOL.conjunct1[OF sc_x])
apply (rule HOL.conjunct1[OF sc_x_0])
apply (rule HOL.conjunct1[OF sc_x_1])
apply (simp add:Closed)
apply (rule VC)
done
qed



end