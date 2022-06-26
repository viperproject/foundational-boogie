theory triangle_cfgtodag_proof
imports Boogie_Lang.Semantics Boogie_Lang.Util Boogie_Lang.BackedgeElim Boogie_Lang.TypingML triangle_before_cfg_to_dag_prog triangle_before_passive_prog triangle_passification_proof triangle_vcphase_proof
begin
locale cfg_to_dag_lemmas = 
fixes A :: "(('a)absval_ty_fun)" and \<Gamma> :: "(('a)fun_interp)"
assumes 
Wf_Fun: "(fun_interp_wf A global_data.fdecls \<Gamma>)"
begin

abbreviation \<Lambda>1
  where
    "\<Lambda>1  \<equiv> ((append global_data.constants_vdecls global_data.globals_vdecls),(append triangle_before_cfg_to_dag_prog.params_vdecls triangle_before_cfg_to_dag_prog.locals_vdecls))"
declare Nat.One_nat_def[simp del]

lemma ty_hint_1:
shows "(hint_ty_subst [])"
by (simp add: hint_ty_subst_def)

lemma cfg_block_GeneratedUnifiedExit:
assumes 
"(\<And> m2' s2'. ((red_cfg_multi A M \<Lambda>1 \<Gamma> [] triangle_before_passive_prog.proc_body ((Inl 0),(Normal ns2)) (m2',s2')) \<Longrightarrow> (s2' \<noteq> Failure)))" and 
"(state_well_typed A \<Lambda>1 [] ns2)"
shows "(expr_all_sat A \<Lambda>1 \<Gamma> [] ns2 triangle_before_cfg_to_dag_prog.post)"
unfolding expr_all_sat_def triangle_before_cfg_to_dag_prog.post_def 
apply (rule cfg_dag_rel_post_invs_3)
apply (erule assms(1))
apply (rule triangle_before_passive_prog.node_0)
apply simp
apply (rule type_safety_top_level_inv[OF Wf_Fun global_data.funcs_wf triangle_before_cfg_to_dag_prog.var_context_wf])
apply (rule assms(2))
apply (simp)
apply ((tactic \<open> typing_tac @{context} @{thms ty_hint_1} @{thms triangle_before_cfg_to_dag_prog.l_t(2) triangle_before_cfg_to_dag_prog.l_n(2)} [] 1\<close>))

unfolding triangle_before_passive_prog.block_0_def
by cfg_dag_rel_tac_single+

lemma block_anon2_LoopDone:
assumes 
"(red_cmd_list A M \<Lambda>1 \<Gamma> [] triangle_before_cfg_to_dag_prog.block_3 (Normal ns1) s')" and 
"(\<And> s2'. ((red_cmd_list A M \<Lambda>1 \<Gamma> [] triangle_before_passive_prog.block_1 (Normal ns2) s2') \<Longrightarrow> (s2' \<noteq> Failure)))" and 
"(dag_lemma_assms A \<Lambda>1 \<Gamma> [] [] [] ns1 ns2)"
shows "(dag_lemma_conclusion A M \<Lambda>1 \<Gamma> [] [] triangle_before_passive_prog.block_1 ns2 s' False)"
using assms
apply (rule dag_rel_block_lemma_compact, simp)
unfolding triangle_before_cfg_to_dag_prog.block_3_def triangle_before_passive_prog.block_1_def
apply cfg_dag_rel_tac_single+
apply simp
apply simp
done

lemma cfg_block_anon2_LoopDone:
assumes 
Red: "(red_cfg_k_step A M \<Lambda>1 \<Gamma> [] triangle_before_cfg_to_dag_prog.proc_body ((Inl 3),(Normal ns1)) j (m',s'))" and 
DagAssms: "(dag_lemma_assms A \<Lambda>1 \<Gamma> [] [] [] ns1 ns2)" and 
DagVerifies: "(\<And> m2' s2'. ((red_cfg_multi A M \<Lambda>1 \<Gamma> [] triangle_before_passive_prog.proc_body ((Inl 1),(Normal ns2)) (m2',s2')) \<Longrightarrow> (s2' \<noteq> Failure)))"
shows "(valid_configuration A \<Lambda>1 \<Gamma> [] triangle_before_cfg_to_dag_prog.post m' s')"
apply (rule cfg_dag_helper_return_2[OF Red])
apply (rule triangle_before_cfg_to_dag_prog.node_3)
apply (rule triangle_before_passive_prog.node_1)
apply (erule DagVerifies)
apply (rule DagAssms)
apply (erule block_anon2_LoopDone)
apply assumption+
apply (rule triangle_before_cfg_to_dag_prog.outEdges_3)
apply (rule triangle_before_passive_prog.outEdges_1)
apply (erule cfg_block_GeneratedUnifiedExit)
by assumption


lemma ty_hint_2:
shows "(hint_ty_subst [])"
by (simp add: hint_ty_subst_def)

lemma Mods_anon2_LoopBody:
shows "(mods_contained_in (set [2,1]) triangle_before_cfg_to_dag_prog.block_2)"
unfolding triangle_before_cfg_to_dag_prog.block_2_def
by simp

lemma block_anon2_LoopBody:
assumes 
"(red_cmd_list A M \<Lambda>1 \<Gamma> [] triangle_before_cfg_to_dag_prog.block_2 (Normal ns1) s')" and 
"(\<And> s2'. ((red_cmd_list A M \<Lambda>1 \<Gamma> [] triangle_before_passive_prog.block_2 (Normal ns2) s2') \<Longrightarrow> (s2' \<noteq> Failure)))" and 
"(dag_lemma_assms A \<Lambda>1 \<Gamma> [] [] [] ns1 ns2)"
shows "(dag_lemma_conclusion A M \<Lambda>1 \<Gamma> [] [(BinOp (Var 2) Eq (BinOp (BinOp (Var 1) Mul (BinOp (Var 1) Sub (Lit (LInt 1)))) Div (Lit (LInt 2)))),(BinOp (Var 1) Le (Var 0))] triangle_before_passive_prog.block_2 ns2 s' True)"
using assms
apply (rule dag_rel_block_lemma_compact, simp)
unfolding triangle_before_cfg_to_dag_prog.block_2_def triangle_before_passive_prog.block_2_def
apply cfg_dag_rel_tac_single+
apply simp
apply simp
apply (intro conjI)
apply (erule type_safety_top_level_inv[OF Wf_Fun global_data.funcs_wf triangle_before_cfg_to_dag_prog.var_context_wf])
apply (simp)
apply ((tactic \<open> typing_tac @{context} @{thms ty_hint_2} @{thms triangle_before_cfg_to_dag_prog.l_t(2) triangle_before_cfg_to_dag_prog.l_m(2)} [] 1\<close>))
apply (erule type_safety_top_level_inv[OF Wf_Fun global_data.funcs_wf triangle_before_cfg_to_dag_prog.var_context_wf])
apply (simp)
apply ((tactic \<open> typing_tac @{context} [] @{thms triangle_before_cfg_to_dag_prog.l_m(2) triangle_before_cfg_to_dag_prog.l_n(2)} [] 1\<close>))

done

lemma cfg_block_anon2_LoopBody:
assumes 
Red: "(red_cfg_k_step A M \<Lambda>1 \<Gamma> [] triangle_before_cfg_to_dag_prog.proc_body ((Inl 2),(Normal ns1)) j (m',s'))" and 
DagAssms: "(dag_lemma_assms A \<Lambda>1 \<Gamma> [] [] [] ns1 ns2)" and 
DagVerifies: "(\<And> m2' s2'. ((red_cfg_multi A M \<Lambda>1 \<Gamma> [] triangle_before_passive_prog.proc_body ((Inl 2),(Normal ns2)) (m2',s2')) \<Longrightarrow> (s2' \<noteq> Failure)))" and 
IH_anon2_LoopHead: "(loop_ih A M \<Lambda>1 \<Gamma> [] triangle_before_cfg_to_dag_prog.proc_body [2,1] [(BinOp (Var 2) Eq (BinOp (BinOp (Var 1) Mul (BinOp (Var 1) Sub (Lit (LInt 1)))) Div (Lit (LInt 2)))),(BinOp (Var 1) Le (Var 0))] triangle_before_cfg_to_dag_prog.post ns1 s' 1 m' j)"
shows "(valid_configuration A \<Lambda>1 \<Gamma> [] triangle_before_cfg_to_dag_prog.post m' s')"
apply (rule cfg_dag_helper_2[OF Red _ _ DagVerifies DagAssms])
apply (rule triangle_before_cfg_to_dag_prog.node_2)
apply (rule triangle_before_passive_prog.node_2)
apply (assumption+)
apply (rule block_anon2_LoopBody)
apply (assumption+)
apply (rule Mods_anon2_LoopBody)
apply ((simp add:triangle_before_cfg_to_dag_prog.outEdges_2))
apply ((simp add:triangle_before_cfg_to_dag_prog.outEdges_2))
apply (erule member_elim)
apply (rule loop_ih_apply[where ?j'="j-1"])
apply (rule IH_anon2_LoopHead)
apply (simp, simp)
unfolding dag_lemma_assms_def
apply (intro conjI, simp)
apply (rule nstate_same_on_sym)
apply (simp)
apply (simp)
apply (rule dag_lemma_assms_state_wt_1[OF DagAssms])
by (simp add: member_rec(2))


lemma Mods_anon2_LoopHead:
shows "(mods_contained_in (set [2,1]) triangle_before_cfg_to_dag_prog.block_1)"
unfolding triangle_before_cfg_to_dag_prog.block_1_def
by simp

lemma block_anon2_LoopHead:
assumes 
"(red_cmd_list A M \<Lambda>1 \<Gamma> [] triangle_before_cfg_to_dag_prog.block_1 (Normal ns1) s')" and 
"(\<And> s2'. ((red_cmd_list A M \<Lambda>1 \<Gamma> [] triangle_before_passive_prog.block_3 (Normal ns2) s2') \<Longrightarrow> (s2' \<noteq> Failure)))" and 
"(dag_lemma_assms A \<Lambda>1 \<Gamma> [] [2,1] [(BinOp (Var 2) Eq (BinOp (BinOp (Var 1) Mul (BinOp (Var 1) Sub (Lit (LInt 1)))) Div (Lit (LInt 2)))),(BinOp (Var 1) Le (Var 0))] ns1 ns2)"
shows "(dag_lemma_conclusion A M \<Lambda>1 \<Gamma> [] [] triangle_before_passive_prog.block_3 ns2 s' False)"
using assms
apply (rule dag_rel_block_lemma_compact, simp)
unfolding triangle_before_cfg_to_dag_prog.block_1_def triangle_before_passive_prog.block_3_def
apply cfg_dag_rel_tac_single+
apply simp
apply ((simp add:triangle_before_cfg_to_dag_prog.l_t(1)))
apply ((simp add:triangle_before_cfg_to_dag_prog.l_m(1)))
apply simp
done

lemma cfg_block_anon2_LoopHead:
assumes 
Red: "(red_cfg_k_step A M \<Lambda>1 \<Gamma> [] triangle_before_cfg_to_dag_prog.proc_body ((Inl 1),(Normal ns1)) j (m',s'))" and 
DagAssms: "(dag_lemma_assms A \<Lambda>1 \<Gamma> [] [2,1] [(BinOp (Var 2) Eq (BinOp (BinOp (Var 1) Mul (BinOp (Var 1) Sub (Lit (LInt 1)))) Div (Lit (LInt 2)))),(BinOp (Var 1) Le (Var 0))] ns1 ns2)" and 
DagVerifies: "(\<And> m2' s2'. ((red_cfg_multi A M \<Lambda>1 \<Gamma> [] triangle_before_passive_prog.proc_body ((Inl 3),(Normal ns2)) (m2',s2')) \<Longrightarrow> (s2' \<noteq> Failure)))"
shows "(valid_configuration A \<Lambda>1 \<Gamma> [] triangle_before_cfg_to_dag_prog.post m' s')"
using Red DagAssms
proof (induction j arbitrary: ns1 rule: less_induct)
case (less j)
show ?case
proof (cases j)
case 0 with less.prems(1) show ?thesis unfolding valid_configuration_def by auto
next
case (Suc j')
from less(3) have StateRel1:"(nstate_same_on \<Lambda>1 ns1 ns2 (set [2,1]))"by (simp add: dag_lemma_assms_def)
from less(3) have StateWt2:"(state_well_typed A \<Lambda>1 [] ns2)"by (simp add: dag_lemma_assms_def)
show ?thesis
apply (rule cfg_dag_helper_2[OF less(2) _ _ DagVerifies less(3)])
apply (rule triangle_before_cfg_to_dag_prog.node_1)
apply (rule triangle_before_passive_prog.node_3)
apply (assumption+)
apply (rule block_anon2_LoopHead)
apply (assumption+)
apply (rule Mods_anon2_LoopHead)
apply ((simp add:triangle_before_cfg_to_dag_prog.outEdges_1))
apply ((simp add:triangle_before_cfg_to_dag_prog.outEdges_1))
apply (erule member_elim)
apply simp
apply (erule allE[where x=1])
apply ((simp add:triangle_before_passive_prog.outEdges_3))
apply ((simp add:member_rec(1)))
apply (rule cfg_block_anon2_LoopDone)
apply simp
unfolding dag_lemma_assms_def
apply (intro conjI)
apply simp
apply simp
apply (fastforce)
apply (simp)
apply (simp)
apply (erule member_elim)
apply simp
apply (erule allE[where x=2])
apply ((simp add:triangle_before_passive_prog.outEdges_3))
apply ((simp add:member_rec(1)))
apply (rule cfg_block_anon2_LoopBody)
apply simp
unfolding dag_lemma_assms_def
apply (intro conjI)
apply simp
apply simp
apply (fastforce)
apply (simp)
apply (simp)
apply (rule loop_ih_prove)
apply (rule less.IH)
apply (erule strictly_smaller_helper, assumption, assumption)
unfolding dag_lemma_assms_def
apply (intro conjI, simp)
apply (rule nstate_same_on_transitive_2[OF _ _ StateRel1])
apply ((fastforce, simp, simp))
apply (rule dag_lemma_assms_state_wt_2[OF less(3)])
by (simp add: member_rec(2))
qed
qed


lemma ty_hint_3:
shows "(hint_ty_subst [])"
by (simp add: hint_ty_subst_def)

lemma block_anon0:
assumes 
"(red_cmd_list A M \<Lambda>1 \<Gamma> [] triangle_before_cfg_to_dag_prog.block_0 (Normal ns1) s')" and 
"(\<And> s2'. ((red_cmd_list A M \<Lambda>1 \<Gamma> [] triangle_before_passive_prog.block_4 (Normal ns2) s2') \<Longrightarrow> (s2' \<noteq> Failure)))" and 
"(dag_lemma_assms A \<Lambda>1 \<Gamma> [] [] [] ns1 ns2)"
shows "(dag_lemma_conclusion A M \<Lambda>1 \<Gamma> [] [(BinOp (Var 2) Eq (BinOp (BinOp (Var 1) Mul (BinOp (Var 1) Sub (Lit (LInt 1)))) Div (Lit (LInt 2)))),(BinOp (Var 1) Le (Var 0))] triangle_before_passive_prog.block_4 ns2 s' False)"
using assms
apply (rule dag_rel_block_lemma_compact, simp)
unfolding triangle_before_cfg_to_dag_prog.block_0_def triangle_before_passive_prog.block_4_def
apply cfg_dag_rel_tac_single+
apply simp
apply simp
apply (intro conjI)
apply (erule type_safety_top_level_inv[OF Wf_Fun global_data.funcs_wf triangle_before_cfg_to_dag_prog.var_context_wf])
apply (simp)
apply ((tactic \<open> typing_tac @{context} @{thms ty_hint_3} @{thms triangle_before_cfg_to_dag_prog.l_t(2) triangle_before_cfg_to_dag_prog.l_m(2)} [] 1\<close>))
apply (erule type_safety_top_level_inv[OF Wf_Fun global_data.funcs_wf triangle_before_cfg_to_dag_prog.var_context_wf])
apply (simp)
apply ((tactic \<open> typing_tac @{context} [] @{thms triangle_before_cfg_to_dag_prog.l_m(2) triangle_before_cfg_to_dag_prog.l_n(2)} [] 1\<close>))

done

lemma cfg_block_anon0:
assumes 
Red: "(red_cfg_k_step A M \<Lambda>1 \<Gamma> [] triangle_before_cfg_to_dag_prog.proc_body ((Inl 0),(Normal ns1)) j (m',s'))" and 
DagAssms: "(dag_lemma_assms A \<Lambda>1 \<Gamma> [] [] [] ns1 ns2)" and 
DagVerifies: "(\<And> m2' s2'. ((red_cfg_multi A M \<Lambda>1 \<Gamma> [] triangle_before_passive_prog.proc_body ((Inl 4),(Normal ns2)) (m2',s2')) \<Longrightarrow> (s2' \<noteq> Failure)))"
shows "(valid_configuration A \<Lambda>1 \<Gamma> [] triangle_before_cfg_to_dag_prog.post m' s')"
apply (rule cfg_dag_helper_1[OF Red _ _ DagVerifies DagAssms])
apply (rule triangle_before_cfg_to_dag_prog.node_0)
apply (rule triangle_before_passive_prog.node_4)
apply (assumption+)
apply (rule block_anon0)
apply (assumption+)
apply ((simp add:triangle_before_cfg_to_dag_prog.outEdges_0))
apply ((simp add:triangle_before_cfg_to_dag_prog.outEdges_0))
apply (erule member_elim)
apply simp
apply (erule allE[where x=3])
apply ((simp add:triangle_before_passive_prog.outEdges_4))
apply ((simp add:member_rec(1)))
apply (rule cfg_block_anon2_LoopHead)
apply simp
unfolding dag_lemma_assms_def
apply (intro conjI)
apply simp
apply (erule nstate_same_on_empty_subset)
apply (fastforce)
apply (simp)
apply (simp)
by (simp add: member_rec(2))


lemma cfg_block_0:
assumes 
"(\<forall> m2' s2'. ((red_cfg_multi A M \<Lambda>1 \<Gamma> [] triangle_before_passive_prog.proc_body ((Inl 5),(Normal ns2)) (m2',s2')) \<longrightarrow> (s2' \<noteq> Failure)))" and 
"(nstate_same_on \<Lambda>1 ns1 ns2 {})" and 
"(state_well_typed A \<Lambda>1 [] ns1)" and 
"(state_well_typed A \<Lambda>1 [] ns2)" and 
"((\<And> m2' s2'. ((red_cfg_multi A M \<Lambda>1 \<Gamma> [] triangle_before_passive_prog.proc_body ((Inl 4),(Normal ns2)) (m2',s2')) \<Longrightarrow> (s2' \<noteq> Failure))) \<Longrightarrow> R)"
shows "R"
using assms
apply (rule cfg_dag_empty_propagate_helper)
apply (assumption, simp)
apply ((simp add:triangle_before_passive_prog.outEdges_5))
by ((simp add:triangle_before_passive_prog.node_5 triangle_before_passive_prog.block_5_def))

lemma entry_lemma:
assumes 
"(red_cfg_k_step A M \<Lambda>1 \<Gamma> [] triangle_before_cfg_to_dag_prog.proc_body ((Inl 0),(Normal ns1)) j (m',s'))" and 
"(dag_lemma_assms A \<Lambda>1 \<Gamma> [] [] [] ns1 ns2)" and 
"(\<And> m2' s2'. ((red_cfg_multi A M \<Lambda>1 \<Gamma> [] triangle_before_passive_prog.proc_body ((Inl 6),(Normal ns2)) (m2',s2')) \<Longrightarrow> (s2' \<noteq> Failure)))" and 
"(expr_all_sat A \<Lambda>1 \<Gamma> [] ns2 triangle_before_cfg_to_dag_prog.pres)"
shows "(valid_configuration A \<Lambda>1 \<Gamma> [] triangle_before_cfg_to_dag_prog.post m' s')"
apply (rule cfg_dag_helper_entry)
apply (rule triangle_before_passive_prog.node_6)
apply (erule assms(3))
apply (rule assms(2))
unfolding triangle_before_passive_prog.block_6_def
apply (rule assume_pres_normal[where ?es=triangle_before_cfg_to_dag_prog.pres])
apply (rule assms(4))
unfolding triangle_before_cfg_to_dag_prog.pres_def
apply simp
apply (rule triangle_before_passive_prog.outEdges_6)
apply ((simp add:triangle_before_passive_prog.node_5 triangle_before_passive_prog.block_5_def))
apply (rule triangle_before_passive_prog.outEdges_5)
by (rule cfg_block_anon0[OF assms(1-2)])


end

abbreviation \<Lambda>0
  where
    "\<Lambda>0  \<equiv> ((append global_data.constants_vdecls global_data.globals_vdecls),(append triangle_before_cfg_to_dag_prog.params_vdecls triangle_before_cfg_to_dag_prog.locals_vdecls))"
lemma end_to_end_theorem_aux:
assumes 
Red: "(red_cfg_multi A M ((append global_data.constants_vdecls global_data.globals_vdecls),(append triangle_before_cfg_to_dag_prog.params_vdecls triangle_before_cfg_to_dag_prog.locals_vdecls)) \<Gamma> [] triangle_before_cfg_to_dag_prog.proc_body ((Inl 0),(Normal ns)) (m',s'))" and 
VC: "(\<And> (vc_n::int) (vc_m::int) (vc_t_0::int) (vc_m_0::int) (vc_t_1::int) (vc_m_1::int) (vc_t_2::int) (vc_t::int). (vc.vc_PreconditionGeneratedEntry vc_n vc_t_0 vc_m_0 vc_t_2 vc_t_1 vc_m_1))" and 
Closed: "(\<And> v. (closed ((type_of_val A) v)))" and 
NonEmptyTypes: "(\<And> t. ((closed t) \<Longrightarrow> (\<exists> v. (((type_of_val A) v) = t))))" and 
FInterp: "(fun_interp_wf A global_data.fdecls \<Gamma>)" and 
Axioms: "(axiom_assm A \<Gamma> global_data.constants_vdecls (ns::(('a)nstate)) global_data.axioms)" and 
Precondition: "(expr_all_sat A \<Lambda>0 \<Gamma> [] ns triangle_before_cfg_to_dag_prog.pres)" and 
ParamsLocal: "(state_typ_wf A [] (local_state ns) (snd \<Lambda>0))" and 
ConstsGlobal: "(state_typ_wf A [] (global_state ns) (fst \<Lambda>0))" and 
OldGlobal: "((global_state ns) = (old_global_state ns))" and 
BinderNs: "((binder_state ns) = Map.empty)"
shows "(valid_configuration A \<Lambda>0 \<Gamma> [] triangle_before_cfg_to_dag_prog.post m' s')"
proof -
from Red obtain j where Aux:"(red_cfg_k_step A M ((append global_data.constants_vdecls global_data.globals_vdecls),(append triangle_before_cfg_to_dag_prog.params_vdecls triangle_before_cfg_to_dag_prog.locals_vdecls)) \<Gamma> [] triangle_before_cfg_to_dag_prog.proc_body ((Inl 0),(Normal ns)) j (m',s'))"
by (meson rtranclp_imp_relpowp)
show ?thesis
apply (rule cfg_to_dag_lemmas.entry_lemma)
unfolding cfg_to_dag_lemmas_def
apply (rule FInterp)
apply (rule Aux)
apply (rule dag_lemma_assms_same)
unfolding state_well_typed_def
apply (intro conjI)
using ParamsLocal apply simp
using ConstsGlobal apply simp
using ConstsGlobal OldGlobal apply simp
using BinderNs apply simp
apply (rule triangle_passification_proof.glue_proof.end_to_end)
unfolding glue_proof_def
apply (intro conjI)
apply assumption
using VC apply simp
using Closed apply simp
using NonEmptyTypes apply simp
apply (rule FInterp)
using Axioms apply simp
using ParamsLocal apply simp
using ConstsGlobal apply simp
using BinderNs apply simp
using OldGlobal apply simp
using Precondition apply simp
done
qed


lemma end_to_end_theorem:
assumes 
VC: "(\<And> (vc_n::int) (vc_m::int) (vc_t_0::int) (vc_m_0::int) (vc_t_1::int) (vc_m_1::int) (vc_t_2::int) (vc_t::int). (vc.vc_PreconditionGeneratedEntry vc_n vc_t_0 vc_m_0 vc_t_2 vc_t_1 vc_m_1))"
shows "(\<And> A. (proc_is_correct (A::(('a)absval_ty_fun)) global_data.fdecls global_data.constants_vdecls global_data.globals_vdecls global_data.axioms triangle_before_cfg_to_dag_prog.proc))"
apply (rule end_to_end_util[OF end_to_end_theorem_aux])
apply assumption using VC apply simp  apply assumption+
by (simp_all add: exprs_to_only_checked_spec_1 exprs_to_only_checked_spec_2 triangle_before_cfg_to_dag_prog.proc_def triangle_before_cfg_to_dag_prog.proc_body_def)


end