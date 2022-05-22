theory no_guard_if_before_cfg_to_dag_prog
imports Boogie_Lang.Semantics Boogie_Lang.TypeSafety Boogie_Lang.Util "../global_data"
begin
definition block_0
  where
    "block_0  = [(Havoc 0)]"
definition block_1
  where
    "block_1  = [(Assign 0 (Lit (LInt 1)))]"
definition block_2
  where
    "block_2  = [(Assign 0 (Lit (LInt 0)))]"
definition outEdges
  where
    "outEdges  = [[2,1],[],[]]"
definition node_to_blocks
  where
    "node_to_blocks  = [block_0,block_1,block_2]"
definition proc_body
  where
    "proc_body  = (|entry = 0,out_edges = outEdges,node_to_block = node_to_blocks|)"
lemma node_0:
shows "((nth (node_to_block proc_body) 0) = block_0)"
by (simp add:proc_body_def node_to_blocks_def)

lemma node_1:
shows "((nth (node_to_block proc_body) 1) = block_1)"
by (simp add:proc_body_def node_to_blocks_def)

lemma node_2:
shows "((nth (node_to_block proc_body) 2) = block_2)"
by (simp add:proc_body_def node_to_blocks_def)

lemma outEdges_0:
shows "((nth (out_edges proc_body) 0) = [2,1])"
by (simp add:proc_body_def outEdges_def)

lemma outEdges_1:
shows "((nth (out_edges proc_body) 1) = [])"
by (simp add:proc_body_def outEdges_def)

lemma outEdges_2:
shows "((nth (out_edges proc_body) 2) = [])"
by (simp add:proc_body_def outEdges_def)

definition pres
  where
    "pres  = []"
definition post
  where
    "post  = []"
definition params_vdecls :: "(vdecls)"
  where
    "params_vdecls  = []"
definition locals_vdecls :: "(vdecls)"
  where
    "locals_vdecls  = [(0,(TPrim TInt),(None ))]"
lemma locals_min_aux:
shows "(((map fst (append no_guard_if_before_cfg_to_dag_prog.params_vdecls no_guard_if_before_cfg_to_dag_prog.locals_vdecls)) \<noteq> []) \<longrightarrow> ((Min (set (map fst (append no_guard_if_before_cfg_to_dag_prog.params_vdecls no_guard_if_before_cfg_to_dag_prog.locals_vdecls)))) \<ge> 0))"
unfolding no_guard_if_before_cfg_to_dag_prog.params_vdecls_def no_guard_if_before_cfg_to_dag_prog.locals_vdecls_def
by simp

lemma locals_min:
shows "(\<forall> x. ((Set.member x (set (map fst (append no_guard_if_before_cfg_to_dag_prog.params_vdecls no_guard_if_before_cfg_to_dag_prog.locals_vdecls)))) \<longrightarrow> (x \<ge> 0)))"
using locals_min_aux helper_min
by blast

lemma globals_locals_disj:
shows "((Set.inter (set (map fst (append global_data.constants_vdecls global_data.globals_vdecls))) (set (map fst (append no_guard_if_before_cfg_to_dag_prog.params_vdecls no_guard_if_before_cfg_to_dag_prog.locals_vdecls)))) = {})"
unfolding global_data.constants_vdecls_def global_data.globals_vdecls_def
by simp

lemma consts_wf:
shows "((list_all (comp (wf_ty 0) (comp fst snd)) global_data.constants_vdecls) )"
unfolding global_data.constants_vdecls_def
by simp

lemma globals_wf:
shows "((list_all (comp (wf_ty 0) (comp fst snd)) global_data.globals_vdecls) )"
unfolding global_data.globals_vdecls_def
by simp

lemma params_wf:
shows "((list_all (comp (wf_ty 0) (comp fst snd)) no_guard_if_before_cfg_to_dag_prog.params_vdecls) )"
unfolding no_guard_if_before_cfg_to_dag_prog.params_vdecls_def
by simp

lemma locals_wf:
shows "((list_all (comp (wf_ty 0) (comp fst snd)) no_guard_if_before_cfg_to_dag_prog.locals_vdecls) )"
unfolding no_guard_if_before_cfg_to_dag_prog.locals_vdecls_def
by simp

lemma var_context_wf:
shows "(\<forall> x \<tau>. (((lookup_var_ty ((append global_data.constants_vdecls global_data.globals_vdecls),(append no_guard_if_before_cfg_to_dag_prog.params_vdecls no_guard_if_before_cfg_to_dag_prog.locals_vdecls)) x) = (Some \<tau>)) \<longrightarrow> ((wf_ty 0) \<tau>)))"
apply (rule lookup_ty_pred_2)
by ((simp_all add:consts_wf globals_wf params_wf locals_wf))

lemma m_x:
shows "((map_of (append no_guard_if_before_cfg_to_dag_prog.params_vdecls no_guard_if_before_cfg_to_dag_prog.locals_vdecls) 0) = (Some ((TPrim TInt),(None ))))"
by (simp add:params_vdecls_def locals_vdecls_def)

lemma l_x:
shows "((lookup_var_decl ((append global_data.constants_vdecls global_data.globals_vdecls),(append no_guard_if_before_cfg_to_dag_prog.params_vdecls no_guard_if_before_cfg_to_dag_prog.locals_vdecls)) 0) = (Some ((TPrim TInt),(None ))))" and "((lookup_var_ty ((append global_data.constants_vdecls global_data.globals_vdecls),(append no_guard_if_before_cfg_to_dag_prog.params_vdecls no_guard_if_before_cfg_to_dag_prog.locals_vdecls)) 0) = (Some (TPrim TInt)))"
using globals_locals_disj m_x
by (simp_all add: lookup_var_decl_global_2 lookup_var_decl_local lookup_var_decl_ty_Some)

definition proc :: "(procedure)"
  where
    "proc  = (|proc_ty_args = 0,proc_args = no_guard_if_before_cfg_to_dag_prog.params_vdecls,proc_rets = [],proc_modifs = [],proc_pres = (exprs_to_only_checked_spec no_guard_if_before_cfg_to_dag_prog.pres),proc_posts = (exprs_to_only_checked_spec no_guard_if_before_cfg_to_dag_prog.post),proc_body = (Some (no_guard_if_before_cfg_to_dag_prog.locals_vdecls,no_guard_if_before_cfg_to_dag_prog.proc_body))|)"

end
