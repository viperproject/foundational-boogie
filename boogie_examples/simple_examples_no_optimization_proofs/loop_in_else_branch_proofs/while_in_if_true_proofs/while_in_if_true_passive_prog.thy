theory while_in_if_true_passive_prog
imports Boogie_Lang.Semantics Boogie_Lang.Util while_in_if_true_before_ast_to_cfg_prog
begin
definition block_0
  where
    "block_0  = []"
definition block_1
  where
    "block_1  = [(Assert (BinOp (Var 6) Lt (Lit (LInt 0))))]"
definition block_2
  where
    "block_2  = [(Assume (BinOp (Var 2) Gt (Lit (LInt 0)))),(Assume (BinOp (Var 6) Eq (Var 2)))]"
definition block_3
  where
    "block_3  = [(Assume (BinOp (Lit (LInt 0)) Ge (Var 5))),(Assume (BinOp (Var 6) Eq (Var 4)))]"
definition block_4
  where
    "block_4  = [(Assume (BinOp (Var 5) Gt (Lit (LInt 0)))),(Assume (BinOp (Var 7) Eq (BinOp (Var 5) Sub (Lit (LInt 1))))),(Assume (Lit (LBool False)))]"
definition block_5
  where
    "block_5  = []"
definition block_6
  where
    "block_6  = [(Assume (BinOp (Lit (LInt 0)) Ge (Var 2))),(Assume (BinOp (Var 4) Eq (BinOp (Var 2) Sub (Lit (LInt 1)))))]"
definition block_7
  where
    "block_7  = []"
definition block_8
  where
    "block_8  = []"
definition block_9
  where
    "block_9  = []"
definition outEdges
  where
    "outEdges  = [[],[0],[1],[1],[0],[3,4],[5],[2,6],[7],[8]]"
definition node_to_blocks
  where
    "node_to_blocks  = [block_0,block_1,block_2,block_3,block_4,block_5,block_6,block_7,block_8,block_9]"
definition proc_body
  where
    "proc_body  = (|entry = 9,out_edges = outEdges,node_to_block = node_to_blocks|)"
lemma node_0:
shows "((nth (node_to_block proc_body) 0) = block_0)"
by (simp add:proc_body_def node_to_blocks_def)

lemma node_1:
shows "((nth (node_to_block proc_body) 1) = block_1)"
by (simp add:proc_body_def node_to_blocks_def)

lemma node_2:
shows "((nth (node_to_block proc_body) 2) = block_2)"
by (simp add:proc_body_def node_to_blocks_def)

lemma node_3:
shows "((nth (node_to_block proc_body) 3) = block_3)"
by (simp add:proc_body_def node_to_blocks_def)

lemma node_4:
shows "((nth (node_to_block proc_body) 4) = block_4)"
by (simp add:proc_body_def node_to_blocks_def)

lemma node_5:
shows "((nth (node_to_block proc_body) 5) = block_5)"
by (simp add:proc_body_def node_to_blocks_def)

lemma node_6:
shows "((nth (node_to_block proc_body) 6) = block_6)"
by (simp add:proc_body_def node_to_blocks_def)

lemma node_7:
shows "((nth (node_to_block proc_body) 7) = block_7)"
by (simp add:proc_body_def node_to_blocks_def)

lemma node_8:
shows "((nth (node_to_block proc_body) 8) = block_8)"
by (simp add:proc_body_def node_to_blocks_def)

lemma node_9:
shows "((nth (node_to_block proc_body) 9) = block_9)"
by (simp add:proc_body_def node_to_blocks_def)

lemma outEdges_0:
shows "((nth (out_edges proc_body) 0) = [])"
by (simp add:proc_body_def outEdges_def)

lemma outEdges_1:
shows "((nth (out_edges proc_body) 1) = [0])"
by (simp add:proc_body_def outEdges_def)

lemma outEdges_2:
shows "((nth (out_edges proc_body) 2) = [1])"
by (simp add:proc_body_def outEdges_def)

lemma outEdges_3:
shows "((nth (out_edges proc_body) 3) = [1])"
by (simp add:proc_body_def outEdges_def)

lemma outEdges_4:
shows "((nth (out_edges proc_body) 4) = [0])"
by (simp add:proc_body_def outEdges_def)

lemma outEdges_5:
shows "((nth (out_edges proc_body) 5) = [3,4])"
by (simp add:proc_body_def outEdges_def)

lemma outEdges_6:
shows "((nth (out_edges proc_body) 6) = [5])"
by (simp add:proc_body_def outEdges_def)

lemma outEdges_7:
shows "((nth (out_edges proc_body) 7) = [2,6])"
by (simp add:proc_body_def outEdges_def)

lemma outEdges_8:
shows "((nth (out_edges proc_body) 8) = [7])"
by (simp add:proc_body_def outEdges_def)

lemma outEdges_9:
shows "((nth (out_edges proc_body) 9) = [8])"
by (simp add:proc_body_def outEdges_def)

definition params_vdecls :: "(vdecls)"
  where
    "params_vdecls  = []"
definition locals_vdecls :: "(vdecls)"
  where
    "locals_vdecls  = [(0,(TPrim TInt),(None )),(1,(TPrim TInt),(None )),(2,(TPrim TInt),(None )),(3,(TPrim TInt),(None )),(4,(TPrim TInt),(None )),(5,(TPrim TInt),(None )),(6,(TPrim TInt),(None )),(7,(TPrim TInt),(None ))]"
lemma locals_min_aux:
shows "(((map fst (append while_in_if_true_passive_prog.params_vdecls while_in_if_true_passive_prog.locals_vdecls)) \<noteq> []) \<longrightarrow> ((Min (set (map fst (append while_in_if_true_passive_prog.params_vdecls while_in_if_true_passive_prog.locals_vdecls)))) \<ge> 0))"
unfolding while_in_if_true_passive_prog.params_vdecls_def while_in_if_true_passive_prog.locals_vdecls_def
by simp

lemma locals_min:
shows "(\<forall> x. ((Set.member x (set (map fst (append while_in_if_true_passive_prog.params_vdecls while_in_if_true_passive_prog.locals_vdecls)))) \<longrightarrow> (x \<ge> 0)))"
using locals_min_aux helper_min
by blast

lemma globals_locals_disj:
shows "((Set.inter (set (map fst (append while_in_if_true_before_ast_to_cfg_prog.constants_vdecls while_in_if_true_before_ast_to_cfg_prog.globals_vdecls))) (set (map fst (append while_in_if_true_passive_prog.params_vdecls while_in_if_true_passive_prog.locals_vdecls)))) = {})"
unfolding while_in_if_true_before_ast_to_cfg_prog.constants_vdecls_def while_in_if_true_before_ast_to_cfg_prog.globals_vdecls_def
by simp

lemma m_x:
shows "((map_of (append while_in_if_true_passive_prog.params_vdecls while_in_if_true_passive_prog.locals_vdecls) 0) = (Some ((TPrim TInt),(None ))))"
by (simp add:params_vdecls_def locals_vdecls_def)

lemma m_y:
shows "((map_of (append while_in_if_true_passive_prog.params_vdecls while_in_if_true_passive_prog.locals_vdecls) 1) = (Some ((TPrim TInt),(None ))))"
by (simp add:params_vdecls_def locals_vdecls_def)

lemma m_x_0:
shows "((map_of (append while_in_if_true_passive_prog.params_vdecls while_in_if_true_passive_prog.locals_vdecls) 2) = (Some ((TPrim TInt),(None ))))"
by (simp add:params_vdecls_def locals_vdecls_def)

lemma m_y_0:
shows "((map_of (append while_in_if_true_passive_prog.params_vdecls while_in_if_true_passive_prog.locals_vdecls) 3) = (Some ((TPrim TInt),(None ))))"
by (simp add:params_vdecls_def locals_vdecls_def)

lemma m_x_1:
shows "((map_of (append while_in_if_true_passive_prog.params_vdecls while_in_if_true_passive_prog.locals_vdecls) 4) = (Some ((TPrim TInt),(None ))))"
by (simp add:params_vdecls_def locals_vdecls_def)

lemma m_y_1:
shows "((map_of (append while_in_if_true_passive_prog.params_vdecls while_in_if_true_passive_prog.locals_vdecls) 5) = (Some ((TPrim TInt),(None ))))"
by (simp add:params_vdecls_def locals_vdecls_def)

lemma m_x_2:
shows "((map_of (append while_in_if_true_passive_prog.params_vdecls while_in_if_true_passive_prog.locals_vdecls) 6) = (Some ((TPrim TInt),(None ))))"
by (simp add:params_vdecls_def locals_vdecls_def)

lemma m_y_2:
shows "((map_of (append while_in_if_true_passive_prog.params_vdecls while_in_if_true_passive_prog.locals_vdecls) 7) = (Some ((TPrim TInt),(None ))))"
by (simp add:params_vdecls_def locals_vdecls_def)

lemma l_x:
shows "((lookup_var_decl ((append while_in_if_true_before_ast_to_cfg_prog.constants_vdecls while_in_if_true_before_ast_to_cfg_prog.globals_vdecls),(append while_in_if_true_passive_prog.params_vdecls while_in_if_true_passive_prog.locals_vdecls)) 0) = (Some ((TPrim TInt),(None ))))" and "((lookup_var_ty ((append while_in_if_true_before_ast_to_cfg_prog.constants_vdecls while_in_if_true_before_ast_to_cfg_prog.globals_vdecls),(append while_in_if_true_passive_prog.params_vdecls while_in_if_true_passive_prog.locals_vdecls)) 0) = (Some (TPrim TInt)))"
using globals_locals_disj m_x
by (simp_all add: lookup_var_decl_global_2 lookup_var_decl_local lookup_var_decl_ty_Some)

lemma l_y:
shows "((lookup_var_decl ((append while_in_if_true_before_ast_to_cfg_prog.constants_vdecls while_in_if_true_before_ast_to_cfg_prog.globals_vdecls),(append while_in_if_true_passive_prog.params_vdecls while_in_if_true_passive_prog.locals_vdecls)) 1) = (Some ((TPrim TInt),(None ))))" and "((lookup_var_ty ((append while_in_if_true_before_ast_to_cfg_prog.constants_vdecls while_in_if_true_before_ast_to_cfg_prog.globals_vdecls),(append while_in_if_true_passive_prog.params_vdecls while_in_if_true_passive_prog.locals_vdecls)) 1) = (Some (TPrim TInt)))"
using globals_locals_disj m_y
by (simp_all add: lookup_var_decl_global_2 lookup_var_decl_local lookup_var_decl_ty_Some)

lemma l_x_0:
shows "((lookup_var_decl ((append while_in_if_true_before_ast_to_cfg_prog.constants_vdecls while_in_if_true_before_ast_to_cfg_prog.globals_vdecls),(append while_in_if_true_passive_prog.params_vdecls while_in_if_true_passive_prog.locals_vdecls)) 2) = (Some ((TPrim TInt),(None ))))" and "((lookup_var_ty ((append while_in_if_true_before_ast_to_cfg_prog.constants_vdecls while_in_if_true_before_ast_to_cfg_prog.globals_vdecls),(append while_in_if_true_passive_prog.params_vdecls while_in_if_true_passive_prog.locals_vdecls)) 2) = (Some (TPrim TInt)))"
using globals_locals_disj m_x_0
by (simp_all add: lookup_var_decl_global_2 lookup_var_decl_local lookup_var_decl_ty_Some)

lemma l_y_0:
shows "((lookup_var_decl ((append while_in_if_true_before_ast_to_cfg_prog.constants_vdecls while_in_if_true_before_ast_to_cfg_prog.globals_vdecls),(append while_in_if_true_passive_prog.params_vdecls while_in_if_true_passive_prog.locals_vdecls)) 3) = (Some ((TPrim TInt),(None ))))" and "((lookup_var_ty ((append while_in_if_true_before_ast_to_cfg_prog.constants_vdecls while_in_if_true_before_ast_to_cfg_prog.globals_vdecls),(append while_in_if_true_passive_prog.params_vdecls while_in_if_true_passive_prog.locals_vdecls)) 3) = (Some (TPrim TInt)))"
using globals_locals_disj m_y_0
by (simp_all add: lookup_var_decl_global_2 lookup_var_decl_local lookup_var_decl_ty_Some)

lemma l_x_1:
shows "((lookup_var_decl ((append while_in_if_true_before_ast_to_cfg_prog.constants_vdecls while_in_if_true_before_ast_to_cfg_prog.globals_vdecls),(append while_in_if_true_passive_prog.params_vdecls while_in_if_true_passive_prog.locals_vdecls)) 4) = (Some ((TPrim TInt),(None ))))" and "((lookup_var_ty ((append while_in_if_true_before_ast_to_cfg_prog.constants_vdecls while_in_if_true_before_ast_to_cfg_prog.globals_vdecls),(append while_in_if_true_passive_prog.params_vdecls while_in_if_true_passive_prog.locals_vdecls)) 4) = (Some (TPrim TInt)))"
using globals_locals_disj m_x_1
by (simp_all add: lookup_var_decl_global_2 lookup_var_decl_local lookup_var_decl_ty_Some)

lemma l_y_1:
shows "((lookup_var_decl ((append while_in_if_true_before_ast_to_cfg_prog.constants_vdecls while_in_if_true_before_ast_to_cfg_prog.globals_vdecls),(append while_in_if_true_passive_prog.params_vdecls while_in_if_true_passive_prog.locals_vdecls)) 5) = (Some ((TPrim TInt),(None ))))" and "((lookup_var_ty ((append while_in_if_true_before_ast_to_cfg_prog.constants_vdecls while_in_if_true_before_ast_to_cfg_prog.globals_vdecls),(append while_in_if_true_passive_prog.params_vdecls while_in_if_true_passive_prog.locals_vdecls)) 5) = (Some (TPrim TInt)))"
using globals_locals_disj m_y_1
by (simp_all add: lookup_var_decl_global_2 lookup_var_decl_local lookup_var_decl_ty_Some)

lemma l_x_2:
shows "((lookup_var_decl ((append while_in_if_true_before_ast_to_cfg_prog.constants_vdecls while_in_if_true_before_ast_to_cfg_prog.globals_vdecls),(append while_in_if_true_passive_prog.params_vdecls while_in_if_true_passive_prog.locals_vdecls)) 6) = (Some ((TPrim TInt),(None ))))" and "((lookup_var_ty ((append while_in_if_true_before_ast_to_cfg_prog.constants_vdecls while_in_if_true_before_ast_to_cfg_prog.globals_vdecls),(append while_in_if_true_passive_prog.params_vdecls while_in_if_true_passive_prog.locals_vdecls)) 6) = (Some (TPrim TInt)))"
using globals_locals_disj m_x_2
by (simp_all add: lookup_var_decl_global_2 lookup_var_decl_local lookup_var_decl_ty_Some)

lemma l_y_2:
shows "((lookup_var_decl ((append while_in_if_true_before_ast_to_cfg_prog.constants_vdecls while_in_if_true_before_ast_to_cfg_prog.globals_vdecls),(append while_in_if_true_passive_prog.params_vdecls while_in_if_true_passive_prog.locals_vdecls)) 7) = (Some ((TPrim TInt),(None ))))" and "((lookup_var_ty ((append while_in_if_true_before_ast_to_cfg_prog.constants_vdecls while_in_if_true_before_ast_to_cfg_prog.globals_vdecls),(append while_in_if_true_passive_prog.params_vdecls while_in_if_true_passive_prog.locals_vdecls)) 7) = (Some (TPrim TInt)))"
using globals_locals_disj m_y_2
by (simp_all add: lookup_var_decl_global_2 lookup_var_decl_local lookup_var_decl_ty_Some)


end
