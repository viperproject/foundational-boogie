theory ExperimentalML
  imports Semantics Util VCHints VCExprHelper
begin


ML\<open> (* taken from Cogent; add_simps adds simplification-rules into a given context. *)
fun add_simps [] ctxt = ctxt
 |  add_simps (thm::thms) ctxt = add_simps thms (Simplifier.add_simp thm ctxt)
\<close>

ML \<open>
fun apply_thm_n_times vc thm n =
 (if n <= 0 then vc else 
  (apply_thm_n_times (thm OF [vc]) thm (n-1))
 )

fun remove_n_assms n i = 
 (if n <= 0 then all_tac else eresolve0_tac [thin_rl] i THEN remove_n_assms (n-1) i)
\<close>

ML \<open>
(** Tactics for quantifiers **)

fun quantifier_basic_tac ctxt =
  FIRST'[
  resolve_tac ctxt [@{thm forall_vc_rel_int}],
  resolve_tac ctxt [@{thm forall_vc_rel_bool}],
  resolve_tac ctxt [@{thm exists_vc_rel_int}],
  resolve_tac ctxt [@{thm exists_vc_rel_int}]
  ];

fun quantifier_poly_tac forall_poly_lemma ctxt =
  resolve_tac ctxt [forall_poly_lemma] THEN' 
  asm_full_simp_tac ctxt THEN'
  asm_full_simp_tac ctxt; 

(* repeat forall at least once and if it succeds, there may be a type premise. To avoid using the 
type premise tactic if it is an actual implication at the Boogie level, the binary op rule is applied
first and only if this fails, the type premise rule is applied *)
fun quantifier_main_tac forall_poly_lemma ctxt i = 
  (REPEAT1 (quantifier_basic_tac ctxt i ORELSE (forall_poly_tac forall_poly_lemma ctxt i))) THEN
  ((resolve_tac ctxt [@{thm RedBinOp}] i) ORELSE
   (resolve_tac ctxt [@{thm imp_vc}] i THEN 
    asm_full_simp_tac ctxt i) ORELSE all_tac);
\<close>

ML \<open>
(** Tactics for proving \<Gamma> \<turnstile> \<langle>e, ns\<rangle> \<Down> BoolV vc  **)

fun vc_expr_rel_select_tac red_expr_tac ctxt assms del_thms (t,i) =
  case (Logic.strip_assums_concl t) of
    Const (@{const_name "HOL.eq"},_) $ _ $ _ => (asm_full_simp_tac (add_simps assms ctxt) |> SOLVED') i
   | @{term "Trueprop"} $ t' => vc_expr_rel_select_tac red_expr_tac ctxt assms del_thms (t',i)
   | _ => red_expr_tac ctxt assms del_thms i

fun b_prove_assert_expr_simple_tac ctxt assms del_thms =
REPEAT_ALL_NEW (SUBGOAL (vc_expr_rel_select_tac 
(fn ctxt => fn assms => fn del_thms => FIRST' [
resolve_tac ctxt [@{thm RedVar}] THEN' (asm_full_simp_tac ((ctxt addsimps assms delsimps del_thms))),
resolve_tac ctxt [@{thm RedLit}],
resolve_tac ctxt [@{thm RedBinOp}],
resolve_tac ctxt [@{thm RedUnOp}],
resolve_tac ctxt [@{thm RedFunOp}] THEN' (asm_full_simp_tac (ctxt addsimps assms delsimps del_thms)),
resolve_tac ctxt [@{thm RedExpListNil}],
resolve_tac ctxt [@{thm RedExpListCons}]
]) ctxt assms del_thms)
)

fun vc_expr_rel_red_tac ctxt assms del_thms = 
 FIRST' [
resolve_tac ctxt [@{thm RedVar}] THEN' (asm_full_simp_tac (ctxt addsimps assms delsimps del_thms) |> SOLVED'),
resolve_tac ctxt [@{thm RedLit}],
resolve_tac ctxt [@{thm conj_vc_rel}],
resolve_tac ctxt [@{thm disj_vc_rel}],
resolve_tac ctxt [@{thm imp_vc_rel}],
resolve_tac ctxt [@{thm not_vc_rel}],
resolve_tac ctxt [@{thm forallt_vc}],
resolve_tac ctxt [@{thm forall_vc_rel_int}] THEN' simp_tac (ctxt delsimps (@{thms simp_thms} @ del_thms)),
resolve_tac ctxt [@{thm forall_vc_rel_bool}] THEN' simp_tac (ctxt delsimps (@{thms simp_thms} @ del_thms)),
resolve_tac ctxt [@{thm exists_vc_rel_int}] THEN' simp_tac (ctxt delsimps (@{thms simp_thms} @ del_thms)),
resolve_tac ctxt [@{thm exists_vc_rel_int}] THEN' simp_tac (ctxt delsimps (@{thms simp_thms} @ del_thms)),

(*
resolve_tac ctxt [@{thm add_vc_rel}],
resolve_tac ctxt [@{thm sub_vc_rel}],
resolve_tac ctxt [@{thm mul_vc_rel}],
resolve_tac ctxt [@{thm uminus_vc_rel}],
*)
resolve_tac ctxt [@{thm RedFunOp}] THEN' (asm_full_simp_tac (ctxt addsimps assms delsimps del_thms) |> SOLVED'),
resolve_tac ctxt [@{thm RedExpListNil}],
resolve_tac ctxt [@{thm RedExpListCons}],
CHANGED o b_prove_assert_expr_simple_tac ctxt assms []
(*(b_prove_assert_expr_simple_tac ctxt assms |> SOLVED')*)
]

fun b_vc_expr_rel_tac ctxt assms del_thms =
  REPEAT o SUBGOAL (vc_expr_rel_select_tac vc_expr_rel_red_tac ctxt assms del_thms)

(* rewrite VC based on expression hint *)
fun expr_hint_tac ctxt (expr_hint:ExprHint option) i =
  (case expr_hint of
    (SOME (RewriteVC thm)) => resolve_tac ctxt [thm] i
    | _ => all_tac
  );
\<close>

ML \<open>
(** Tactics to deal with assume statements **)

fun b_assume_base_tac ctxt inst_thm vc_elim expr_hint global_assms i =
(resolve_tac ctxt [inst_thm] i) THEN 
  (asm_full_simp_tac ctxt i) THEN
  (resolve_tac ctxt [vc_elim] i) THEN
  (expr_hint_tac ctxt expr_hint i) THEN
  (resolve_tac ctxt [@{thm expr_to_vc}] i) THEN
  (assume_tac ctxt i) THEN
  (b_vc_expr_rel_tac ctxt global_assms [] i)

fun b_assume_foc_tac global_assms vc_elim expr_hint i (focus: Subgoal.focus) =
let
  val (red :: vc :: _) = #prems(focus)
  val ctxt = #context(focus)
in
  (b_assume_base_tac ctxt (@{thm assume_ml} OF [red]) (vc_elim vc) expr_hint global_assms i)
  handle THM _ => no_tac
end

fun b_assume_simple_tac ctxt global_assms vc_elim expr_hint n_assms_rem =
  (Subgoal.FOCUS (b_assume_foc_tac global_assms vc_elim expr_hint 1) ctxt 1) THEN   
   remove_n_assms n_assms_rem 1


fun b_assume_conjr_tac ctxt b_assume_tac global_assms expr_hint n =
  let val vc_elim = 
    fn (vc) => @{thm imp_conj_elim} OF [(apply_thm_n_times vc @{thm imp_conj_imp} (n-1))]
  in
    (b_assume_tac ctxt global_assms vc_elim expr_hint 3)
  end
\<close>

ML \<open>
(** Tactics to deal with assert statements **)

fun b_prove_assert_expr_tac ctxt vc_expr global_assms i =
(resolve_tac ctxt [@{thm vc_to_expr} OF vc_expr] i) THEN
(b_vc_expr_rel_tac ctxt global_assms [] i)

fun b_assert_base_tac ctxt inst_thm vc_expr global_assms ehint i =
(resolve_tac ctxt [inst_thm] i) THEN
  (expr_hint_tac ctxt ehint i) THEN
  (b_prove_assert_expr_tac ctxt vc_expr global_assms i)

fun b_assert_foc_tac b_assert_base_tac global_assms vc_elim ehint i (focus: Subgoal.focus) =
let 
  val (red :: vc :: _) = #prems(focus)
  val ctxt = #context(focus)
in
 (b_assert_base_tac ctxt (@{thm assert_ml} OF [red]) [(@{thm conjunct1} OF [vc])] global_assms ehint i) THEN
  (resolve_tac ctxt [(vc_elim OF [vc])] i)  
  handle THM _ => no_tac 
end

fun b_assert_tac ctxt b_assert_base_tac global_assms vc_elim ehint =
  (Subgoal.FOCUS (b_assert_foc_tac b_assert_base_tac global_assms vc_elim ehint 1) ctxt 1)  THEN
  eresolve0_tac [thin_rl] 1 THEN
  eresolve0_tac [thin_rl] 1

fun b_assert_no_conj_foc_tac b_assert_base_tac global_assms ehint i (focus: Subgoal.focus) =
let 
  val (red :: vc :: _) = #prems(focus) 
  val ctxt = #context(focus)
in
 (b_assert_base_tac ctxt (@{thm assert_ml} OF [red]) [vc] global_assms ehint i)
  handle THM _ => no_tac 
end

fun b_assert_no_conj_tac b_assert_tac ctxt global_assms ehint =
  (Subgoal.FOCUS (b_assert_no_conj_foc_tac b_assert_tac global_assms ehint 1) ctxt 1)
\<close>

ML \<open>
(** main tactic **)

fun b_vc_hint_tac ctxt  _ _ _ _ ([]: (VcHint * (ExprHint option)) list) =
  TRY (eresolve_tac ctxt [@{thm nil_cmd_elim}] 1 THEN asm_full_simp_tac ctxt 1)
| b_vc_hint_tac ctxt b_assume_tac b_assert_base_tac forall_poly_tac global_assms (x::xs) = 
  (case x of
  (* assume statement normal *)
    (AssumeConjR 0, ehint) => b_assume_tac ctxt global_assms (fn (vc) => @{thm impE} OF [vc]) ehint 3
  | (AssumeConjR n, ehint) => 
     if n = 1 then
        b_assume_tac ctxt global_assms (fn (vc) => @{thm imp_conj_elim} OF [vc]) ehint 3
     else
       b_assume_conjr_tac ctxt b_assume_tac global_assms ehint n
  (* assert statement normal *)
  | (AssertNoConj, ehint) => b_assert_no_conj_tac b_assert_base_tac ctxt global_assms ehint
  | (AssertConj, ehint) => b_assert_tac ctxt b_assert_base_tac global_assms (@{thm conj_elim_2}) ehint
  | (AssertSub, ehint) => b_assert_tac ctxt b_assert_base_tac global_assms (@{thm conj_imp_elim}) ehint 
  (* special cases *)
  | (AssumeFalse, _) => (eresolve_tac ctxt [@{thm assume_false_cmds}] 1) THEN (ALLGOALS (asm_full_simp_tac ctxt))
  | (AssumeNot, ehint) => b_assume_tac ctxt global_assms (fn (vc) => @{thm imp_not_elim} OF [vc]) ehint 0 THEN 
      TRY (ALLGOALS (asm_full_simp_tac ctxt))
  | (AssertFalse, _) => SOLVED' (asm_full_simp_tac ctxt) 1
  | (AssumeTrue, _) => (eresolve_tac ctxt [@{thm assume_true_cmds}] 1) THEN (asm_full_simp_tac ctxt 1) THEN
                  rotate_tac 1 1
  | (AssertTrue, _) => (eresolve_tac ctxt [@{thm assert_true_cmds}] 1) THEN (rotate_tac 1 1)
  ) THEN
   b_vc_hint_tac ctxt b_assume_tac b_assert_base_tac forall_poly_tac global_assms xs 

fun b_vc_tac ctxt = b_vc_hint_tac ctxt b_assume_simple_tac b_assert_base_tac 
\<close>

end