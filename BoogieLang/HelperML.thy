theory HelperML
imports Main
begin

ML\<open> (* taken from Cogent; add_simps adds simplification-rules into a given context. *)
fun add_simps [] ctxt = ctxt
 |  add_simps (thm::thms) ctxt = add_simps thms (Simplifier.add_simp thm ctxt)

fun simp_tac_with_thms thms ctxt = asm_full_simp_tac (add_simps thms ctxt)

fun assm_full_simp_solved_tac ctxt = (asm_full_simp_tac ctxt |> SOLVED')

fun assm_full_simp_solved_with_thms_tac thms ctxt = (asm_full_simp_tac (add_simps thms ctxt) |> SOLVED')

fun fastforce_tac ctxt thms = Clasimp.fast_force_tac (add_simps thms ctxt)

fun simp_only_tac thms ctxt = asm_full_simp_tac (add_simps thms (Simplifier.clear_simpset ctxt))
\<close>                         

ML 
\<open>

fun THEN_ELSE' cond_tac (then_tac, else_tac) i = 
    (cond_tac i) THEN_ELSE (then_tac i, else_tac i)


(* FIRST_AND_THEN' cs fs applies the first tactic in cs that works and then applies the corresponding
   tactic in fs at the same position. *)
fun FIRST_AND_THEN' [] []  = K no_tac
  | FIRST_AND_THEN' (_ :: _) [] = error "FIRST_AND_THEN' invoked with different argument lengths"
  | FIRST_AND_THEN' [] (_ :: _) = error "FIRST_AND_THEN' invoked with different argument lengths"
  | FIRST_AND_THEN' (cand_tac :: cs) (follow_tac :: fs) =
      THEN_ELSE' cand_tac (follow_tac, FIRST_AND_THEN' cs fs)

(* The following tactic runs the input tactic on an input theorem. If the tactic fails, then NONE
   is returned. If the tactic succeeds, then the first possible outcome is returned (wrapped by Some).*)   
fun simulate_determ_tac tac st =
  (case Seq.pull (tac st) of
            NONE => NONE
          | SOME (st', _) => SOME st')

(* apply tactic that takes the number of goals as first input *)
fun tactic_ngoals tac st =
  let 
   val prop = Thm.prop_of st;
   val (As, _) = Logic.strip_horn prop
  in
   tac (length As) st
  end

(* repeat tactic exactly n times *)
fun repeat_n_tac 0 _  = all_tac
  | repeat_n_tac n tac = tac THEN repeat_n_tac (n-1) tac

fun repeat_n_tac' 0 _  = (fn _ => all_tac)
  | repeat_n_tac' n tac = tac THEN' repeat_n_tac' (n-1) tac

fun unfold_let_tac ctxt = simp_tac (Simplifier.add_simp @{thm Let_def} (empty_simpset ctxt))
\<close>

ML \<open>
fun apply_thm_n_times vc thm n =
 (if n <= 0 then vc else 
  (apply_thm_n_times (thm OF [vc]) thm (n-1))
 )

fun remove_n_assms n i = 
 (if n <= 0 then all_tac else eresolve0_tac [thin_rl] i THEN remove_n_assms (n-1) i)

(* applies "OF" to the first theorem for which the instantiation works *)
fun OF_first [] _ = NONE
 | OF_first (thm :: thms) vc =
    (SOME (thm OF [vc]))
    handle THM _ => OF_first thms vc
\<close>

end