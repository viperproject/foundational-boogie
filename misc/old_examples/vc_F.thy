theory vc_F
imports Semantics Util
begin
locale vc = 
fixes n :: "int" and r_0 :: "int" and call0formal_n_0 :: "int" and call1formal_r_0 :: "int" and call1formal_r_0_0 :: "int" and r_1 :: "int"
begin

definition vc_GeneratedUnifiedExit
  where
    "vc_GeneratedUnifiedExit  = ((((100::int) < n) \<longrightarrow> (r_1 = (n - (10::int)))) \<and> ((((100::int) < n) \<longrightarrow> (r_1 = (n - (10::int)))) \<longrightarrow> ((n \<le> (100::int)) \<longrightarrow> (r_1 = (91::int)))))"
definition vc_anon3_Then
  where
    "vc_anon3_Then  = (((100::int) < n) \<longrightarrow> (((r_0 = (n - (10::int))) \<and> (r_1 = r_0)) \<longrightarrow> vc_GeneratedUnifiedExit))"
definition vc_anon3_Else
  where
    "vc_anon3_Else  = ((n \<le> (100::int)) \<longrightarrow> (((call0formal_n_0 = (n + (11::int))) \<and> (((100::int) < call0formal_n_0) \<longrightarrow> (call1formal_r_0 = (call0formal_n_0 - (10::int))))) \<longrightarrow> (((((call0formal_n_0 \<le> (100::int)) \<longrightarrow> (call1formal_r_0 = (91::int))) \<and> (((100::int) < call1formal_r_0) \<longrightarrow> (call1formal_r_0_0 = (call1formal_r_0 - (10::int))))) \<and> (((call1formal_r_0 \<le> (100::int)) \<longrightarrow> (call1formal_r_0_0 = (91::int))) \<and> (r_1 = call1formal_r_0_0))) \<longrightarrow> vc_GeneratedUnifiedExit)))"
definition vc_anon0
  where
    "vc_anon0  = (vc_anon3_Then \<and> vc_anon3_Else)"
lemma vc_correct:

shows "vc_anon0"
apply (simp only: vc_anon0_def vc_anon3_Else_def vc_anon3_Then_def vc_GeneratedUnifiedExit_def)
  by linarith


end

locale finalProg =
  fixes n_s vc_n vc_r_0 vc_call0formal_n_0 vc_call1formal_r_0 vc_call1formal_r_0__0 vc_r_1
  assumes 
A1:"((n_s ''n'') = (Some (IntV vc_n)))" and 
A2:"((n_s ''r_0'') = (Some (IntV vc_r_0)))" and 
A3:"((n_s ''call0formal_n_0'') = (Some (IntV vc_call0formal_n_0)))" and 
A4:"((n_s ''call1formal_r_0'') = (Some (IntV vc_call1formal_r_0)))" and 
A5:"((n_s ''call1formal_r_0_0'') = (Some (IntV vc_call1formal_r_0__0)))" and 
A6:"((n_s ''r_1'') = (Some (IntV vc_r_1)))"
begin

lemmas state_assms = A1 A2 A3 A4 A5 A6

lemma GeneratedUnifiedExit_correct:
assumes 
"(red_cmd_list \<Gamma> [(Assert (BinOp (BinOp (Val (IntV 100)) Lt (Var ''n'')) Imp (BinOp (Var ''r_1'') Eq (BinOp (Var ''n'') Sub (Val (IntV 10)))))), (Assert (BinOp (BinOp (Var ''n'') Le (Val (IntV 100))) Imp (BinOp (Var ''r_1'') Eq (Val (IntV 91)))))] (Normal n_s) s')" and 
"(vc.vc_GeneratedUnifiedExit vc_n vc_r_1)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (n_s' = n_s))))"
using assms state_assms
apply cases
apply (simp only: vc.vc_GeneratedUnifiedExit_def)
  apply (handle_cmd_list_full?)
by (auto?)

lemma anon3_Then_correct:
assumes 
"(red_cmd_list \<Gamma> [(Assume (BinOp (Val (IntV 100)) Lt (Var ''n''))), (Assume (BinOp (Var ''r_0'') Eq (BinOp (Var ''n'') Sub (Val (IntV 10))))), (Assume (BinOp (Var ''r_1'') Eq (Var ''r_0'')))] (Normal n_s) s')" and 
"(vc.vc_anon3_Then vc_n vc_r_0 vc_r_1)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> ((n_s' = n_s) \<and> (vc.vc_GeneratedUnifiedExit vc_n vc_r_1)))))"
using assms finalProg_def finalProg_axioms
apply cases
apply (simp only: vc.vc_anon3_Then_def)
apply (handle_cmd_list_full?)
by (auto?)

lemma anon3_Else_correct:
assumes 
"(red_cmd_list \<Gamma> [(Assume (BinOp (Var ''n'') Le (Val (IntV 100)))), (Assume (BinOp (Var ''call0formal_n_0'') Eq (BinOp (Var ''n'') Add (Val (IntV 11))))), (Assume (BinOp (BinOp (Val (IntV 100)) Lt (Var ''call0formal_n_0'')) Imp (BinOp (Var ''call1formal_r_0'') Eq (BinOp (Var ''call0formal_n_0'') Sub (Val (IntV 10)))))), (Assume (BinOp (BinOp (Var ''call0formal_n_0'') Le (Val (IntV 100))) Imp (BinOp (Var ''call1formal_r_0'') Eq (Val (IntV 91))))), (Assume (BinOp (BinOp (Val (IntV 100)) Lt (Var ''call1formal_r_0'')) Imp (BinOp (Var ''call1formal_r_0_0'') Eq (BinOp (Var ''call1formal_r_0'') Sub (Val (IntV 10)))))), (Assume (BinOp (BinOp (Var ''call1formal_r_0'') Le (Val (IntV 100))) Imp (BinOp (Var ''call1formal_r_0_0'') Eq (Val (IntV 91))))), (Assume (BinOp (Var ''r_1'') Eq (Var ''call1formal_r_0_0'')))] (Normal n_s) s')" and 
"(vc.vc_anon3_Else vc_n vc_call0formal_n_0 vc_call1formal_r_0 vc_call1formal_r_0__0 vc_r_1)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> ((n_s' = n_s) \<and> (vc.vc_GeneratedUnifiedExit vc_n vc_r_1)))))"
using assms finalProg_def finalProg_axioms
apply cases
apply (simp only: vc.vc_anon3_Else_def)
apply (handle_cmd_list_full?)
by (auto?)

lemma anon0_correct:
assumes 
"(red_cmd_list \<Gamma> [] (Normal n_s) s')" and 
"(vc.vc_anon0 vc_n vc_r_0 vc_call0formal_n_0 vc_call1formal_r_0 vc_call1formal_r_0__0 vc_r_1)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> ((n_s' = n_s) \<and> ((vc.vc_anon3_Then vc_n vc_r_0 vc_r_1) \<and> (vc.vc_anon3_Else vc_n vc_call0formal_n_0 vc_call1formal_r_0 vc_call1formal_r_0__0 vc_r_1))))))"
using assms finalProg_def finalProg_axioms
apply cases
apply (simp only: vc.vc_anon0_def)
apply (handle_cmd_list_full?)
  by (auto?)

end

locale Test =
  fixes n_s vc_n vc_r_0 vc_call0formal_n_0 vc_call1formal_r_0 vc_call1formal_r_0__0 vc_r_1
  assumes 
  "((n_s ''n'') = (Some (IntV vc_n)))"
begin

lemma test: "((n_s ''n'') = (Some (IntV vc_n)))"  
  using Test_axioms Test_def by blast


end

end


end