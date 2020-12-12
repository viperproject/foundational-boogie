theory Passification
imports Semantics "HOL-Eisbach.Eisbach" "HOL-Eisbach.Eisbach_Tools" Util
begin

text \<open>Dependence of set U on variables D\<close>

type_synonym passive_rel = "vname \<rightharpoonup> (vname + lit)"

definition lookup_var_ty_match :: "'a absval_ty_fun \<Rightarrow> var_context \<Rightarrow> rtype_env \<Rightarrow> 'a nstate \<Rightarrow> vname \<Rightarrow> ty \<Rightarrow> bool"
  where "lookup_var_ty_match A \<Lambda> \<Omega> ns x \<tau> = (Option.map_option (type_of_val A) (lookup_var \<Lambda> ns x) = Some (instantiate \<Omega> \<tau>))"

definition closed_set_ty :: "'a absval_ty_fun \<Rightarrow> var_context \<Rightarrow> rtype_env \<Rightarrow>  ('a nstate) set \<Rightarrow> 'a nstate \<Rightarrow> vname \<Rightarrow> ty \<Rightarrow> bool"
  where "closed_set_ty A \<Lambda> \<Omega> U ns x \<tau> = (\<forall>v :: 'a val. type_of_val A v = instantiate \<Omega> \<tau> \<longrightarrow> update_var \<Lambda> ns x v \<in> U)"

definition dependent :: "'a absval_ty_fun \<Rightarrow> var_context \<Rightarrow> rtype_env \<Rightarrow> ('a nstate) set \<Rightarrow> vname set \<Rightarrow> bool" where
 "dependent A \<Lambda> \<Omega> U D = (\<forall>u \<in> U. 
                          (\<forall>d \<tau>. lookup_var_ty \<Lambda> d = Some \<tau> \<longrightarrow>
                            (lookup_var_ty_match A \<Lambda> \<Omega> u d \<tau>) \<and>                          
                            (d \<notin> D \<longrightarrow> closed_set_ty A \<Lambda> \<Omega> U u d \<tau>)))"

lemma dependent_ext: 
  assumes "D \<subseteq> D'" and "dependent A \<Lambda> \<Omega> U D"
  shows "dependent A \<Lambda> \<Omega> U D'"
  using assms
  unfolding dependent_def
  by blast

definition set_red_cmd :: "'a absval_ty_fun \<Rightarrow> method_context \<Rightarrow> var_context \<Rightarrow> 'a fun_interp \<Rightarrow> rtype_env \<Rightarrow> cmd \<Rightarrow> 'a nstate set \<Rightarrow> 'a state set"
  where "set_red_cmd A M \<Lambda> \<Gamma> \<Omega> c N = {s. \<exists>n_s. n_s \<in> N \<and> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>c, Normal n_s\<rangle> \<rightarrow> s}"

fun push_old_expr :: "bool \<Rightarrow> expr \<Rightarrow> expr"
  where 
    "push_old_expr True (Var x)  = Old (Var x)"
  | "push_old_expr False (Var x)  = (Var x)"
  | "push_old_expr _ (BVar i) = BVar i"
  | "push_old_expr _ (Lit l) = Lit l"
  | "push_old_expr b (UnOp unop e) = UnOp unop (push_old_expr b e)"
  | "push_old_expr b (e1 \<guillemotleft>bop\<guillemotright> e2) = (push_old_expr b e1) \<guillemotleft>bop\<guillemotright> (push_old_expr b e2)"
  | "push_old_expr b (FunExp f ts args) = FunExp f ts (map (push_old_expr b) args)"
  | "push_old_expr b (Old e) = push_old_expr True e"
  | "push_old_expr b (Forall ty e) = Forall ty (push_old_expr b e)"
  | "push_old_expr b (Exists ty e) = Exists ty (push_old_expr b e)"
  | "push_old_expr b (ForallT e) = ForallT (push_old_expr b e)"
  | "push_old_expr b (ExistsT e) = ExistsT (push_old_expr b e)"

lemma push_old_true_same: "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e, ns\<rangle> \<Down> v \<Longrightarrow> ns = ns'\<lparr>global_state := old_global_state ns'\<rparr> \<Longrightarrow> A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>push_old_expr True e, ns'\<rangle> \<Down> v"
and "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>es, ns\<rangle> [\<Down>] vs \<Longrightarrow> ns = ns'\<lparr>global_state := old_global_state ns'\<rparr> \<Longrightarrow> A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>map (push_old_expr True) es, ns'\<rangle> [\<Down>] vs"
  by (induction arbitrary: ns' and ns' rule: red_expr_red_exprs.inducts, auto intro: red_expr_red_exprs.intros)

lemma push_old_false_same: "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e, ns\<rangle> \<Down> v \<Longrightarrow> A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>push_old_expr False e, ns\<rangle> \<Down> v"
and "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>es, ns\<rangle> [\<Down>] vs \<Longrightarrow> A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>map (push_old_expr False) es, ns\<rangle> [\<Down>] vs"
proof (induction rule: red_expr_red_exprs.inducts)
  case (RedOld \<Omega> e n_s v)
  thus ?case 
    apply simp
    apply (erule push_old_true_same)
    by simp
qed (auto intro: red_expr_red_exprs.intros)

fun is_not_var :: "expr \<Rightarrow> bool"
  where 
    "is_not_var (Var _) = False"
  | "is_not_var _ = True"


text \<open> Expression relation \<close>
text \<open> R: active variable relation, 
       R_old: old global variable to passive variable relation, 
       loc_vars: parameters and locals \<close>
inductive expr_rel :: "passive_rel \<Rightarrow> passive_rel \<Rightarrow> vdecls \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> bool" and 
 expr_list_rel :: "passive_rel \<Rightarrow> passive_rel \<Rightarrow> vdecls \<Rightarrow> expr list \<Rightarrow> expr list \<Rightarrow> bool"
  for R :: passive_rel and R_old :: passive_rel and loc_vars :: vdecls
  where    
   Var_Rel: "R x1 = Some (Inl x2) \<Longrightarrow> expr_rel R R_old loc_vars (Var x1) (Var x2)"
 | Var_Const_Rel: "R x1 = Some (Inr l) \<Longrightarrow> expr_rel R R_old loc_vars (Var x1) (Lit l)"
 | BVar_Rel: "expr_rel R R_old loc_vars (BVar i) (BVar i)"
 | Lit_Rel: "expr_rel R R_old loc_vars (Lit lit) (Lit lit)"
 | UnOp_Rel: "expr_rel R R_old loc_vars e1 e2 \<Longrightarrow> expr_rel R R_old loc_vars (UnOp uop e1) (UnOp uop e2)"
 | BinOp_Rel: "\<lbrakk> expr_rel R R_old loc_vars e11 e21; expr_rel R R_old loc_vars e12 e22 \<rbrakk> \<Longrightarrow> 
              expr_rel R R_old loc_vars (e11 \<guillemotleft>bop\<guillemotright> e12) (e21 \<guillemotleft>bop\<guillemotright> e22)"
 | FunExp_Rel: "\<lbrakk> expr_list_rel R R_old loc_vars args1 args2 \<rbrakk>  \<Longrightarrow> 
              expr_rel R R_old loc_vars (FunExp f ts args1) (FunExp f ts args2)"
 | OldGlobalVar_Rel: "\<lbrakk>R_old x = Some (Inl y)\<rbrakk> \<Longrightarrow>
              expr_rel R R_old loc_vars (Old (Var x)) (Var y)"
 | OldLocalVar_Rel: "\<lbrakk>map_of loc_vars x = Some v; expr_rel R R_old loc_vars (Var x) (Var y)\<rbrakk> \<Longrightarrow> 
              expr_rel R R_old loc_vars (Old (Var x)) (Var y)"
 | OldExp_Rel: "\<lbrakk> is_not_var e1; expr_rel R R_old loc_vars (push_old_expr False (Old e1)) e2 \<rbrakk>  \<Longrightarrow> 
              expr_rel R R_old loc_vars (Old e1) e2"
 | Forall_Rel: "\<lbrakk> expr_rel R R_old loc_vars e1 e2 \<rbrakk> \<Longrightarrow> 
              expr_rel R R_old loc_vars (Forall ty e1) (Forall ty e2)"
 | Exists_Rel: "\<lbrakk> expr_rel R R_old loc_vars e1 e2 \<rbrakk> \<Longrightarrow> 
              expr_rel R R_old loc_vars (Exists ty e1) (Exists ty e2)"
 | ForallT_Rel: "\<lbrakk> expr_rel R R_old loc_vars e1 e2 \<rbrakk> \<Longrightarrow> 
              expr_rel R R_old loc_vars (ForallT e1) (ForallT e2)"
 | ExistsT_Rel: "\<lbrakk> expr_rel R R_old loc_vars e1 e2 \<rbrakk> \<Longrightarrow> 
             expr_rel R R_old loc_vars (ExistsT e1) (ExistsT e2)"
 | Nil_Rel: "expr_list_rel R R_old loc_vars [] []"
 | Cons_Rel: "\<lbrakk>expr_rel R R_old loc_vars x y; expr_list_rel R R_old loc_vars xs ys\<rbrakk> \<Longrightarrow>
              expr_list_rel R R_old loc_vars (x#xs) (y#ys)"

(*
method expr_rel_tac uses R_def = 
  (match conclusion in "expr_rel ?R (Var ?x1) (Var ?x2)" \<Rightarrow> \<open>rule, solves \<open>simp add: R_def\<close>\<close> \<bar>
                       "expr_rel ?R ?e1 ?e2" \<Rightarrow> rule  \<bar>
                       "expr_list_rel ?R ?es1 ?es2" \<Rightarrow> rule \<bar> 
                       "_" \<Rightarrow> fail)+
*)

(* don't need to explicitly prove that constant has the declared type of the variable, since no 
corresponding variable is constrained in the passive program *)
definition rel_const_correct :: "var_context \<Rightarrow> passive_rel \<Rightarrow> 'a nstate \<Rightarrow> bool"
  where "rel_const_correct \<Lambda> R ns = 
           (\<forall> x l. R x = Some (Inr l) \<longrightarrow>
            ( lookup_var \<Lambda> ns x = Some (LitV l) ))"

definition rel_well_typed :: "'a absval_ty_fun \<Rightarrow> var_context \<Rightarrow> rtype_env \<Rightarrow> passive_rel \<Rightarrow> 'a nstate \<Rightarrow> bool"
  where "rel_well_typed A \<Lambda> \<Omega> R ns = (
           (\<forall> x y. R x = Some (Inl y) \<longrightarrow> 
             (\<exists>v \<tau>. lookup_var \<Lambda> ns x = Some v \<and> lookup_var_ty \<Lambda> x = Some \<tau> \<and> type_of_val A v = instantiate \<Omega> \<tau>)) \<and>
           (rel_const_correct \<Lambda> R ns))"

lemma rel_well_typed_update: 
  assumes "rel_well_typed A \<Lambda> \<Omega> R ns" and "lookup_var_ty \<Lambda> x = Some \<tau>" and "type_of_val A v = instantiate \<Omega> \<tau>"
  shows "rel_well_typed A \<Lambda> \<Omega> (R(x \<mapsto> (Inl x'))) (update_var \<Lambda> ns x v)"
  using assms
  unfolding rel_well_typed_def rel_const_correct_def 
  by simp

lemma rel_well_typed_update_const:
  assumes "rel_well_typed A \<Lambda> \<Omega> R ns"
  shows "rel_well_typed A \<Lambda> \<Omega> (R(x \<mapsto> Inr l)) (update_var \<Lambda> ns x (LitV l))"
  using assms
  unfolding rel_well_typed_def rel_const_correct_def
  by simp

definition nstate_old_rel :: "var_context \<Rightarrow> var_context \<Rightarrow> passive_rel \<Rightarrow> 'a nstate \<Rightarrow> 'a nstate \<Rightarrow> bool"
  where "nstate_old_rel \<Lambda> \<Lambda>' R ns1 ns2 = 
          (\<forall>x y.  R x = Some (Inl y) \<longrightarrow> 
                 (map_of (fst \<Lambda>) x \<noteq> None \<and> map_of (snd \<Lambda>) x = None) \<and>
                 (\<exists>v. (old_global_state ns1) x = Some v \<and> lookup_var \<Lambda>' ns2 y = Some v))"

definition nstate_rel :: "var_context \<Rightarrow> var_context \<Rightarrow> passive_rel \<Rightarrow> 'a nstate \<Rightarrow> 'a nstate \<Rightarrow> bool"
  where "nstate_rel \<Lambda> \<Lambda>' R ns1 ns2 = 
          ((\<forall>x y.  R x = Some (Inl y) \<longrightarrow> (lookup_var \<Lambda> ns1 x = lookup_var \<Lambda>' ns2 y))
            \<and> binder_state ns1 = binder_state ns2)"

definition nstate_rel_states :: "var_context \<Rightarrow> var_context \<Rightarrow> passive_rel \<Rightarrow> 'a nstate \<Rightarrow> 'a nstate set \<Rightarrow> bool"
  where "nstate_rel_states \<Lambda> \<Lambda>' R ns U \<equiv> \<forall>u \<in> U. nstate_rel \<Lambda> \<Lambda>' R ns u"

definition nstate_old_rel_states :: "var_context \<Rightarrow> var_context \<Rightarrow> passive_rel \<Rightarrow> 'a nstate \<Rightarrow> 'a nstate set \<Rightarrow> bool"
  where "nstate_old_rel_states \<Lambda> \<Lambda>' R ns U \<equiv> \<forall>u \<in> U. nstate_old_rel \<Lambda> \<Lambda>' R ns u"

lemma nstate_rel_update_const: "nstate_rel \<Lambda> \<Lambda>' R ns1 ns2 \<Longrightarrow> nstate_rel \<Lambda> \<Lambda>' (R(x \<mapsto> Inr l)) (update_var \<Lambda> ns1 x v) ns2"
  unfolding nstate_rel_def
  by (simp add: update_var_binder_same)

lemma nstate_rel_states_update_const: "nstate_rel_states \<Lambda> \<Lambda>' R ns1 U \<Longrightarrow> nstate_rel_states \<Lambda> \<Lambda>' (R(x \<mapsto> Inr l)) (update_var \<Lambda> ns1 x v) U"
  unfolding nstate_rel_states_def
  by (simp add: nstate_rel_update_const)

definition update_nstate_rel
  where "update_nstate_rel R upds  = R ((map fst upds) [\<mapsto>] (map snd upds))"

lemma lookup_nstate_rel: "R x = Some (Inl y) \<Longrightarrow> nstate_rel \<Lambda> \<Lambda>' R ns u \<Longrightarrow> rel_well_typed A \<Lambda> \<Omega> R ns \<Longrightarrow>
   lookup_var \<Lambda>' u y = Some (the (lookup_var \<Lambda> ns x))"
  unfolding nstate_rel_def rel_well_typed_def
  using option.exhaust_sel by force  

lemma lookup_nstates_rel: "u \<in> U \<Longrightarrow> nstate_rel_states \<Lambda> \<Lambda>' R ns U \<Longrightarrow>  rel_well_typed A \<Lambda> \<Omega> R ns \<Longrightarrow>
           R x = Some (Inl y) \<Longrightarrow> 
           lookup_var \<Lambda>' u y = Some (the (lookup_var \<Lambda> ns x))"
  unfolding nstate_rel_states_def
  using lookup_nstate_rel by blast

lemma update_var_nstate_rel:
  assumes Srel:"nstate_rel \<Lambda> \<Lambda>' R ns1 ns2" and
          "lookup_var \<Lambda>' ns2 x = Some v"
  shows "nstate_rel \<Lambda> \<Lambda>' (R(y \<mapsto> (Inl x))) (update_var \<Lambda> ns1 y v) ns2" 
proof (simp only: nstate_rel_def, rule conjI, rule allI, rule allI, rule impI)
  fix z1 z2
  assume Map:"(R(y \<mapsto> (Inl x))) z1 = Some (Inl z2)"
  show "lookup_var \<Lambda> (update_var \<Lambda> ns1 y v) z1 = lookup_var \<Lambda>' ns2 z2"
  proof (cases "z1 = y")
    case True
    then show ?thesis using Map \<open>lookup_var \<Lambda>' ns2 x = Some v\<close> by simp
  next
    case False
    then show ?thesis using Map Srel
      by (metis map_upd_Some_unfold nstate_rel_def update_var_other) 
  qed
next
  show "binder_state (update_var \<Lambda> ns1 y v) = binder_state ns2" using Srel 
    by (simp add: update_var_binder_same nstate_rel_def)    
qed

lemma update_nstate_rel_cons: "update_nstate_rel (R(x \<mapsto> x2)) Q = update_nstate_rel R ((x,x2)#Q)"
  unfolding update_nstate_rel_def
  by simp

lemma update_nstate_rel_nil: "update_nstate_rel R [] = R" 
  by (simp add: update_nstate_rel_def)

  
lemma update_rel_nstate_same_state:
  assumes Srel: "nstate_rel \<Lambda> \<Lambda>' R ns1 ns2" and "R x = Some (Inl x1)" and LookupEq:"lookup_var \<Lambda>' ns2 x1 = lookup_var \<Lambda>' ns2 x2"
  shows "nstate_rel \<Lambda> \<Lambda>' (R(x \<mapsto> (Inl x2))) ns1 ns2"
proof (unfold nstate_rel_def, rule+)
  fix arg y
  assume "(R(x \<mapsto> (Inl x2))) arg = Some (Inl y)"
  thus "lookup_var \<Lambda> ns1 arg = lookup_var \<Lambda>' ns2 y"
   using Srel \<open>R x = Some (Inl x1)\<close> LookupEq
   by (metis fun_upd_apply nstate_rel_def option.sel sum.inject(1))   
next
  from Srel show "binder_state ns1 = binder_state ns2" by (simp add: nstate_rel_def)
qed

lemma binder_update_nstate_rel: "nstate_rel \<Lambda> \<Lambda>' R ns1 ns2 \<Longrightarrow> (\<And>v. nstate_rel \<Lambda> \<Lambda>' R (full_ext_env ns1 v) (full_ext_env ns2 v))"
  unfolding nstate_rel_def
  apply (simp only: lookup_full_ext_env_same)
  by (simp add: binder_full_ext_env_same)

lemma binder_update_nstate_old_rel: "nstate_old_rel \<Lambda> \<Lambda>' R ns1 ns2 \<Longrightarrow> (\<And>v. nstate_old_rel \<Lambda> \<Lambda>' R (full_ext_env ns1 v) (full_ext_env ns2 v))"
  unfolding nstate_old_rel_def
  apply (simp only: lookup_full_ext_env_same)
  by (simp add: binder_full_ext_env_same)

lemma binder_update_rel_const: "rel_const_correct \<Lambda> R ns \<Longrightarrow> (\<And>v. rel_const_correct \<Lambda> R (full_ext_env ns v))"
  unfolding rel_const_correct_def
  by (simp only: lookup_full_ext_env_same) auto  

lemma old_global_var_red:
  assumes "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>Old (Var x),ns\<rangle> \<Down> v" and "map_of (snd \<Lambda>) x = None"
  shows "v = the (old_global_state ns x)"
  using assms
  apply cases
  by (auto split: option.split simp: lookup_var_def)

lemma old_local_var_red_2:
  assumes "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>Old (Var x),ns\<rangle> \<Down> v" and A2:"map_of (snd \<Lambda>) x \<noteq> None"
  shows "v = the (local_state ns x)"
  using assms
  apply cases
  apply (erule RedVar_case)
  by (auto split: option.split simp: lookup_var_def)

lemma old_local_var_red:
  assumes "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>Old (Var x),ns\<rangle> \<Down> v" and A2:"map_of (snd \<Lambda>) x \<noteq> None"
  shows "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>Var x,ns\<rangle> \<Down> v"
 (* using old_local_var_red[OF assms] *)
  using assms
  apply cases
  apply (erule RedVar_case)
  by (metis RedVar lookup_var_def nstate.ext_inject nstate.surjective nstate.update_convs(2) option.case_eq_if)
  
(*
lemma old_local_var_red:
  assumes "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>Old (Var x),ns\<rangle> \<Down> v" and A2:"map_of (fst \<Lambda>) x = None"
  shows "v = the (local_state ns x)"
  using assms
  apply cases
  apply (erule RedVar_case)
  unfolding lookup_var_def
  apply (auto split: option.split)
*)

lemma expr_rel_same:
  shows "expr_rel R R_old (snd \<Lambda>) e1 e2 \<Longrightarrow>
         rel_const_correct \<Lambda> R ns1 \<Longrightarrow> 
         nstate_rel \<Lambda> \<Lambda>' R ns1 ns2 \<Longrightarrow> 
         nstate_old_rel \<Lambda> \<Lambda>' R_old ns1 ns2 \<Longrightarrow>
         A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e1, ns1\<rangle> \<Down> v \<Longrightarrow> 
         A,\<Lambda>',\<Gamma>,\<Omega> \<turnstile> \<langle>e2, ns2\<rangle> \<Down> v" and
    "expr_list_rel R R_old (snd \<Lambda>) es1 es2 \<Longrightarrow>
     rel_const_correct \<Lambda> R ns1 \<Longrightarrow> 
     nstate_rel \<Lambda> \<Lambda>' R ns1 ns2 \<Longrightarrow> 
     nstate_old_rel \<Lambda> \<Lambda>' R_old ns1 ns2 \<Longrightarrow>
     A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>es1, ns1\<rangle> [\<Down>] vs \<Longrightarrow> 
     A,\<Lambda>',\<Gamma>,\<Omega> \<turnstile> \<langle>es2, ns2\<rangle> [\<Down>] vs" 
proof (induction arbitrary: v ns1 ns2 \<Omega> and vs ns1 ns2 \<Omega> rule: expr_rel_expr_list_rel.inducts)
next
  case (OldGlobalVar_Rel x y)  
  from \<open>R_old x = Some (Inl y)\<close> and \<open>nstate_old_rel \<Lambda> \<Lambda>' R_old ns1 ns2\<close>
  show ?case using old_global_var_red[OF \<open>A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>Old (Var x),ns1\<rangle> \<Down> v\<close>]
    by (metis RedVar nstate_old_rel_def option.sel)
next
  case (OldLocalVar_Rel x v')
  thus ?case
    using old_local_var_red[OF \<open> A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>Old (Var x),ns1\<rangle> \<Down> v\<close>] \<open>map_of (snd \<Lambda>) x = Some v'\<close>
    by auto   
next
  case (OldExp_Rel e1 e2)
  thus ?case
    using push_old_false_same by blast
next
  case (Var_Rel x1 x2)
  thus ?case  by (auto intro: red_expr_red_exprs.intros simp: nstate_rel_def)
next
  case (Var_Const_Rel x1 l)
  then show ?case by (auto intro: red_expr_red_exprs.intros simp: rel_const_correct_def)
next
  case (BVar_Rel x1 x2)
  thus ?case 
 by (auto intro: red_expr_red_exprs.intros simp: nstate_rel_def)
next
  case (Lit_Rel lit)
  then show ?case by (blast intro: red_expr_red_exprs.intros )
next
  case (UnOp_Rel e1 e2 uop)
  then show ?case by (blast intro: red_expr_red_exprs.intros)
next
  case (BinOp_Rel e11 e21 e12 e22 bop)
  then show ?case by (blast intro: red_expr_red_exprs.intros)
next
  case (FunExp_Rel args1 args2 f ts)
  then show ?case by (blast intro: red_expr_red_exprs.intros)
next
  case (Forall_Rel e1 e2 ty)
  hence RelExt:"\<And>v. nstate_rel \<Lambda> \<Lambda>' R (full_ext_env ns1 v) (full_ext_env ns2 v)" using binder_update_nstate_rel by blast
  from Forall_Rel have RelOldExt: "\<And>v. nstate_old_rel \<Lambda> \<Lambda>' R_old (full_ext_env ns1 v) (full_ext_env ns2 v)" using binder_update_nstate_old_rel by blast 
  from Forall_Rel have RelWtExt:"\<And>v. rel_const_correct \<Lambda> R (full_ext_env ns1 v)" using binder_update_rel_const by blast   
  from \<open>A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>Forall ty e1,ns1\<rangle> \<Down> v\<close>     
  show ?case
    by (cases; blast intro: red_expr_red_exprs.intros dest:Forall_Rel.IH(2)[OF RelWtExt RelExt RelOldExt])
next
  case (Exists_Rel e1 e2 ty)
  hence RelExt:"\<And>v. nstate_rel \<Lambda> \<Lambda>' R (full_ext_env ns1 v) (full_ext_env ns2 v)" using binder_update_nstate_rel by blast
  from Exists_Rel have RelOldExt: "\<And>v. nstate_old_rel \<Lambda> \<Lambda>' R_old (full_ext_env ns1 v) (full_ext_env ns2 v)" using binder_update_nstate_old_rel by blast 
  from Exists_Rel have RelWtExt:"\<And>v. rel_const_correct \<Lambda> R (full_ext_env ns1 v)" using binder_update_rel_const by blast 
  from \<open>A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>Exists ty e1,ns1\<rangle> \<Down> v\<close>
  show ?case
    by (cases; blast intro: red_expr_red_exprs.intros dest:Exists_Rel.IH(2)[OF RelWtExt RelExt RelOldExt])
next
  case (ForallT_Rel e1 e2)
  from \<open>A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>ForallT e1,ns1\<rangle> \<Down> v\<close>
  show ?case
    by cases (auto intro: red_expr_red_exprs.intros dest: ForallT_Rel.IH(2)[OF \<open>rel_const_correct \<Lambda> R ns1\<close> \<open>nstate_rel \<Lambda> \<Lambda>' R ns1 ns2\<close> \<open>nstate_old_rel \<Lambda> \<Lambda>' R_old ns1 ns2\<close>])
next
  case (ExistsT_Rel e1 e2)
  from \<open>A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>ExistsT e1,ns1\<rangle> \<Down> v\<close>
  show ?case
    by cases (auto intro: red_expr_red_exprs.intros dest: ExistsT_Rel.IH(2)[OF \<open>rel_const_correct \<Lambda> R ns1\<close> \<open>nstate_rel \<Lambda> \<Lambda>' R ns1 ns2\<close> \<open>nstate_old_rel \<Lambda> \<Lambda>' R_old ns1 ns2\<close>])
next
  case Nil_Rel
  then show ?case
    using RedExpListNil by blast 
next
  case (Cons_Rel x y xs ys)
  thus ?case
    by (blast elim: cons_exp_elim2 intro: red_expr_red_exprs.intros)
qed

lemma expr_rel_same_set:
  assumes "expr_rel R R_old (snd \<Lambda>) e1 e2" and 
          "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e1, ns1\<rangle> \<Down> v" and 
          "rel_const_correct \<Lambda> R ns1" and
          "nstate_rel_states \<Lambda> \<Lambda>' R ns1 U" and
          "nstate_old_rel_states \<Lambda> \<Lambda>' R_old ns1 U"
  shows "\<forall>u \<in> U. A,\<Lambda>',\<Gamma>,\<Omega> \<turnstile> \<langle>e2, u\<rangle> \<Down> v"
  using assms expr_rel_same unfolding nstate_rel_states_def nstate_old_rel_states_def by blast

fun varsInExpr :: "expr \<Rightarrow> vname set"
  where
   "varsInExpr (Lit _) = {}"
 | "varsInExpr (Var x) = {x}"
 | "varsInExpr (BVar i) = {}"
 | "varsInExpr (UnOp uop e) = varsInExpr(e)"
 | "varsInExpr (e1 \<guillemotleft>bop\<guillemotright> e2) = varsInExpr(e1) \<union> varsInExpr(e2)"
 | "varsInExpr (FunExp f ts args) = foldl (\<lambda> res e. res \<union> varsInExpr(e)) {} args"
 | "varsInExpr (Old e) = varsInExpr(e)"
 | "varsInExpr (Forall ty e) = varsInExpr(e)"
 | "varsInExpr (Exists ty e) = varsInExpr(e)"
 | "varsInExpr (ForallT e) = varsInExpr(e)"
 | "varsInExpr (ExistsT e) = varsInExpr(e)"

fun isPassive :: "cmd \<Rightarrow> bool"
  where
   "isPassive (Assign _ _) = False"
 | "isPassive (Havoc _) = False"
 | "isPassive (MethodCall _ _ _) = False"
 | "isPassive _ = True"

lemma passive_state_same:
  assumes Apassive:"isPassive c" and Ared:"A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>c, Normal ns\<rangle> \<rightarrow> Normal ns'"
  shows "ns' = ns"
  using Ared Apassive
  by (cases, auto)
  
lemma passive_states_propagate: 
  assumes "isPassive c"
  shows "\<forall>ns' \<in> {ns'. Normal ns' \<in> (set_red_cmd A M \<Lambda> \<Gamma> \<Omega> c U)}. A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>c, Normal ns'\<rangle> \<rightarrow> Normal ns'"
proof
  fix ns'
  assume "ns' \<in> {ns''. Normal ns'' \<in> (set_red_cmd A M \<Lambda> \<Gamma> \<Omega> c U)}"
  hence "Normal ns' \<in> (set_red_cmd A M \<Lambda> \<Gamma> \<Omega> c U)"
    by simp
  from this obtain ns where "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>c, Normal ns\<rangle> \<rightarrow> Normal ns'"
    by (auto simp add: set_red_cmd_def)
  moreover from this have "ns' = ns"
    by (rule passive_state_same[OF \<open>isPassive c\<close>])
  ultimately show "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>c,Normal ns'\<rangle> \<rightarrow> Normal ns'"
    by simp
qed

lemma passive_states_propagate_2:
  assumes "isPassive c" and "ns \<in> {ns'. Normal ns' \<in> (set_red_cmd A M \<Lambda> \<Gamma> \<Omega> c U)}"
  shows "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>c, Normal ns\<rangle> \<rightarrow> Normal ns"
  using assms
  by (simp add: passive_states_propagate)

lemma passive_states_subset:
  assumes "isPassive c"
  shows "{ns'. Normal ns' \<in> (set_red_cmd A M \<Lambda> \<Gamma> \<Omega> c U)} \<subseteq> U"
proof
  fix ns
  assume "ns \<in> {ns'. Normal ns' \<in> (set_red_cmd A M \<Lambda> \<Gamma> \<Omega> c U)}"
  from this obtain ns0 where "ns0 \<in> U" and "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>c, Normal ns0\<rangle> \<rightarrow> Normal ns"
    unfolding set_red_cmd_def by auto 
  moreover from this have "ns0 = ns" using passive_state_same[OF \<open>isPassive c\<close>] by blast
  ultimately show "ns \<in> U" by simp
qed

lemma assume_assign_dependent:
  assumes  DepU:"dependent A \<Lambda> \<Omega> U D" and
           "x \<notin> D" and
           Ared:"\<forall>ns' \<in> U. A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e2, ns'\<rangle> \<Down> v" (* could replace this by varsInExpr(e2) \<subseteq> D *)
         shows "dependent A \<Lambda> \<Omega> {ns'. Normal ns' \<in> (set_red_cmd A M \<Lambda> \<Gamma> \<Omega> (Assume ((Var x) \<guillemotleft>Eq\<guillemotright> e2)) U)} (D \<union> {x})"
               (is "dependent A \<Lambda> \<Omega> ?U' (D \<union> {x})")
  using assms
proof -
  have Apassive:"isPassive (Assume ((Var x) \<guillemotleft>Eq\<guillemotright> e2))" by simp
  show "dependent A \<Lambda> \<Omega> ?U' (D \<union> {x})"
    unfolding dependent_def closed_set_ty_def
  proof (rule ballI, rule allI, rule allI, rule impI, rule conjI[OF _ impI[OF allI[OF impI]]])
    fix u' d \<tau>
    assume "u' \<in> ?U'"
    assume LookupD:"lookup_var_ty \<Lambda> d = Some \<tau>"
    assume "u' \<in> ?U'"
    hence "u' \<in> U" using passive_states_subset isPassive.simps by blast
    thus "lookup_var_ty_match A \<Lambda> \<Omega> u' d \<tau>" using DepU LookupD 
      unfolding dependent_def lookup_var_ty_match_def
      by simp
  next
    fix u' y \<tau> w    
    assume "u' \<in> ?U'"
    hence "u' \<in> U" using passive_states_subset isPassive.simps by blast     
    from this have "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e2, u'\<rangle> \<Down> v" using Ared by auto
    from \<open>u' \<in> ?U'\<close> have "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>Assume (Var x \<guillemotleft>Eq\<guillemotright> e2), Normal u'\<rangle> \<rightarrow> Normal u'"
      using passive_states_propagate_2[OF Apassive] by blast

    from this obtain v' where "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>Var x, u'\<rangle> \<Down> v'" and "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e2, u'\<rangle> \<Down> v'"
      apply cases
      apply (erule RedBinOp_case)
      by auto
    hence "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>Var x, u'\<rangle> \<Down> v" using expr_eval_determ(1)[OF \<open>A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e2, u'\<rangle> \<Down> v\<close>]
      by auto
    hence "lookup_var \<Lambda> u' x = Some v" by auto 
    moreover assume "y \<notin> (D \<union> {x})"
    ultimately have "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>Var x, (update_var \<Lambda> u' y w)\<rangle> \<Down> v"      
      by (auto intro: RedVar)  
    assume \<open>lookup_var_ty \<Lambda> y = Some \<tau>\<close> and \<open>type_of_val A w = instantiate \<Omega> \<tau>\<close>
    with \<open>u' \<in> U\<close> \<open>y \<notin> (D \<union> {x})\<close> have "(update_var \<Lambda> u' y w) \<in> U" using DepU
      by (simp add: dependent_def closed_set_ty_def)      
    hence "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e2, update_var \<Lambda> u' y w\<rangle> \<Down> v" using Ared by auto
    with \<open>update_var \<Lambda> u' y w \<in> U\<close> \<open>A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>Var x, (update_var \<Lambda> u' y w)\<rangle> \<Down> v\<close> show "update_var \<Lambda> u' y w \<in> ?U'"
      by (auto intro!: red_cmd.intros red_expr_red_exprs.intros simp: set_red_cmd_def)
  qed
qed

lemma assume_assign_non_empty:
  assumes  Ared:"\<forall>ns' \<in> U.  A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e2, ns'\<rangle> \<Down> v" and
           TypeVal: "type_of_val A v = instantiate \<Omega> \<tau>" and
           LookupTy:"lookup_var_ty \<Lambda> x = Some \<tau>"
           "U \<noteq> {}" and
           DepU:"dependent A \<Lambda> \<Omega> U D" and 
           "x \<notin> D"           
  shows "{ns'. Normal ns' \<in> (set_red_cmd A M \<Lambda> \<Gamma> \<Omega> (Assume ((Var x) \<guillemotleft>Eq\<guillemotright> e2)) U)} \<noteq> {}"
        (is "?U' \<noteq> {}")
proof -
  from Ared \<open>U \<noteq> {}\<close> obtain u where "u \<in> U" and "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e2, u\<rangle> \<Down> v" by auto
  with \<open>x \<notin> D\<close> DepU TypeVal LookupTy have "update_var \<Lambda> u x v \<in> U" by (auto simp: dependent_def lookup_var_ty_match_def closed_set_ty_def)
  moreover from this have "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e2,update_var \<Lambda> u x v\<rangle> \<Down> v" by (auto simp: Ared)
  ultimately have "update_var \<Lambda> u x v \<in> ?U'"
    by (auto intro!: red_cmd.intros red_expr_red_exprs.intros simp: set_red_cmd_def)   
  thus ?thesis by auto
qed

lemma assume_reduction_args:
  assumes "ns'\<in> {ns'. Normal ns' \<in> (set_red_cmd A M \<Lambda> \<Gamma> \<Omega> (Assume ((Var x) \<guillemotleft>Eq\<guillemotright> e2)) U)}"
  (is "ns' \<in> ?U'")
  shows "\<exists>v. (A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>Var x, ns'\<rangle> \<Down> v) \<and> (A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e2, ns'\<rangle> \<Down> v)"
proof -
  have Apassive:"isPassive (Assume ((Var x) \<guillemotleft>Eq\<guillemotright> e2))" by simp
  from \<open>ns' \<in> ?U'\<close> have "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>Assume (Var x \<guillemotleft>Eq\<guillemotright> e2), Normal ns'\<rangle> \<rightarrow> Normal ns'"
    using passive_states_propagate_2[OF Apassive] by blast
  thus ?thesis
  apply (cases)
  apply (erule RedBinOp_case, rule, auto)
  done
qed

lemma assume_sync_nstate_rel:
  assumes "R x_orig = Some (Inl x1)" and
          Srel:"nstate_rel_states \<Lambda> \<Lambda>' R ns U" and 
          Rel_wt: "rel_well_typed A \<Lambda> \<Omega> R ns"
  shows "nstate_rel_states \<Lambda> \<Lambda>' (R(x_orig \<mapsto> (Inl x2))) ns {ns'. Normal ns' \<in> (set_red_cmd A M \<Lambda>' \<Gamma> \<Omega> (Assume ((Var x2) \<guillemotleft>Eq\<guillemotright> (Var x1))) U)}"
 (is "nstate_rel_states \<Lambda> \<Lambda>' (R(x_orig \<mapsto> (Inl x2))) ns ?U'")
proof (unfold nstate_rel_states_def, rule ballI)
  have Apassive:"isPassive (Assume ((Var x2) \<guillemotleft>Eq\<guillemotright> (Var x1)))" by simp
  fix u'
  assume "u' \<in> ?U'"
  hence "u' \<in> U" using passive_states_subset[OF Apassive] by blast
  with Srel have "nstate_rel \<Lambda> \<Lambda>' R ns u'" by (simp add: nstate_rel_states_def)
  let ?v = "(the (lookup_var \<Lambda> ns x_orig))"
  have "A,\<Lambda>',\<Gamma>,\<Omega> \<turnstile> \<langle>Var x1, u'\<rangle> \<Down> ?v"
    using lookup_nstate_rel[OF \<open>R x_orig = Some (Inl x1)\<close> \<open>nstate_rel \<Lambda> \<Lambda>' R ns u'\<close> Rel_wt]
    by (auto intro: RedVar)
  hence Lookup1:"lookup_var \<Lambda>' u' x1 = Some ?v" by auto
  from \<open>u' \<in> ?U'\<close> have "A,\<Lambda>',\<Gamma>,\<Omega> \<turnstile> \<langle>Var x2, u'\<rangle> \<Down> ?v" 
   using  expr_eval_determ(1)[OF \<open>A,\<Lambda>',\<Gamma>,\<Omega> \<turnstile> \<langle>Var x1, u'\<rangle> \<Down> ?v\<close>] assume_reduction_args by metis
  hence "lookup_var \<Lambda>' u' x2 = Some ?v" by auto
  thus "nstate_rel \<Lambda> \<Lambda>' (R(x_orig \<mapsto> (Inl x2))) ns u'"
    using Lookup1 update_rel_nstate_same_state[OF \<open>nstate_rel \<Lambda> \<Lambda>' R ns u'\<close> \<open>R x_orig = Some (Inl x1)\<close>] 
    by simp
qed

lemma assume_assign_nstate_rel:
  assumes Erel:"expr_rel R R_old (snd \<Lambda>) e1 e2" and
          "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e1, ns\<rangle> \<Down> v" and
          Rel:"nstate_rel_states \<Lambda> \<Lambda>' R ns U" and
          OldRel: "nstate_old_rel_states \<Lambda> \<Lambda>' R_old ns U" and
          CRel:"rel_const_correct \<Lambda> R ns"
  shows   "nstate_rel_states 
               \<Lambda> \<Lambda>' (R(x_orig \<mapsto> (Inl x))) (update_var \<Lambda> ns x_orig v) {ns'. Normal ns' \<in> (set_red_cmd A M \<Lambda>' \<Gamma> \<Omega> (Assume ((Var x) \<guillemotleft>Eq\<guillemotright> e2)) U)}" 
 (is "nstate_rel_states \<Lambda> \<Lambda>' (R(x_orig \<mapsto> (Inl x))) (update_var \<Lambda> ns x_orig v) ?U'")
proof (unfold nstate_rel_states_def, rule ballI)
  have Apassive:"isPassive (Assume ((Var x) \<guillemotleft>Eq\<guillemotright> e2))" by simp
  fix u'
  assume "u' \<in> ?U'"
  hence "u' \<in> U" using passive_states_subset[OF Apassive] by blast
  with Rel have Rel2:"nstate_rel \<Lambda> \<Lambda>' R ns u'" by (simp add: nstate_rel_states_def)
  from \<open>u' \<in> U\<close> and OldRel have OldRel2:"nstate_old_rel \<Lambda> \<Lambda>' R_old ns u'" by (simp add: nstate_old_rel_states_def)
  have "A,\<Lambda>',\<Gamma>,\<Omega> \<turnstile> \<langle>e2, u'\<rangle> \<Down> v" using expr_rel_same(1)[OF Erel CRel Rel2 OldRel2 \<open>A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e1, ns\<rangle> \<Down> v\<close>] by simp
  from \<open>u' \<in> ?U'\<close> have "A,\<Lambda>',\<Gamma>,\<Omega> \<turnstile> \<langle>Var x, u'\<rangle> \<Down> v" 
     using  expr_eval_determ(1)[OF \<open>A,\<Lambda>',\<Gamma>,\<Omega> \<turnstile> \<langle>e2, u'\<rangle> \<Down> v\<close>] assume_reduction_args by metis
  hence "lookup_var \<Lambda>' u' x = Some v" by auto
  from this show "nstate_rel \<Lambda> \<Lambda>' (R(x_orig \<mapsto> (Inl x))) (update_var \<Lambda> ns x_orig v) u'" 
    by (rule update_var_nstate_rel[OF \<open>nstate_rel \<Lambda> \<Lambda>' R ns u'\<close>])
qed

lemma single_assign_reduce:
  "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>Assign x e, Normal n_s\<rangle> \<rightarrow> s' \<Longrightarrow> \<exists>v. A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e, n_s\<rangle> \<Down> v"
  by (erule red_cmd.cases; auto)

lemma single_assign_reduce_2:
  "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>Assign x e, Normal n_s\<rangle> \<rightarrow> s' \<Longrightarrow>  
    (\<exists>v \<tau>. (lookup_var_ty \<Lambda> x = Some \<tau>) \<and> (A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e, n_s\<rangle> \<Down> v) \<and> type_of_val A v = instantiate \<Omega> \<tau>)"
  by (erule red_cmd.cases) auto

lemma assume_rel_normal:
  assumes Ared:"A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e1, ns\<rangle> \<Down> (BoolV True)" and
          Srel:"nstate_rel_states \<Lambda> \<Lambda>' R ns U" and 
          OldRel: "nstate_old_rel_states \<Lambda> \<Lambda>' R_old ns U" and
          Crel:"rel_const_correct \<Lambda> R ns" and
          Erel:"expr_rel R R_old (snd \<Lambda>) e1 e2"
        shows "\<And>u. u \<in> U \<Longrightarrow> A,M,\<Lambda>',\<Gamma>,\<Omega> \<turnstile> \<langle>Assume e2, Normal u\<rangle> \<rightarrow> Normal u"
proof -
  fix u
  assume "u \<in> U"
  with Srel OldRel have "nstate_rel \<Lambda> \<Lambda>' R ns u" and "nstate_old_rel \<Lambda> \<Lambda>' R_old ns u"    
      by (auto simp:  nstate_rel_states_def nstate_old_rel_states_def)
  with Ared Erel have "A,\<Lambda>',\<Gamma>,\<Omega> \<turnstile> \<langle>e2, u\<rangle> \<Down> (BoolV True)" using expr_rel_same Crel by blast
  thus "A,M,\<Lambda>',\<Gamma>,\<Omega> \<turnstile> \<langle>Assume e2,Normal u\<rangle> \<rightarrow> Normal u" by (auto intro: RedAssumeOk)
qed

lemma assume_rel_magic:
  assumes Ared:"A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e1, ns\<rangle> \<Down> (BoolV False)" and
          Srel:"nstate_rel_states \<Lambda> \<Lambda>' R ns U" and
          OldRel: "nstate_old_rel_states \<Lambda> \<Lambda>' R_old ns U" and
          Crel:"rel_const_correct \<Lambda> R ns" and
          Erel:"expr_rel R R_old (snd \<Lambda>) e1 e2"
  shows "\<And>u. u \<in> U \<Longrightarrow> A,M,\<Lambda>',\<Gamma>,\<Omega> \<turnstile> \<langle>Assume e2, Normal u\<rangle> \<rightarrow> Magic"
proof -
  fix u
  assume "u \<in> U"
  with Srel OldRel have "nstate_rel \<Lambda> \<Lambda>' R ns u" and "nstate_old_rel \<Lambda> \<Lambda>' R_old ns u"    
    by (auto simp:  nstate_rel_states_def nstate_old_rel_states_def)
  with Ared Erel have "A,\<Lambda>',\<Gamma>,\<Omega> \<turnstile> \<langle>e2, u\<rangle> \<Down> (BoolV False)" using expr_rel_same Crel by blast
  thus "A,M,\<Lambda>',\<Gamma>,\<Omega> \<turnstile> \<langle>Assume e2,Normal u\<rangle> \<rightarrow> Magic" by (auto intro: RedAssumeMagic)
qed

lemma assert_rel_normal:
  assumes Ared:"A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e1, ns\<rangle> \<Down> (BoolV True)" and
          Srel:"nstate_rel_states \<Lambda> \<Lambda>' R ns U" and 
          OldRel: "nstate_old_rel_states \<Lambda> \<Lambda>' R_old ns U" and
          Crel:"rel_const_correct \<Lambda> R ns" and
          Erel:"expr_rel R R_old (snd \<Lambda>) e1 e2"
  shows "{ns'. Normal ns' \<in> (set_red_cmd A M \<Lambda>' \<Gamma> \<Omega> (Assert e2) U)} = U" (is "?U' = U")
proof 
  have Apassive:"isPassive (Assert e2)" by simp
  show "?U' \<subseteq> U" by (rule passive_states_subset[OF Apassive])
next
  show "U \<subseteq> ?U'" 
  proof
    fix u
    assume "u \<in> U"
    with Srel OldRel have "nstate_rel \<Lambda> \<Lambda>' R ns u" and "nstate_old_rel \<Lambda> \<Lambda>' R_old ns u"    
      by (auto simp:  nstate_rel_states_def nstate_old_rel_states_def)
    with Ared Erel have "A,\<Lambda>',\<Gamma>,\<Omega> \<turnstile> \<langle>e2, u\<rangle> \<Down> (BoolV True)" using expr_rel_same Crel by blast
    with \<open>u \<in> U\<close> show "u \<in> ?U'"
      by (auto intro!: red_cmd.intros simp: set_red_cmd_def)
  qed
qed

lemma assert_rel_normal_2:
  assumes Ared:"A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e1, ns\<rangle> \<Down> (BoolV True)" and
          Srel:"nstate_rel_states \<Lambda> \<Lambda>' R ns U" and
          OldRel: "nstate_old_rel_states \<Lambda> \<Lambda>' R_old ns U" and
          Crel:"rel_const_correct \<Lambda> R ns" and
          Erel:"expr_rel R R_old (snd \<Lambda>) e1 e2"
        shows "\<And>u. u \<in> U \<Longrightarrow> A,M,\<Lambda>',\<Gamma>,\<Omega> \<turnstile> \<langle>Assert e2, Normal u\<rangle> \<rightarrow> Normal u"
proof -
  fix u
  assume "u \<in> U"
  with Srel OldRel have "nstate_rel \<Lambda> \<Lambda>' R ns u" and "nstate_old_rel \<Lambda> \<Lambda>' R_old ns u"    
    by (auto simp:  nstate_rel_states_def nstate_old_rel_states_def)
  with Ared Erel have "A,\<Lambda>',\<Gamma>,\<Omega> \<turnstile> \<langle>e2, u\<rangle> \<Down> (BoolV True)" using expr_rel_same Crel by blast
  thus "A,M,\<Lambda>',\<Gamma>,\<Omega> \<turnstile> \<langle>Assert e2,Normal u\<rangle> \<rightarrow> Normal u" by (auto intro: RedAssertOk)
qed

lemma assert_rel_failure:
  assumes Ared:"A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e1, ns\<rangle> \<Down> (BoolV False)" and
          Srel:"nstate_rel_states \<Lambda> \<Lambda>' R ns U" and
          OldRel: "nstate_old_rel_states \<Lambda> \<Lambda>' R_old ns U" and
          Crel:"rel_const_correct \<Lambda> R ns" and
          Erel:"expr_rel R R_old (snd \<Lambda>) e1 e2"
  shows "\<And>u. u \<in> U \<Longrightarrow> A,M,\<Lambda>',\<Gamma>,\<Omega> \<turnstile> \<langle>Assert e2, Normal u\<rangle> \<rightarrow> Failure"
proof -
  fix u
  assume "u \<in> U"
  with Srel OldRel have "nstate_rel \<Lambda> \<Lambda>' R ns u" and "nstate_old_rel \<Lambda> \<Lambda>' R_old ns u"    
      by (auto simp:  nstate_rel_states_def nstate_old_rel_states_def)
  with Ared Erel have "A,\<Lambda>',\<Gamma>,\<Omega> \<turnstile> \<langle>e2, u\<rangle> \<Down> (BoolV False)" using expr_rel_same Crel by blast
  thus "A,M,\<Lambda>',\<Gamma>,\<Omega> \<turnstile> \<langle>Assert e2,Normal u\<rangle> \<rightarrow> Failure" by (auto intro: RedAssertFail)
qed

lemma havoc_nstate_rel:
  assumes Srel:"nstate_rel_states \<Lambda> \<Lambda>' R ns U"
  shows   "nstate_rel_states 
               \<Lambda> \<Lambda>' (R(x_orig \<mapsto> (Inl x2))) (update_var \<Lambda> ns x_orig v) {u' \<in> U. lookup_var \<Lambda>' u' x2 = Some v}"
 (is "nstate_rel_states 
               \<Lambda> \<Lambda>' (R(x_orig \<mapsto> (Inl x2))) (update_var \<Lambda> ns x_orig v) ?U'")
  using assms
  unfolding nstate_rel_states_def
  by (simp add: update_var_nstate_rel)  

lemma havoc_dependent:
  assumes Dep: "dependent A \<Lambda> \<Omega> U D" and
          "x2 \<notin> D"
  shows "dependent A \<Lambda> \<Omega> {u' \<in> U. lookup_var \<Lambda> u' x2 = Some v} (D \<union> {x2})"
  using assms
  by (simp add: dependent_def lookup_var_ty_match_def closed_set_ty_def)

lemma havoc_non_empty:
  assumes Dep: "dependent A \<Lambda> \<Omega> U D" and "U \<noteq> {}" and
          "x2 \<notin> D" and
          "lookup_var_ty \<Lambda> x2 = Some \<tau>" and
          "type_of_val A v = instantiate \<Omega> \<tau>"
  shows "{u' \<in> U. lookup_var \<Lambda> u' x2 = Some v} \<noteq> {}"
  using assms
  by (metis (mono_tags, lifting) dependent_def closed_set_ty_def empty_iff equals0I mem_Collect_eq update_var_same)

(* evaluation of U on cs is in relation with s' *)
definition passive_sim 
  where "passive_sim A M \<Lambda> \<Lambda>' \<Gamma> \<Omega> cs s' R U \<equiv> 
              (\<forall>u \<in> U. \<exists>su. (A,M,\<Lambda>',\<Gamma>,\<Omega> \<turnstile> \<langle>cs, Normal u\<rangle> [\<rightarrow>] su) \<and> 
                       (s' = Failure \<longrightarrow> su = Failure) \<and>
                       (\<forall>ns'. s' = Normal ns' \<longrightarrow> (su = Normal u \<and> nstate_rel \<Lambda> \<Lambda>' R ns' u \<and> rel_well_typed A \<Lambda> \<Omega> R ns')))"


inductive passive_cmds_rel :: "vdecls \<Rightarrow> vname list \<Rightarrow> passive_rel \<Rightarrow> passive_rel \<Rightarrow> (vname \<times> (vname + lit)) list \<Rightarrow> cmd list \<Rightarrow> cmd list \<Rightarrow> bool"
  for loc_vars :: vdecls
  where 
    PAssignNormal: 
    "\<lbrakk> expr_rel R R_old loc_vars e1 e2; passive_cmds_rel loc_vars W (R(x1 \<mapsto> (Inl x2))) R_old Q cs1 cs2 \<rbrakk> \<Longrightarrow> 
        passive_cmds_rel loc_vars (x2#W) R R_old ((x1,(Inl x2))#Q) ((Assign x1 e1) # cs1) ((Assume ((Var x2) \<guillemotleft>Eq\<guillemotright> e2)) # cs2)"
  | PConst:
    " \<lbrakk> passive_cmds_rel loc_vars W (R(x1 \<mapsto> (Inr l))) R_old Q cs1 cs2 \<rbrakk> \<Longrightarrow>
       passive_cmds_rel loc_vars W R R_old ((x1, (Inr l))#Q) ((Assign x1 (Lit l))#cs1) cs2"
  | PAssert: 
    "\<lbrakk> expr_rel R R_old loc_vars e1 e2; passive_cmds_rel loc_vars W R R_old Q cs1 cs2 \<rbrakk> \<Longrightarrow> 
        passive_cmds_rel loc_vars W R R_old Q ((Assert e1) # cs1) ((Assert e2) # cs2)"
  | PAssumeNormal: 
    "\<lbrakk> expr_rel R R_old loc_vars e1 e2; passive_cmds_rel loc_vars W R R_old Q cs1 cs2 \<rbrakk> \<Longrightarrow> 
        passive_cmds_rel loc_vars W R R_old Q ((Assume e1) # cs1) ((Assume e2) # cs2)"
  | PHavoc: 
    "\<lbrakk> passive_cmds_rel loc_vars W (R(x \<mapsto> (Inl x'))) R_old Q cs1 cs2\<rbrakk> \<Longrightarrow> 
       passive_cmds_rel loc_vars (x'#W) R R_old ((x,(Inl x'))#Q) ((Havoc x) # cs1) cs2"
  | PSync:       
    "\<lbrakk> R x = Some (Inl x1); passive_cmds_rel loc_vars W (R(x \<mapsto> (Inl x2))) R_old Q [] cs \<rbrakk> \<Longrightarrow>
       passive_cmds_rel loc_vars (x2#W) R R_old ((x,(Inl x2))#Q) [] ((Assume ( (Var x2) \<guillemotleft>Eq\<guillemotright> (Var x1))) # cs)"
  | PNil: "passive_cmds_rel loc_vars [] R R_old [] [] []"

(*
method passive_rel_tac uses R_def = 
  (match conclusion in
                       "passive_cmds_rel ?W ?R ?Q [] []" \<Rightarrow> \<open>rule PNil\<close> \<bar>
                       "passive_cmds_rel ?W ?R ?Q ((Havoc ?x1)#?cs1) ?cs2" \<Rightarrow> \<open>rule PHavoc\<close> \<bar>
                       "passive_cmds_rel ?W ?R ?Q [] ?cs2" \<Rightarrow> \<open>rule PSync, solves \<open>simp add: R_def\<close>\<close>  \<bar>
                       "passive_cmds_rel ?W ?R ?Q ?cs1 ?cs2" \<Rightarrow> \<open>rule, solves \<open>expr_rel_tac R_def: R_def\<close>\<close> \<bar>                 
                       "_" \<Rightarrow> fail)+
*)

(* "semantic" block lemma *)
(*
lemma
  assumes "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs, Normal ns\<rangle> [\<rightarrow>] s'" (* source execution *) and
          "dependent \<Lambda> U0 D0" (* U0: set of input passive states, D0: constrained variables in U0 *) and 
          "U0 \<noteq> {}" and
          "nstate_rel_states \<Lambda> \<Lambda>' R ns U0" and
          "W \<inter> D0 = {}"          
  shows "\<exists> U1 \<subseteq> U0. U1 \<noteq> {} \<and> dependent \<Lambda> U1 (D0 \<union> W) \<and>
          (\<forall>u \<in> U1. \<exists>su. (A,M,\<Lambda>',\<Gamma>,\<Omega> \<turnstile> \<langle>cs', Normal u\<rangle> [\<rightarrow>] su) \<and> 
                 (s' = Failure \<longrightarrow> su = Failure) \<and>
                 (\<forall>ns'. s' = Normal ns' \<longrightarrow> (su = Normal u \<and> nstate_rel \<Lambda> \<Lambda>' [OutputRelation unclear here] ns' u)))"
  oops
*)

definition type_rel :: "var_context \<Rightarrow> var_context \<Rightarrow> (vname \<times> (vname + lit)) list \<Rightarrow> bool"
  where "type_rel \<Lambda> \<Lambda>' Q = list_all (\<lambda> t. 
                case (snd t) of
                 (Inl y) \<Rightarrow>  lookup_var_ty \<Lambda> (fst t) = lookup_var_ty \<Lambda>' y 
                | (Inr _) \<Rightarrow> True
                  ) Q"

  
(* helper lemma to prove semantic block lemma *)
lemma passification_block_lemma_aux:
  assumes 
          "passive_cmds_rel (snd \<Lambda>) W R R_old Q cs1 cs2" and
          "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs1, Normal ns\<rangle> [\<rightarrow>] s'" and          
          "dependent A \<Lambda>' \<Omega> U0 D0" and
          "nstate_rel_states \<Lambda> \<Lambda>' R ns U0" and
          "nstate_old_rel_states \<Lambda> \<Lambda>' R_old ns U0" and
          "rel_well_typed A \<Lambda> \<Omega> R ns" and
          "(set W) \<inter> D0 = {}" and
          "U0 \<noteq> {}" and
          "type_rel \<Lambda> \<Lambda>' Q" and
          "distinct W"
        shows "\<exists> U1 \<subseteq> U0. U1 \<noteq> {} \<and> dependent A \<Lambda>' \<Omega> U1 (D0 \<union> (set W)) \<and> passive_sim A M \<Lambda> \<Lambda>' \<Gamma> \<Omega> cs2 s' (update_nstate_rel R Q) U1"
  unfolding passive_sim_def
(*
  shows "\<exists> U1 \<subseteq> U0. U1 \<noteq> {} \<and> dependent \<Lambda>' U1 (D0 \<union> (set W)) \<and>
          (\<forall>u \<in> U1. \<exists>su. (A,M,\<Lambda>',\<Gamma>,\<Omega> \<turnstile> \<langle>cs2, Normal u\<rangle> [\<rightarrow>] su) \<and> 
                 (s' = Failure \<longrightarrow> su = Failure) \<and>
                 (\<forall>ns'. s' = Normal ns' \<longrightarrow> (su = Normal u \<and> nstate_rel \<Lambda> \<Lambda>' (update_nstate_rel R Q) ns' u)))" *)
  using assms
proof (induction arbitrary: ns U0 D0)
case (PAssignNormal R R_old e1 e2 W x1 x2 Q cs1 cs2)  (* TODO: share proof with case PSync *)
  hence "x2 \<notin> D0" and "rel_const_correct \<Lambda> R ns" by (auto simp: rel_well_typed_def)
  from \<open>A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>Assign x1 e1 # cs1,Normal ns\<rangle> [\<rightarrow>] s'\<close> obtain v1 \<tau>
    where RedE1:"A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e1,ns\<rangle> \<Down> v1" and LookupX1:"lookup_var_ty \<Lambda> x1 = Some \<tau>" and 
                TyV1:"type_of_val A v1 = instantiate \<Omega> \<tau>" by (meson RedCmdListCons_case single_assign_reduce_2)
  with expr_rel_same_set[OF \<open>expr_rel R R_old (snd \<Lambda>) e1 e2\<close> _ \<open>rel_const_correct \<Lambda> R ns\<close> \<open>nstate_rel_states \<Lambda> \<Lambda>' R ns U0\<close> \<open>nstate_old_rel_states \<Lambda> \<Lambda>' R_old ns U0\<close>]
  have RedE2:"\<forall>u\<in>U0. A, \<Lambda>',\<Gamma>,\<Omega> \<turnstile> \<langle>e2,u\<rangle> \<Down> v1" by blast  
  from LookupX1 have LookupX2:"lookup_var_ty \<Lambda>' x2 = Some \<tau>" using \<open>type_rel \<Lambda> \<Lambda>' ((x1, (Inl x2)) # Q)\<close> by (simp add: type_rel_def)
  let ?U1 = "(set_red_cmd A M \<Lambda>' \<Gamma> \<Omega> (Assume ((Var x2) \<guillemotleft>Eq\<guillemotright> e2)) U0)"
  let ?U1Normal = "{ns. Normal ns \<in> ?U1}"   
  have U1Sub:"?U1Normal \<subseteq> U0"
    by (simp add: passive_states_subset) 
  have U1NonEmpty: "?U1Normal \<noteq> {}" using \<open>U0 \<noteq> {}\<close> \<open>x2 \<notin> D0\<close> \<open>dependent A \<Lambda>' \<Omega> U0 D0\<close> RedE2 TyV1 LookupX2
    by (blast dest: assume_assign_non_empty)
  have U1Dep: "dependent A \<Lambda>' \<Omega> ?U1Normal (D0 \<union> {x2})" using \<open>x2 \<notin> D0\<close> \<open>dependent A \<Lambda>' \<Omega> U0 D0\<close> RedE2    
    by (blast dest:  assume_assign_dependent)
    have RelStates: "nstate_rel_states \<Lambda> \<Lambda>' (R(x1 \<mapsto> (Inl x2))) (update_var \<Lambda> ns x1 v1) ?U1Normal"
      using \<open>nstate_rel_states \<Lambda> \<Lambda>' R ns U0\<close> \<open>nstate_old_rel_states \<Lambda> \<Lambda>' R_old ns U0\<close> \<open>expr_rel R R_old (snd \<Lambda>) e1 e2\<close> \<open>rel_const_correct \<Lambda> R ns\<close> RedE1
      by (blast dest: assume_assign_nstate_rel)
    have RelOldStates: "nstate_old_rel_states \<Lambda> \<Lambda>' R_old (update_var \<Lambda> ns x1 v1) ?U1Normal"
      using \<open>nstate_old_rel_states \<Lambda> \<Lambda>' R_old ns U0\<close> U1Sub 
  from \<open>distinct (x2 # W)\<close> \<open>set (x2 # W) \<inter> D0 = {}\<close> have "distinct W" and "set W \<inter> (D0 \<union> {x2}) = {}" by auto
  from \<open>A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>Assign x1 e1 # cs1,Normal ns\<rangle> [\<rightarrow>] s'\<close> have RedCs1:\<open>A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs1, Normal (update_var \<Lambda> ns x1 v1)\<rangle> [\<rightarrow>] s'\<close>
    by (metis RedCmdListCons_case RedE1 expr_eval_determ(1) single_assign_cases)
  have RedAssume: "\<And>u. u \<in> ?U1Normal \<Longrightarrow> A,M,\<Lambda>',\<Gamma>,\<Omega> \<turnstile> \<langle>Assume ((Var x2) \<guillemotleft>Eq\<guillemotright> e2),Normal u\<rangle> \<rightarrow> Normal u"    
    by (rule passive_states_propagate_2) simp
  from \<open>type_rel \<Lambda> \<Lambda>' ((x1, (Inl x2)) # Q)\<close> have QTyRel:"type_rel \<Lambda> \<Lambda>' Q" by (simp add: type_rel_def)
  from \<open>rel_well_typed A \<Lambda> \<Omega> R ns\<close> have Rel_wt:\<open>rel_well_typed A \<Lambda> \<Omega> (R(x1 \<mapsto> (Inl x2))) (update_var \<Lambda> ns x1 v1)\<close> using LookupX1 TyV1    
    by (blast dest: rel_well_typed_update)
  from PAssignNormal.IH[OF RedCs1 U1Dep RelStates Rel_wt \<open>set W \<inter> (D0 \<union> {x2}) = {}\<close>  U1NonEmpty QTyRel \<open>distinct W\<close>] obtain U2 where
    U2Sub:"U2 \<subseteq> ?U1Normal" and
    "U2 \<noteq> {}" and U2Dep:"dependent A \<Lambda>' \<Omega> U2 (D0 \<union> {x2} \<union> set W)" and
    U2Rel:"(\<forall>u\<in>U2.
         \<exists>su. (A,M,\<Lambda>',\<Gamma>,\<Omega> \<turnstile> \<langle>cs2,Normal u\<rangle> [\<rightarrow>] su) \<and>
              (s' = Failure \<longrightarrow> su = Failure) \<and> 
              (\<forall>ns'. s' = Normal ns' \<longrightarrow> su = Normal u \<and> nstate_rel \<Lambda> \<Lambda>' (update_nstate_rel (R(x1 \<mapsto> (Inl x2))) Q) ns' u \<and> rel_well_typed A \<Lambda> \<Omega> (update_nstate_rel (R(x1 \<mapsto> (Inl x2))) Q) ns'))"
    by blast
  hence U2Sub':"U2 \<subseteq> U0" and  U2Dep':"dependent A \<Lambda>' \<Omega> U2 (D0 \<union> set (x2 # W))" and 
        RedAssume2:"\<And>u. u \<in> U2 \<Longrightarrow> A,M,\<Lambda>',\<Gamma>,\<Omega> \<turnstile> \<langle>Assume ((Var x2) \<guillemotleft>Eq\<guillemotright> e2),Normal u\<rangle> \<rightarrow> Normal u" using U1Sub RedAssume by auto
   show ?case 
    apply (rule exI, intro conjI, rule U2Sub', rule \<open>U2 \<noteq> {}\<close>, rule U2Dep', rule ballI)
     using U2Rel RedAssume2 update_nstate_rel_cons
     by (metis RedCmdListCons)
next
  case (PConst W R x1 l Q cs1 cs2)
  let ?ns' = "(update_var \<Lambda> ns x1 (LitV l))"
  from \<open>A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>Assign x1 (Lit l) # cs1,Normal ns\<rangle> [\<rightarrow>] s'\<close> have
      RedCs1:\<open>A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs1,Normal ?ns'\<rangle> [\<rightarrow>] s'\<close>       
    by (metis RedCmdListCons_case single_assign_cases val_elim)
  from \<open>nstate_rel_states \<Lambda> \<Lambda>' R ns U0\<close> have RelStates:"nstate_rel_states \<Lambda> \<Lambda>' (R(x1 \<mapsto> Inr l)) ?ns' U0" by (simp add: nstate_rel_states_update_const)  
  from \<open>rel_well_typed A \<Lambda> \<Omega> R ns\<close> have Rel_wt:"rel_well_typed A \<Lambda> \<Omega> (R(x1 \<mapsto> Inr l)) ?ns'" by (simp add: rel_well_typed_update_const)
  from \<open>type_rel \<Lambda> \<Lambda>' ((x1, Inr l) # Q)\<close> have QTyRel:"type_rel \<Lambda> \<Lambda>' Q" by (simp add: type_rel_def)

  from PConst.IH[OF RedCs1 \<open>dependent A \<Lambda>' \<Omega> U0 D0\<close> RelStates Rel_wt _ _ QTyRel] obtain U1 where
    "U1 \<subseteq> U0" and "U1 \<noteq> {}" and "dependent A \<Lambda>' \<Omega> U1 (D0 \<union> set W)" and
    "(\<forall>u\<in>U1.
         \<exists>su. (A,M,\<Lambda>',\<Gamma>,\<Omega> \<turnstile> \<langle>cs2,Normal u\<rangle> [\<rightarrow>] su) \<and>
              (s' = Failure \<longrightarrow> su = Failure) \<and>
              (\<forall>ns'. s' = Normal ns' \<longrightarrow>
                     su = Normal u \<and>
                     nstate_rel \<Lambda> \<Lambda>' (update_nstate_rel (R(x1 \<mapsto> Inr l)) Q) ns' u \<and> rel_well_typed A \<Lambda> \<Omega> (update_nstate_rel (R(x1 \<mapsto> Inr l)) Q) ns'))"
    using PConst by blast    
  then show ?case using update_nstate_rel_cons
    by metis
next
  case (PAssert R e1 e2 W Q cs1 cs2)
  hence "rel_const_correct \<Lambda> R ns" by (simp add: rel_well_typed_def)
  from \<open>A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>Assert e1 # cs1,Normal ns\<rangle> [\<rightarrow>] s'\<close> obtain s'' where 
    RedAssert:"A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>Assert e1,Normal ns\<rangle> \<rightarrow> s''" and
    RedCs1:"A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs1, s''\<rangle> [\<rightarrow>] s'" 
    by blast
  from RedAssert show ?case
  proof cases
    case RedAssertOk
    hence RedE2:"\<And>u. u\<in>U0 \<Longrightarrow> A,M,\<Lambda>',\<Gamma>,\<Omega> \<turnstile> \<langle>Assert e2,Normal u\<rangle> \<rightarrow> Normal u"
      using assert_rel_normal_2 \<open>nstate_rel_states \<Lambda> \<Lambda>' R ns U0\<close> \<open>expr_rel R e1 e2\<close> \<open>rel_const_correct \<Lambda> R ns\<close> by blast
    from \<open>s'' = Normal ns\<close> RedCs1 have RedCs1Normal:"A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs1, Normal ns\<rangle> [\<rightarrow>] s'" by simp
    from PAssert.IH[OF RedCs1Normal \<open>dependent A \<Lambda>' \<Omega> U0 D0\<close>] obtain U1 
      where U1Sub: "U1 \<subseteq> U0" and "U1 \<noteq> {}" and U1Dep:"dependent A \<Lambda>' \<Omega> U1 (D0 \<union> set W)" and
       U1Rel:"(\<forall>u\<in>U1.
           \<exists>su. (A,M,\<Lambda>',\<Gamma>,\<Omega> \<turnstile> \<langle>cs2,Normal u\<rangle> [\<rightarrow>] su) \<and>
                (s' = Failure \<longrightarrow> su = Failure) \<and>
                (\<forall>ns'. s' = Normal ns' \<longrightarrow> su = Normal u \<and> nstate_rel \<Lambda> \<Lambda>' (update_nstate_rel R Q) ns' u \<and> rel_well_typed A \<Lambda> \<Omega> (update_nstate_rel R Q) ns') )"
      using PAssert.prems by auto
    show ?thesis 
      apply (rule exI, intro conjI)
         apply (rule U1Sub)
        apply (rule \<open>U1 \<noteq> {}\<close>)
       apply (rule U1Dep)
      using U1Sub RedE2 U1Rel
      by (meson RedCmdListCons subsetD)
  next
    case RedAssertFail
    hence RedE2:"\<And>u. u\<in>U0 \<Longrightarrow> A,M,\<Lambda>',\<Gamma>,\<Omega> \<turnstile> \<langle>Assert e2,Normal u\<rangle> \<rightarrow> Failure" 
      using assert_rel_failure \<open>nstate_rel_states \<Lambda> \<Lambda>' R ns U0\<close> \<open>expr_rel R e1 e2\<close> \<open>rel_const_correct \<Lambda> R ns\<close> by blast
    from  \<open>s'' = Failure\<close> have "s' = Failure" using RedCs1
      by (simp add: failure_stays_cmd_list)
    show ?thesis
      apply (rule exI, intro conjI, rule subset_refl)
      apply (rule \<open>U0 \<noteq> {}\<close>)
       apply (rule dependent_ext[OF _ \<open>dependent A \<Lambda>' \<Omega> U0 D0\<close>])
       apply simp
      using RedE2 \<open>s' = Failure\<close> failure_red_cmd_list RedCmdListCons by blast
  qed
next
  case (PAssumeNormal R e1 e2 W Q cs1 cs2)
  hence "rel_const_correct \<Lambda> R ns" by (simp add: rel_well_typed_def)
  from \<open>A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>Assume e1 # cs1,Normal ns\<rangle> [\<rightarrow>] s'\<close> obtain s'' where 
    RedAssume:"A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>Assume e1,Normal ns\<rangle> \<rightarrow> s''" and
    RedCs1:"A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs1, s''\<rangle> [\<rightarrow>] s'" 
    by blast
  from RedAssume show ?case
  proof cases
    case RedAssumeOk
    hence RedE2:"\<And>u. u\<in>U0 \<Longrightarrow> A,M,\<Lambda>',\<Gamma>,\<Omega> \<turnstile> \<langle>Assume e2,Normal u\<rangle> \<rightarrow> Normal u"
      using assume_rel_normal \<open>nstate_rel_states \<Lambda> \<Lambda>' R ns U0\<close> \<open>expr_rel R e1 e2\<close> \<open>rel_const_correct \<Lambda> R ns\<close> by blast
    from \<open>s'' = Normal ns\<close> RedCs1 have RedCs1Normal:"A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs1, Normal ns\<rangle> [\<rightarrow>] s'" by simp
    from PAssumeNormal.IH[OF RedCs1Normal \<open>dependent A \<Lambda>' \<Omega> U0 D0\<close>] obtain U1 
      where U1Sub: "U1 \<subseteq> U0" and "U1 \<noteq> {}" and U1Dep:"dependent A \<Lambda>' \<Omega> U1 (D0 \<union> set W)" and
       U1Rel:"(\<forall>u\<in>U1.
           \<exists>su. (A,M,\<Lambda>',\<Gamma>,\<Omega> \<turnstile> \<langle>cs2,Normal u\<rangle> [\<rightarrow>] su) \<and>
                (s' = Failure \<longrightarrow> su = Failure) \<and>
                (\<forall>ns'. s' = Normal ns' \<longrightarrow> su = Normal u \<and> nstate_rel \<Lambda> \<Lambda>' (update_nstate_rel R Q) ns' u \<and> rel_well_typed A \<Lambda> \<Omega> (update_nstate_rel R Q) ns'))"
      using PAssumeNormal.prems by auto
    show ?thesis 
      apply (rule exI, intro conjI)
         apply (rule U1Sub)
        apply (rule \<open>U1 \<noteq> {}\<close>)
       apply (rule U1Dep)
      using U1Sub RedE2 U1Rel
      by (meson RedCmdListCons subsetD)  
  next
    case RedAssumeMagic
    hence  RedE2:"\<And>u. u\<in>U0 \<Longrightarrow> A,M,\<Lambda>',\<Gamma>,\<Omega> \<turnstile> \<langle>Assume e2,Normal u\<rangle> \<rightarrow> Magic"
      using assume_rel_magic \<open>nstate_rel_states \<Lambda> \<Lambda>' R ns U0\<close> \<open>expr_rel R e1 e2\<close> \<open>rel_const_correct \<Lambda> R ns\<close> by blast
    from \<open>s'' = Magic\<close> have "s' = Magic" using RedCs1
      by (simp add: magic_stays_cmd_list) 
    show ?thesis 
      apply (rule exI, intro conjI, rule subset_refl)
        apply (rule \<open>U0 \<noteq> {}\<close>)
       apply (rule dependent_ext[OF _ \<open>dependent A \<Lambda>' \<Omega> U0 D0\<close>], simp)
      using RedE2 RedCmdListCons \<open>s' = Magic\<close> magic_red_cmd_list by blast
  qed 
next
  case (PHavoc W R x x' Q cs1 cs2)
  hence "x' \<notin> D0" and Disj:"set W \<inter> (D0 \<union> {x'}) = {}" and "distinct W" by auto
  from \<open>A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>Havoc x # cs1,Normal ns\<rangle> [\<rightarrow>] s'\<close> obtain v \<tau> where 
    RedCs1:"A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs1,Normal (update_var \<Lambda> ns x v)\<rangle> [\<rightarrow>] s'" and 
    LookupX:"lookup_var_ty \<Lambda> x = Some \<tau>" and TyV:"type_of_val A v = instantiate \<Omega> \<tau>"
    by (blast elim: havoc_cases_2)
  hence LookupX':"lookup_var_ty \<Lambda>' x' = Some \<tau>" using \<open>type_rel \<Lambda> \<Lambda>' ((x, (Inl x')) # Q)\<close> by (simp add: type_rel_def)
  let ?U1 = "{u' \<in> U0. lookup_var \<Lambda>' u' x' = Some v}"
  have DepU1:"dependent A \<Lambda>' \<Omega> ?U1 (D0 \<union> {x'})" and  "?U1 \<noteq> {}"
    using \<open>dependent A \<Lambda>' \<Omega> U0 D0\<close> \<open>x' \<notin> D0\<close> \<open>U0 \<noteq> {}\<close> LookupX' TyV
   by (blast dest: havoc_dependent havoc_non_empty)+

  have RelU1:"nstate_rel_states \<Lambda> \<Lambda>' (R(x \<mapsto> (Inl x'))) (update_var \<Lambda> ns x v) ?U1" using \<open>nstate_rel_states \<Lambda> \<Lambda>' R ns U0\<close>
    by (blast dest: havoc_nstate_rel)
  have U1Sub: "?U1 \<subseteq> U0" by auto
  from \<open>type_rel \<Lambda> \<Lambda>' ((x, Inl x') # Q)\<close> have QTyRel:"type_rel \<Lambda> \<Lambda>' Q" by (simp add: type_rel_def)
  from \<open>rel_well_typed A \<Lambda> \<Omega> R ns\<close> have Rel_wt:\<open>rel_well_typed A \<Lambda> \<Omega> (R(x \<mapsto> Inl x')) (update_var \<Lambda> ns x v)\<close>
    using LookupX TyV    
    by (blast dest: rel_well_typed_update)
  from PHavoc.IH[OF RedCs1 DepU1 RelU1 Rel_wt Disj \<open>?U1 \<noteq> {}\<close> QTyRel \<open>distinct W\<close>] obtain U2 where
       "U2 \<subseteq> ?U1" and "U2 \<noteq> {}" and
       "dependent A \<Lambda>' \<Omega> U2 (D0 \<union> {x'} \<union> set W)" and
       "(\<forall>u\<in>U2.
         \<exists>su. (A,M,\<Lambda>',\<Gamma>,\<Omega> \<turnstile> \<langle>cs2,Normal u\<rangle> [\<rightarrow>] su) \<and>
              (s' = Failure \<longrightarrow> su = Failure) \<and>
              (\<forall>ns'. s' = Normal ns' \<longrightarrow> su = Normal u \<and> nstate_rel \<Lambda> \<Lambda>' (update_nstate_rel (R(x \<mapsto> Inl x')) Q) ns' u \<and> rel_well_typed A \<Lambda> \<Omega> (update_nstate_rel (R(x \<mapsto> Inl x')) Q) ns'))"
    by blast 
  thus ?case    
    apply (simp)
    apply (rule exI[where ?x=U2], intro conjI)
       apply fastforce
      apply fastforce
     apply fastforce
    using update_nstate_rel_cons
    by (simp add: update_nstate_rel_cons)
next
  case (PSync R x x1 W x2 Q cs)
  hence "x2 \<notin> D0" by simp
  let ?U1 = "(set_red_cmd A M \<Lambda>' \<Gamma> \<Omega> (Assume ((Var x2) \<guillemotleft>Eq\<guillemotright> (Var x1))) U0)"
  let ?U1Normal = "{ns. Normal ns \<in> ?U1}"   
  have U1Sub:"?U1Normal \<subseteq> U0"
    by (simp add: passive_states_subset)
  from \<open>R x = Some (Inl x1)\<close> \<open>rel_well_typed A \<Lambda> \<Omega> R ns\<close> obtain v \<tau> where 
       LookupX:"lookup_var \<Lambda> ns x = Some v" and LookupTy:"lookup_var_ty \<Lambda> x = Some \<tau>" and TyV:"type_of_val A v = instantiate \<Omega> \<tau>" 
       by (auto simp: rel_well_typed_def)
  hence RedX1:"\<forall>u\<in>U0. A,\<Lambda>',\<Gamma>,\<Omega> \<turnstile> \<langle>Var x1,u\<rangle> \<Down> v"        
    using \<open>nstate_rel_states \<Lambda> \<Lambda>' R ns U0\<close> \<open>R x = Some (Inl x1)\<close> \<open>rel_well_typed A \<Lambda> \<Omega> R ns\<close> by (fastforce dest: lookup_nstates_rel intro: RedVar)
  from LookupTy have "lookup_var_ty \<Lambda>' x2 = Some \<tau>" using \<open>type_rel \<Lambda> \<Lambda>' ((x, Inl x2) # Q)\<close> by (simp add: type_rel_def)
  hence U1NonEmpty: "?U1Normal \<noteq> {}" using RedX1 \<open>U0 \<noteq> {}\<close> \<open>dependent A \<Lambda>' \<Omega> U0 D0\<close> \<open>x2 \<notin> D0\<close> TyV
    using  assume_assign_non_empty by (blast dest: assume_assign_non_empty)
  have U1Dep: "dependent A \<Lambda>' \<Omega> ?U1Normal (D0 \<union> {x2})"
    using \<open>dependent A \<Lambda>' \<Omega> U0 D0\<close> \<open>x2 \<notin> D0\<close> RedX1
    by (blast dest: assume_assign_dependent)
  have RelStates: "nstate_rel_states \<Lambda> \<Lambda>' (R(x \<mapsto> Inl x2)) ns ?U1Normal" 
    using \<open>nstate_rel_states \<Lambda> \<Lambda>' R ns U0\<close>  \<open>R x = Some (Inl x1)\<close> \<open>rel_well_typed A \<Lambda> \<Omega> R ns\<close> by (blast dest: assume_sync_nstate_rel)
  have RedAssume: "\<And>u. u \<in> ?U1Normal \<Longrightarrow> A,M,\<Lambda>',\<Gamma>,\<Omega> \<turnstile> \<langle>Assume ((Var x2) \<guillemotleft>Eq\<guillemotright> (Var x1)),Normal u\<rangle> \<rightarrow> Normal u"    
    by (rule passive_states_propagate_2) simp
  from \<open>distinct (x2 # W)\<close> \<open>set (x2 # W) \<inter> D0 = {}\<close> have "distinct W" and "set W \<inter> (D0 \<union> {x2}) = {}" by auto
  from \<open>type_rel \<Lambda> \<Lambda>' ((x, (Inl x2)) # Q)\<close> have QTyRel:"type_rel \<Lambda> \<Lambda>' Q" by (simp add: type_rel_def)
  from \<open>rel_well_typed A \<Lambda> \<Omega> R ns\<close> have Rel_wt:\<open>rel_well_typed A \<Lambda> \<Omega> (R(x \<mapsto> (Inl x2))) ns\<close> using \<open>R x = Some (Inl x1)\<close> by (simp add: rel_well_typed_def rel_const_correct_def)
  from PSync.IH[OF \<open>A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>[],Normal ns\<rangle> [\<rightarrow>] s'\<close> U1Dep RelStates Rel_wt \<open>set W \<inter> (D0 \<union> {x2}) = {}\<close> U1NonEmpty QTyRel \<open>distinct W\<close>]
  obtain U2 where 
      U2Sub:"U2 \<subseteq> ?U1Normal" and
      "U2 \<noteq> {}" and U2Dep:"dependent A \<Lambda>' \<Omega> U2 (D0 \<union> {x2} \<union> set W)" and
      U2Rel:
        "\<forall>u\<in>U2.
         \<exists>su. (A,M,\<Lambda>',\<Gamma>,\<Omega> \<turnstile> \<langle>cs,Normal u\<rangle> [\<rightarrow>] su) \<and>
              (s' = Failure \<longrightarrow> su = Failure) \<and> (\<forall>ns'. s' = Normal ns' \<longrightarrow> su = Normal u \<and>
              nstate_rel \<Lambda> \<Lambda>' (update_nstate_rel (R(x \<mapsto> Inl x2)) Q) ns' u \<and> rel_well_typed A \<Lambda> \<Omega> (update_nstate_rel (R(x \<mapsto> Inl x2)) Q) ns')"
    by blast
  hence U2Sub':"U2 \<subseteq> U0" and  U2Dep':"dependent A \<Lambda>' \<Omega> U2 (D0 \<union> set (x2 # W))" and 
    RedAssume2:"\<And>u. u \<in> U2 \<Longrightarrow> A,M,\<Lambda>',\<Gamma>,\<Omega> \<turnstile> \<langle>Assume ((Var x2) \<guillemotleft>Eq\<guillemotright> (Var x1)),Normal u\<rangle> \<rightarrow> Normal u"
      using U1Sub RedAssume by auto
  show ?case
    apply (rule exI, intro conjI, rule U2Sub', rule \<open>U2 \<noteq> {}\<close>, rule U2Dep', rule ballI)
    using U2Rel RedAssume2 update_nstate_rel_cons
    by (metis RedCmdListCons)  
next
  case (PNil R)
  then show ?case
    by (metis RedCmdListNil empty_set nstate_rel_states_def state.distinct(1) state.inject step_nil_same subset_refl sup_bot.right_neutral update_nstate_rel_nil) 
qed

definition passive_block_conclusion
  where "passive_block_conclusion A M \<Lambda> \<Lambda>' \<Gamma> \<Omega> U0 D1 R cs2 s' = 
  (\<exists> U1 \<subseteq> U0. U1 \<noteq> {} \<and> dependent A \<Lambda>' \<Omega> U1 D1 \<and> passive_sim A M \<Lambda> \<Lambda>' \<Gamma> \<Omega> cs2 s' R U1)"

definition passive_lemma_assms
  where "passive_lemma_assms A M \<Lambda> \<Lambda>' \<Gamma> \<Omega> W R U0 D0 cs1 ns s' = 
          (nstate_rel_states \<Lambda> \<Lambda>' R ns U0 \<and> rel_well_typed A \<Lambda> \<Omega> R ns \<and>
          dependent A \<Lambda>' \<Omega> U0 D0 \<and> (set W) \<inter> D0 = {} \<and>
          U0 \<noteq> {})"

lemma passification_block_lemma_compact:
  assumes 
          "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs1, Normal ns\<rangle> [\<rightarrow>] s'"
          "passive_lemma_assms A M \<Lambda> \<Lambda>' \<Gamma> \<Omega> W R U0 D0 cs1 ns s'" and
          "passive_cmds_rel W R Q cs1 cs2" and
          "type_rel \<Lambda> \<Lambda>' Q" and
          "distinct W"
  shows "passive_block_conclusion A M \<Lambda> \<Lambda>' \<Gamma> \<Omega> U0 (D0 \<union> (set W)) (update_nstate_rel R Q) cs2 s'"
  using assms
  unfolding passive_lemma_assms_def passive_block_conclusion_def
  using passification_block_lemma_aux by meson

text \<open>CFG proofs\<close>
definition passive_cfg_assms
  where "passive_cfg_assms A M \<Lambda> \<Lambda>' \<Gamma> \<Omega> G W R U0 D0 m m' ns s' = 
          ( (A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (m, Normal ns) -n\<rightarrow>* (m',s')) \<and>
           nstate_rel_states \<Lambda> \<Lambda>' R ns U0 \<and> rel_well_typed A \<Lambda> \<Omega> R ns \<and>
           dependent A \<Lambda>' \<Omega> U0 D0 \<and> (set W) \<inter> D0 = {} \<and>
          U0 \<noteq> {})"

definition passive_sim_cfg
  where "passive_sim_cfg A M \<Lambda>' \<Gamma> \<Omega> G U m_p s' \<equiv> 
              (\<forall>u \<in> U. \<exists> m_p' su. (A,M,\<Lambda>',\<Gamma>,\<Omega>, G \<turnstile> (m_p, Normal u) -n\<rightarrow>* (m_p',su)) \<and> 
                       (s' = Failure \<longrightarrow> su = Failure))"

(*
definition passive_cfg_conclusion
  where "passive_cfg_conclusion A M \<Lambda> \<Lambda>' \<Gamma> \<Omega> G U0 D1 R m m' s' = 
  (\<exists> U1 \<subseteq> U0. U1 \<noteq> {} \<and> dependent A \<Lambda>' \<Omega> U1 D1 \<and> passive_sim_cfg A M \<Lambda>' \<Gamma> \<Omega> G U1 m m' s')"

definition passive_cfg_lemma
  where "passive_cfg_lemma A M \<Lambda> \<Lambda>' \<Gamma> \<Omega> G W R U0 D0 m m' m_p m_p' ns s' =
          (passive_cfg_assms A M \<Lambda> \<Lambda>' \<Gamma> \<Omega> G W R U0 D0 m m' ns s' \<longrightarrow>
           passive_cfg_conclusion A M \<Lambda> \<Lambda>' \<Gamma> \<Omega> G U0 (D0 \<union> (set W)) R m_p m_p' s')"
*)

  
          
          

end