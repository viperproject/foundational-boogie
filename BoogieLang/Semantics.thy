section \<open>Semantics of the Boogie Language\<close>

theory Semantics
imports Lang BoogieDeBruijn
begin

subsection \<open>Values, State, Variable Context\<close>

text \<open>The values (and as a result the semantics) are parametrized by the carrier type 'a for the 
abstract values (values that have a type constructed via type constructors)\<close>
datatype 'a val = LitV lit | AbsV (the_absv: 'a)

abbreviation IntV where "IntV i \<equiv> LitV (LInt i)"
abbreviation BoolV where "BoolV b \<equiv> LitV (LBool b)"
abbreviation RealV where "RealV r \<equiv> LitV (LReal r)"

primrec is_lit_val :: "'a val \<Rightarrow> bool"
  where 
    "is_lit_val (LitV _) = True"
  | "is_lit_val (AbsV _) = False"

lemma lit_val_elim:
 "\<lbrakk> \<And>b. v = BoolV b \<Longrightarrow> P; \<And>i. v = IntV i \<Longrightarrow> P; \<And>r. v = RealV r \<Longrightarrow> P; \<And> a. v = AbsV a \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (metis lit.exhaust val.exhaust)

text \<open>We differentiate between DeBruijn variables (used for bound variales) and named variables. When we open 
a term in the semantics, we do not change the bound variable constructors (i.e., we treat bound 
variables as in the pure DeBruijn case). Opening a term happens for example, when one evaluates a
universal quantifier (recursing over the body of the quantifier without the quantifier itself is
called "opening"). As a result, we need a separate state in the semantics to track the bound variables 
that become temporarily free in the semantics.

We did not pick a pure DeBruijn approach, since it becomes a bit unnatural to differentiate local
and global variables. Moreover, we did not pick a locally nameless approach, since generating proofs
becomes cumbersome due to the free variable constraints when opening terms.\<close>

type_synonym 'a named_state = "vname \<rightharpoonup> 'a val"

record 'a nstate = 
  old_global_state :: "'a named_state"
  global_state :: "'a named_state" 
  local_state :: "'a named_state"
  binder_state :: "nat \<rightharpoonup> 'a val"

text \<open>
\<^const>\<open>old_global_state\<close> stores the global state (global variable mapping) 
as it was at the beginning of the procedure (required for old expressions).
\<^const>\<open>global_state\<close> stores the current global variable mapping.
\<^const>\<open>local_state\<close> stores the current parameter/local variable/return variable mapping.
\<^const>\<open>binder_state\<close> tracks the bound variables that become free (i.e., it is empty before and
after a program statement in practice).
\<close>

fun local_to_nstate :: "'a named_state \<Rightarrow> 'a nstate"
  where "local_to_nstate ls = \<lparr>old_global_state = Map.empty, global_state = Map.empty, local_state = ls, binder_state = Map.empty\<rparr>"

fun global_to_nstate :: "'a named_state => 'a nstate"
  where "global_to_nstate gs = \<lparr>old_global_state = Map.empty, global_state = gs, local_state = Map.empty, binder_state = Map.empty\<rparr>"

text\<open>Boogie program state\<close>
datatype 'a state = Normal "'a nstate" | Failure | Magic

text\<open>A variable context is a tuple of the global variable declarations and the local variable 
declarations (parameters, local variables, return variables) \<close>
type_synonym var_context = "vdecls \<times> vdecls"


subsection\<open>Variable lookup/update helper definitions and lemmas \<close>

definition lookup_var_decl :: "var_context \<Rightarrow> vname \<Rightarrow> (ty \<times> expr option) option"
  where 
    "lookup_var_decl \<Lambda> x = 
      (case (map_of (snd \<Lambda>) x) of Some t \<Rightarrow> Some t |
                                 None \<Rightarrow> map_of (fst \<Lambda>) x)"

text\<open>A local variable may shadow a global variable, as the variable declaration lookup function in
 \<^term>\<open>lookup_var_decl\<close> reflects. \<close>

definition lookup_var_ty :: "var_context \<Rightarrow> vname \<Rightarrow> ty option"
  where "lookup_var_ty \<Lambda> x = map_option fst (lookup_var_decl \<Lambda> x)"

definition lookup_vdecls_ty :: "vdecls \<Rightarrow> vname \<Rightarrow> ty option"
  where "lookup_vdecls_ty vs x = map_option fst (map_of vs x)"

lemma lookup_vdecls_ty_map_of: "lookup_vdecls_ty vs x = Some \<tau> \<Longrightarrow> \<exists>w. map_of vs x = Some (\<tau>,w)"
  by (simp add: lookup_vdecls_ty_def)

lemma map_of_lookup_vdecls_ty: "map_of vs x = Some tw \<Longrightarrow> lookup_vdecls_ty vs x = Some (fst tw)"
  by (simp add: lookup_vdecls_ty_def)

lemma lookup_var_decl_ty_Some: "lookup_var_decl \<Lambda> x = Some (\<tau>,w) \<Longrightarrow> lookup_var_ty \<Lambda> x = Some \<tau>"
  by (simp add: lookup_var_decl_def lookup_var_ty_def)

lemma lookup_var_decl_ty_None: "lookup_var_decl \<Lambda> x = None \<Longrightarrow> lookup_var_ty \<Lambda> x = None"
  by (simp add: lookup_var_decl_def lookup_var_ty_def)

lemma lookup_var_ty_decl_Some: "lookup_var_ty \<Lambda> x = Some \<tau> \<Longrightarrow> \<exists>w. lookup_var_decl \<Lambda> x = Some (\<tau>,w)"
  by (simp add: lookup_var_decl_def lookup_var_ty_def)

lemma lookup_var_ty_decl_None: "lookup_var_ty \<Lambda> x = None \<Longrightarrow> lookup_var_decl \<Lambda> x = None"
  by (simp add: lookup_var_decl_def lookup_var_ty_def)

definition lookup_var :: "var_context \<Rightarrow> 'a nstate \<Rightarrow> vname \<Rightarrow> 'a val option"
  where 
   "lookup_var \<Lambda> ns x = 
      (case (map_of (snd \<Lambda>) x) of Some res \<Rightarrow> local_state ns x |
                                 None \<Rightarrow> global_state ns x)"

text\<open>If variable does not exist, then the global state is updated (for well-typed programs this 
should not happen).\<close>
definition update_var :: "var_context \<Rightarrow> 'a nstate \<Rightarrow> vname \<Rightarrow> 'a val \<Rightarrow>  'a nstate"
  where 
   "update_var \<Lambda> n_s x v =
            (case (map_of (snd \<Lambda>) x) of Some res \<Rightarrow> n_s\<lparr>local_state := (local_state(n_s))(x \<mapsto> v) \<rparr>  |
                                 None \<Rightarrow> n_s\<lparr>global_state := (global_state(n_s))(x \<mapsto> v) \<rparr>)"

definition update_var_opt :: "var_context \<Rightarrow> 'a nstate \<Rightarrow> vname \<Rightarrow> 'a val option \<Rightarrow>  'a nstate"
  where 
   "update_var_opt \<Lambda> n_s x v =
            (case (map_of (snd \<Lambda>) x) of Some res \<Rightarrow> n_s\<lparr>local_state := (local_state(n_s))(x := v)\<rparr>  |
                                 None \<Rightarrow> n_s\<lparr>global_state := (global_state(n_s))(x := v) \<rparr>)"

lemma update_var_update_var_opt: "update_var \<Lambda> n_s x v = update_var_opt \<Lambda> n_s x (Some v)"
  by (auto simp: update_var_def update_var_opt_def)

fun full_ext_env :: "'a nstate \<Rightarrow> 'a val \<Rightarrow> 'a nstate"
  where "full_ext_env n_s v = n_s\<lparr> binder_state := ext_env (binder_state n_s) v \<rparr>"

lemma lookup_var_local: "map_of L x = Some ty \<Longrightarrow> lookup_var (G,L) n_s x = local_state n_s x"
  by (simp add: lookup_var_def split: option.split)

lemma lookup_var_global: "map_of L x = None \<Longrightarrow> lookup_var (G,L) n_s x = global_state n_s x"
  by (simp add: lookup_var_def split: option.split)

lemma lookup_var_binder_upd:
"lookup_var \<Lambda> (n_s\<lparr> binder_state := b \<rparr>) x  = lookup_var \<Lambda> n_s x"  by (simp add: lookup_var_def split: option.split)

lemma update_var_apply [simp]: "lookup_var \<Lambda> (update_var \<Lambda> n_s x v) y = (if x = y then Some v else lookup_var \<Lambda> n_s y)"
  unfolding update_var_def lookup_var_def
  by (simp split: option.split)

lemma update_var_opt_apply [simp]: "lookup_var \<Lambda> (update_var_opt \<Lambda> n_s x v) y = (if x = y then v else lookup_var \<Lambda> n_s y)"
  unfolding update_var_opt_def lookup_var_def
  by (simp split: option.split)

lemma update_var_same: "lookup_var \<Lambda> (update_var \<Lambda> n_s x v) x = Some v"
  unfolding update_var_def lookup_var_def
  by (simp split: option.split)

lemma update_var_other: "y \<noteq> x \<Longrightarrow> lookup_var \<Lambda> (update_var \<Lambda> n_s x v) y = lookup_var \<Lambda> n_s y"
  unfolding update_var_def lookup_var_def
  by (simp split: option.split)

lemma update_var_binder_same: "binder_state (update_var \<Lambda> n_s x v) = binder_state n_s"
  unfolding update_var_def
  by (simp split: option.split)

lemma update_var_old_global_same: "old_global_state (update_var \<Lambda> n_s x v) = old_global_state n_s"
  unfolding update_var_def
  by (simp split: option.split)

lemma update_var_opt_same: "lookup_var \<Lambda> (update_var_opt \<Lambda> n_s x v) x =  v"
  unfolding update_var_opt_def lookup_var_def
  by (simp split: option.split)

lemma update_var_opt_other: "y \<noteq> x \<Longrightarrow> lookup_var \<Lambda> (update_var_opt \<Lambda> n_s x v) y = lookup_var \<Lambda> n_s y"
  unfolding update_var_opt_def lookup_var_def
  by (simp split: option.split)

lemma local_state_update_other: "x \<noteq> d \<Longrightarrow> (local_state (update_var \<Lambda> u d v) x) = local_state u x"
  by (simp add: update_var_def split: option.split)

lemma global_state_update_other: "x \<noteq> d \<Longrightarrow> (global_state (update_var \<Lambda> u d v) x) = global_state u x"
  by (simp add: update_var_def split: option.split)

lemma global_state_update_local: "map_of (snd \<Lambda>) d = Some \<tau> \<Longrightarrow> global_state (update_var \<Lambda> u d v) = global_state u"
  by (simp add: update_var_def split: option.split)

lemma global_update: "map_of (snd \<Lambda>) d = None \<Longrightarrow> (global_state (update_var \<Lambda> u d v)) = (global_state u)(d \<mapsto> v)"
  by (simp add: update_var_def split: option.split)

lemma local_update: "map_of (snd \<Lambda>) d = Some t \<Longrightarrow> (local_state (update_var \<Lambda> u d v)) = (local_state u)(d \<mapsto> v)"
  by (simp add: update_var_def split: option.split)

lemma lookup_full_ext_env_same: "lookup_var \<Lambda> (full_ext_env ns v) x = lookup_var \<Lambda> ns x"
  by (simp add: lookup_var_binder_upd)

lemma lookup_var_decl_local: "map_of (snd \<Lambda>) x = Some t \<Longrightarrow> lookup_var_decl \<Lambda> x = Some t"
  by (simp add: lookup_var_decl_def split: option.split)

lemma lookup_var_decl_local_2: "map_of (snd \<Lambda>) x \<noteq> None \<Longrightarrow> lookup_var_decl \<Lambda> x = Some t \<Longrightarrow> map_of (snd \<Lambda>) x = Some t"
  by (fastforce simp: lookup_var_decl_def split: option.split)

lemma lookup_vdecls_ty_local_3: "lookup_vdecls_ty (snd \<Lambda>) x = Some t \<Longrightarrow> lookup_var_ty \<Lambda> x = Some t"
  using lookup_var_decl_local
  by (fastforce simp: lookup_var_ty_def lookup_vdecls_ty_def)

lemma lookup_var_decl_global: "map_of (fst \<Lambda>) x = Some t \<Longrightarrow> map_of (snd \<Lambda>) x = None \<Longrightarrow> lookup_var_decl \<Lambda> x = Some t"
  by (simp add: lookup_var_decl_def split: option.split)

lemma lookup_var_decl_global_2: 
  assumes Disj:"set (map fst (fst \<Lambda>)) \<inter> set (map fst (snd \<Lambda>)) = {}" and MemFst:"map_of (fst \<Lambda>) x = Some t"
  shows "lookup_var_decl \<Lambda> x = Some t"
  using assms lookup_var_decl_global 
  by (metis disjoint_iff image_set map_of_eq_None_iff option.distinct(1))
 
lemma lookup_var_decl_global_3:
  assumes "map_of (snd \<Lambda>) x = None" and "lookup_var_decl \<Lambda> x = Some \<tau>"
  shows "map_of (fst \<Lambda>) x = Some \<tau>"
  using assms
  unfolding lookup_var_decl_def
  by simp

lemma lookup_vdecls_ty_global_4: "map_of (snd \<Lambda>) x = None \<Longrightarrow> lookup_vdecls_ty (fst \<Lambda>) x = Some t \<Longrightarrow> lookup_var_ty \<Lambda> x = Some t"
  using lookup_var_decl_global  
  by (fastforce simp: lookup_var_ty_def lookup_vdecls_ty_def)

lemma lookup_vdecls_ty_global_5: "map_of (snd \<Lambda>) x = None \<Longrightarrow> lookup_var_ty \<Lambda> x = Some t \<Longrightarrow> lookup_vdecls_ty (fst \<Lambda>) x = Some t"
  using lookup_var_ty_def lookup_vdecls_ty_def
  by (metis lookup_var_ty_decl_Some lookup_var_decl_global_3)

lemma binder_full_ext_env_same: "binder_state ns1 = binder_state ns2 \<Longrightarrow> 
  binder_state (full_ext_env ns1 v) = binder_state (full_ext_env ns2 v)"
  by simp

lemma binder_state_local_upd_same: "binder_state (ns\<lparr>local_state := gs\<rparr>) = binder_state ns"
  by simp

subsection \<open>Binary operation helper definitions\<close>

fun binop_less :: "lit \<Rightarrow> lit \<rightharpoonup> lit"
  where
    "binop_less (LInt i1) (LInt i2) = Some (LBool (i1 < i2))"
  | "binop_less (LReal r1) (LReal r2) = Some (LBool (r1 < r2))"
  | "binop_less _ _ = None"

fun binop_lessOrEqual :: "lit \<Rightarrow> lit \<rightharpoonup> lit"
where
  "binop_lessOrEqual (LInt i1) (LInt i2) = Some (LBool (i1 \<le> i2))"
| "binop_lessOrEqual (LReal r1) (LReal r2) = Some (LBool (r1 \<le> r2))"
| "binop_lessOrEqual _ _ = None"

fun binop_greater :: "lit \<Rightarrow> lit \<rightharpoonup> lit"
  where
    "binop_greater (LInt i1) (LInt i2) = Some (LBool (i1 > i2))"
  | "binop_greater (LReal r1) (LReal r2) = Some (LBool (r1 > r2))"
  | "binop_greater _ _ = None"

fun binop_greaterOrEqual :: "lit \<Rightarrow> lit \<rightharpoonup> lit"
where
  "binop_greaterOrEqual (LInt i1) (LInt i2) = Some (LBool (i1 \<ge> i2))"
| "binop_greaterOrEqual (LReal r1) (LReal r2) = Some (LBool (r1 \<ge> r2))"
| "binop_greaterOrEqual _ _ = None"

fun binop_add :: "lit \<Rightarrow> lit \<rightharpoonup> lit"
  where 
    "binop_add (LInt i1) (LInt i2) = Some (LInt (i1 + i2))"
  | "binop_add (LReal r1) (LReal r2) = Some (LReal (r1 + r2))"
  | "binop_add _ _ = None"

fun binop_sub :: "lit \<Rightarrow> lit \<rightharpoonup> lit"
  where 
    "binop_sub (LInt i1) (LInt i2) = Some (LInt (i1 - i2))"
  | "binop_sub (LReal r1) (LReal r2) = Some (LReal (r1 - r2))"
  | "binop_sub _ _ = None"

fun binop_mul :: "lit \<Rightarrow> lit \<rightharpoonup> lit"
  where
    "binop_mul (LInt i1) (LInt i2) = Some (LInt (i1 * i2))"
  | "binop_mul (LReal r1) (LReal r2) = Some (LReal (r1 * r2))"
  | "binop_mul _ _ = None"

text \<open>Boogie's division semantics is determined by SMTLIB's division semantics, which is given
by the euclidean division if the divisor is nonzero and undefined (but fixed) otherwise.\<close>

definition eucl_div :: "int \<Rightarrow> int \<Rightarrow> int" where
  "eucl_div a b \<equiv> if b > 0 then a div b else -(a div -b)"

definition eucl_mod :: "int \<Rightarrow> int \<Rightarrow> int" where
  "eucl_mod a b \<equiv> if b > 0 then a mod b else a mod -b"

text \<open>Isabelle's built-in division fixes division by 0 to 0, so we have a case distinction here.
\<^const>\<open>undefined\<close> in Isabelle is just some fixed (but unknown) value of the correct type.\<close>

definition smt_div :: "int \<Rightarrow> int \<Rightarrow> int" where
  "smt_div i1 i2 = (if i2 \<noteq> 0 then eucl_div i1 i2 else undefined)"

definition smt_mod :: "int \<Rightarrow> int \<Rightarrow> int" where
  "smt_mod i1 i2 = (if i2 \<noteq> 0 then eucl_mod i1 i2 else undefined)"

definition smt_real_div :: "real \<Rightarrow> real \<Rightarrow> real" where
  "smt_real_div r1 r2 = (if r2 \<noteq> 0 then r1 div r2 else undefined)"

fun binop_div :: "lit \<Rightarrow> lit \<rightharpoonup> lit"
  where
    "binop_div (LInt i1) (LInt i2) = Some (LInt (smt_div i1 i2))"
  | "binop_div _ _ = None"

fun binop_real_div :: "lit \<Rightarrow> lit \<rightharpoonup> lit"
  where 
    "binop_real_div (LReal r1) (LReal r2) = Some (LReal (smt_real_div r1 r2))"
  | "binop_real_div (LInt i1) (LReal r2) = Some (LReal (smt_real_div (real_of_int i1) r2))"
  | "binop_real_div (LReal r1) (LInt i2) = Some (LReal (smt_real_div r1 (real_of_int i2)))"
  | "binop_real_div (LInt i1) (LInt i2) = Some (LReal (smt_real_div (real_of_int i1) (real_of_int i2)))"
  | "binop_real_div _ _ = None"

fun binop_mod :: "lit \<Rightarrow> lit \<rightharpoonup> lit"
  where 
    "binop_mod (LInt i1) (LInt i2) = Some (LInt (smt_mod i1 i2))"
  | "binop_mod _ _ = None"

fun binop_and :: "lit \<Rightarrow> lit \<rightharpoonup> lit"
  where
    "binop_and (LBool b1) (LBool b2) = Some (LBool (b1 \<and> b2))"
  | "binop_and _ _ = None"

fun binop_or :: "lit \<Rightarrow> lit \<rightharpoonup> lit"
  where
    "binop_or (LBool b1) (LBool b2) = Some (LBool (b1 \<or> b2))"
  | "binop_or _ _ = None"

fun binop_implies :: "lit \<Rightarrow> lit \<rightharpoonup> lit"
  where
    "binop_implies (LBool b1) (LBool b2) = Some (LBool (b1 \<longrightarrow> b2))"
  | "binop_implies _ _ = None"

fun binop_iff :: "lit \<Rightarrow> lit \<rightharpoonup> lit"
  where
    "binop_iff (LBool b1) (LBool b2) = Some (LBool (b1 = b2))"
  | "binop_iff _ _ = None"

fun binop_eval ::"binop \<Rightarrow> lit \<Rightarrow> lit \<rightharpoonup> lit"
  where
   "binop_eval Eq v1 v2 = Some (LBool (v1 = v2))"
 | "binop_eval Neq v1 v2 = Some (LBool (v1 \<noteq> v2))"
 | "binop_eval Add v1 v2 = binop_add v1 v2"
 | "binop_eval Sub v1 v2 = binop_sub v1 v2"
 | "binop_eval Mul v1 v2 = binop_mul v1 v2"
 | "binop_eval Div v1 v2 = binop_div v1 v2"
 | "binop_eval RealDiv v1 v2 = binop_real_div v1 v2"
 | "binop_eval Mod v1 v2 = binop_mod v1 v2"
 | "binop_eval Lt v1 v2 = binop_less v1 v2"
 | "binop_eval Le v1 v2 = binop_lessOrEqual v1 v2"
 | "binop_eval Gt v1 v2 = binop_greater v1 v2"
 | "binop_eval Ge v1 v2 = binop_greaterOrEqual v1 v2"
 | "binop_eval And v1 v2 = binop_and v1 v2"
 | "binop_eval Or v1 v2 = binop_or v1 v2"
 | "binop_eval Imp v1 v2 = binop_implies v1 v2"
 | "binop_eval Iff v1 v2 = binop_iff v1 v2"

fun binop_eval_val :: "binop \<Rightarrow> 'a val \<Rightarrow> 'a val \<rightharpoonup> 'a val"
  where 
  (* equality and inequality always reduce *)
   "binop_eval_val Eq v1 v2 = Some (LitV (LBool (v1 = v2)))"
 | "binop_eval_val Neq v1 v2 = Some (LitV (LBool (v1 \<noteq> v2)))"
 | "binop_eval_val bop (LitV v1) (LitV v2) = map_option LitV (binop_eval bop v1 v2)"
 | "binop_eval_val bop _ _ = None"

fun unop_not :: "lit \<rightharpoonup> lit"
  where
    "unop_not (LBool b) = Some (LBool (\<not> b))"
  | "unop_not _ = None"

fun unop_minus :: "lit \<rightharpoonup> lit"
  where 
    "unop_minus (LInt i) = Some (LInt (-i))"
  | "unop_minus (LReal r) = Some (LReal (-r))"
  | "unop_minus _ = None"

fun unop_int_to_real :: "lit \<rightharpoonup> lit"
  where 
    "unop_int_to_real (LInt i) = Some (LReal (real_of_int i))"
  | "unop_int_to_real _ = None"

fun unop_eval :: "unop \<Rightarrow> lit \<rightharpoonup> lit"
  where 
   "unop_eval Not v = unop_not v"
 | "unop_eval UMinus v = unop_minus v"
 | "unop_eval IntToReal v = unop_int_to_real v"

fun unop_eval_val :: "unop \<Rightarrow> 'a val \<rightharpoonup> 'a val"
  where
   "unop_eval_val uop (LitV v) = map_option LitV (unop_eval uop v)"
 | "unop_eval_val _ _ = None"

subsection \<open>Type and function interpretation\<close>

text\<open>Function interpretation:
  A Boogie function is semantically represented by an Isabelle function that takes as parameters the 
  instantiated type parameters and the argument values\<close>

type_synonym 'a fun_repr = "ty list \<Rightarrow> 'a val list \<rightharpoonup> 'a val"
type_synonym 'a fun_interp = "fname \<rightharpoonup> 'a fun_repr"

text\<open>Type interpretation: 
Each value of the abstract carrier type must be mapped to a corresponding type (constructed via a
type constructor).\<close>
type_synonym 'a absval_ty_fun = "'a \<Rightarrow> (tcon_id \<times> ty list)"

fun type_of_val :: "'a absval_ty_fun \<Rightarrow> 'a val \<Rightarrow> ty"
  where 
   "type_of_val A (LitV v) = TPrim (type_of_lit v)"
 | "type_of_val A (AbsV v) = TCon (fst (A v)) (snd (A v))"

type_synonym rtype_env = "ty list"

(* can only be used for instantiating closed types *)
fun instantiate :: "rtype_env \<Rightarrow> ty \<Rightarrow> ty"
  where
    "instantiate \<Omega> (TVar i) = (if i < length \<Omega> then \<Omega> ! i else TVar i)"
  | "instantiate \<Omega> (TPrim p) = (TPrim p)"
  | "instantiate \<Omega> (TCon tcon_id ty_args) = (TCon tcon_id (map (instantiate \<Omega>) ty_args))"

lemma instantiate_nil [simp]: "instantiate [] \<tau> = \<tau>"
  by (induction \<tau>) (simp_all add: map_idI)

type_synonym 'struct_ty proc_context = "'struct_ty pdecl list"

subsection \<open>Expression reduction (big-step semantics)\<close>

inductive red_expr :: "'a absval_ty_fun \<Rightarrow> var_context \<Rightarrow> 'a fun_interp \<Rightarrow> rtype_env \<Rightarrow> expr \<Rightarrow> 'a nstate \<Rightarrow> 'a val \<Rightarrow> bool"
  ("_,_,_,_ \<turnstile> ((\<langle>_,_\<rangle>) \<Down> _)" [51,0,0,0,0,0] 81)
  and red_exprs :: "'a absval_ty_fun \<Rightarrow> var_context \<Rightarrow> 'a fun_interp \<Rightarrow> rtype_env \<Rightarrow> expr list \<Rightarrow> 'a nstate \<Rightarrow> 'a val list \<Rightarrow> bool"
  ("_,_,_,_ \<turnstile> ((\<langle>_,_\<rangle>) [\<Down>] _)" [51,0,0,0,0,0] 81)
  for A :: "'a absval_ty_fun" and \<Lambda> :: "var_context" and \<Gamma> :: "'a fun_interp"
  where 
    RedVar: "\<lbrakk> lookup_var \<Lambda> n_s x = Some v \<rbrakk> \<Longrightarrow> A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(Var x), n_s\<rangle> \<Down> v"
  | RedBVar: "\<lbrakk> binder_state n_s i = Some v \<rbrakk> \<Longrightarrow> A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>BVar i, n_s\<rangle> \<Down> v"
  | RedLit: "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(Lit v), n_s\<rangle> \<Down> LitV v" 
  | RedBinOp: "\<lbrakk>A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e1, n_s\<rangle> \<Down> v1; A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e2, n_s\<rangle> \<Down> v2;
                 binop_eval_val bop v1 v2 = (Some v) \<rbrakk> \<Longrightarrow> 
             A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(e1 \<guillemotleft>bop\<guillemotright> e2), n_s\<rangle> \<Down> v"
  | RedUnOp: " \<lbrakk> A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e, n_s\<rangle> \<Down> v; unop_eval_val uop v = Some v' \<rbrakk> \<Longrightarrow> A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>UnOp uop e, n_s\<rangle> \<Down> v'"
  | RedFunOp: "\<lbrakk> \<Gamma> f = Some f_interp;
                A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>args, n_s\<rangle> [\<Down>] v_args;
                f_interp (map (instantiate \<Omega>) ty_args) v_args = Some v \<rbrakk> \<Longrightarrow>
             A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle> FunExp f ty_args args, n_s \<rangle> \<Down> v"
  | RedCondExpTrue: 
               "\<lbrakk> A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cond, n_s\<rangle> \<Down> (BoolV True); 
                  A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>thn, n_s\<rangle> \<Down> v \<rbrakk> \<Longrightarrow>
            A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle> CondExp cond thn els, n_s \<rangle> \<Down> v"
  | RedCondExpFalse: 
               "\<lbrakk> A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cond, n_s\<rangle> \<Down> (BoolV False); 
                  A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>els, n_s\<rangle> \<Down> v \<rbrakk> \<Longrightarrow>
            A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle> CondExp cond thn els, n_s \<rangle> \<Down> v"
  | RedOld: "\<lbrakk> A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle> e, n_s\<lparr>global_state := old_global_state n_s \<rparr> \<rangle> \<Down> v\<rbrakk> \<Longrightarrow> 
            A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle> Old e, n_s \<rangle> \<Down> v"
  | RedExpListNil:
    "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>[], n_s\<rangle> [\<Down>] []"
  | RedExpListCons:
    "\<lbrakk>A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e, n_s\<rangle> \<Down> v; A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>es, n_s\<rangle> [\<Down>] vs \<rbrakk> \<Longrightarrow>
      A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(e # es), n_s\<rangle> [\<Down>] (v # vs)"
(* value quantification rules *)
  | RedForAllTrue:
    "\<lbrakk>\<And>v. type_of_val A v = (instantiate \<Omega> ty) \<Longrightarrow> A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e, full_ext_env n_s v\<rangle> \<Down> LitV (LBool True) \<rbrakk> \<Longrightarrow> 
     A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>Forall ty e, n_s\<rangle> \<Down> LitV (LBool True)"
  | RedForAllFalse:
    "\<lbrakk>type_of_val A v = instantiate \<Omega> ty; A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e, full_ext_env n_s v\<rangle> \<Down> LitV (LBool False) \<rbrakk> \<Longrightarrow> 
     A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>Forall ty e, n_s\<rangle> \<Down> LitV (LBool False)"
  | RedExistsTrue:
    "\<lbrakk>type_of_val A v = instantiate \<Omega> ty; A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e, full_ext_env n_s v\<rangle> \<Down> LitV (LBool True) \<rbrakk> \<Longrightarrow>
     A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>Exists ty e, n_s\<rangle> \<Down> LitV (LBool True)"
  | RedExistsFalse:
    "\<lbrakk>\<And>v. type_of_val A v = instantiate \<Omega> ty \<Longrightarrow> A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e, full_ext_env n_s v\<rangle> \<Down> LitV (LBool False) \<rbrakk> \<Longrightarrow>
     A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>Exists ty e, n_s\<rangle> \<Down> LitV (LBool False)"
(* type quantification rules *)
  | RedForallT_True:
    "\<lbrakk>\<And>\<tau>. closed \<tau> \<Longrightarrow> A,\<Lambda>,\<Gamma>,(\<tau>#\<Omega>) \<turnstile> \<langle>e, n_s\<rangle> \<Down> LitV (LBool True) \<rbrakk> \<Longrightarrow> 
     A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>ForallT e, n_s\<rangle> \<Down> LitV (LBool True)"
  | RedForallT_False:
    "\<lbrakk>closed \<tau>; A,\<Lambda>,\<Gamma>,(\<tau>#\<Omega>) \<turnstile> \<langle>e, n_s\<rangle> \<Down> LitV (LBool False) \<rbrakk> \<Longrightarrow>
     A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>ForallT e, n_s\<rangle> \<Down> LitV (LBool False)"
  | RedExistsT_True:
    "\<lbrakk>closed \<tau>; A,\<Lambda>,\<Gamma>,(\<tau>#\<Omega>) \<turnstile> \<langle>e, n_s\<rangle> \<Down> LitV (LBool True) \<rbrakk> \<Longrightarrow>
     A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>ExistsT e, n_s\<rangle> \<Down> LitV (LBool True)"
  | RedExistsT_False:
    "\<lbrakk>\<And>\<tau>. closed \<tau> \<Longrightarrow> A,\<Lambda>,\<Gamma>,(\<tau>#\<Omega>) \<turnstile> \<langle>e, n_s\<rangle> \<Down> LitV (LBool False) \<rbrakk> \<Longrightarrow>
     A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>ExistsT e, n_s\<rangle> \<Down> LitV (LBool False)"

inductive_cases RedBinOp_case[elim!]: "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(e1 \<guillemotleft>bop\<guillemotright> e2), n_s\<rangle> \<Down> v"
inductive_cases RedUnOp_case[elim!]: "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>UnOp uop e1, n_s\<rangle> \<Down> v"
inductive_cases RedFunOp_case[elim!]: "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle> FunExp f ty_args args, n_s \<rangle> \<Down> v"
inductive_cases RedCondExp_case[elim!]: "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle> CondExp cond thn els, n_s \<rangle> \<Down> v"
inductive_cases RedOld_case[elim!]: "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>Old  e, n_s\<rangle> \<Down> v"
inductive_cases RedLit_case[elim!]: "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(Lit l), n_s\<rangle> \<Down> LitV l"
inductive_cases RedVar_case[elim!]: "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(Var x), n_s\<rangle> \<Down> v"
inductive_cases RedBVar_case[elim!]: "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(BVar i), n_s\<rangle> \<Down> v"
inductive_cases RedForallTrue_case: "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>Forall ty e, n_s\<rangle> \<Down> LitV (LBool True)"
inductive_cases RedForallFalse_case: "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>Forall ty e, n_s\<rangle> \<Down> LitV (LBool False)"

lemma red_cond_exp_cases:
  assumes "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>CondExp cond thn els, n_s \<rangle> \<Down> v"
  obtains b
  where "(A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cond, n_s\<rangle> \<Down> BoolV b) \<and> (A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>if b then thn else els, n_s\<rangle> \<Down> v)"
  using assms
  apply cases
   apply fastforce
  apply fastforce
  done

definition expr_sat :: "'a absval_ty_fun \<Rightarrow> var_context \<Rightarrow> 'a fun_interp \<Rightarrow> rtype_env \<Rightarrow> 'a nstate \<Rightarrow> expr \<Rightarrow> bool"
  where "expr_sat A \<Lambda> \<Gamma> \<Omega> n_s e = (A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e, n_s\<rangle> \<Down> LitV (LBool True))"

definition expr_all_sat :: "'a absval_ty_fun \<Rightarrow> var_context \<Rightarrow> 'a fun_interp \<Rightarrow> rtype_env \<Rightarrow> 'a nstate \<Rightarrow> expr list \<Rightarrow> bool"
  where "expr_all_sat A \<Lambda> \<Gamma> \<Omega> n_s es = list_all (expr_sat A \<Lambda> \<Gamma> \<Omega> n_s) es"

definition expr_exists_fail :: "'a absval_ty_fun \<Rightarrow> var_context \<Rightarrow> 'a fun_interp \<Rightarrow> rtype_env \<Rightarrow> 'a nstate \<Rightarrow> expr list \<Rightarrow> bool"
  where "expr_exists_fail A \<Lambda> \<Gamma> \<Omega> n_s es = list_ex (expr_sat A \<Lambda> \<Gamma> \<Omega> n_s) es"

definition where_clause_sat :: "'a absval_ty_fun \<Rightarrow> var_context \<Rightarrow> 'a fun_interp \<Rightarrow> rtype_env \<Rightarrow> 'a nstate \<Rightarrow> vdecl \<Rightarrow> bool"
  where "where_clause_sat A \<Lambda> \<Gamma> \<Omega> n_s vd = (\<forall>x ty w. vd = (x,ty,Some w) \<longrightarrow> expr_sat A \<Lambda> \<Gamma> \<Omega> n_s w)"

definition where_clauses_all_sat :: "'a absval_ty_fun \<Rightarrow> var_context \<Rightarrow> 'a fun_interp \<Rightarrow> rtype_env \<Rightarrow> 'a nstate \<Rightarrow> vdecls \<Rightarrow> bool"
  where "where_clauses_all_sat A \<Lambda> \<Gamma> \<Omega> n_s vs = list_all (where_clause_sat A \<Lambda> \<Gamma> \<Omega> n_s) vs"

(* where-clauses of global variables should be assumed without taking local variables into account, due to shadowing. *)
definition where_clauses_all_sat_context :: "'a absval_ty_fun \<Rightarrow> var_context \<Rightarrow> 'a fun_interp \<Rightarrow> rtype_env \<Rightarrow> 'a nstate \<Rightarrow> bool"
  where "where_clauses_all_sat_context A \<Lambda> \<Gamma> \<Omega> ns \<equiv> 
           where_clauses_all_sat A (fst \<Lambda>, []) \<Gamma> \<Omega> ns (fst \<Lambda>) \<and> where_clauses_all_sat A \<Lambda> \<Gamma> \<Omega> ns (snd \<Lambda>)"

subsection \<open>Command reduction (big-step semantics)\<close>

inductive red_cmd :: "'a absval_ty_fun \<Rightarrow> 'm proc_context \<Rightarrow> var_context \<Rightarrow> 'a fun_interp \<Rightarrow> rtype_env \<Rightarrow> cmd \<Rightarrow> 'a state \<Rightarrow> 'a state \<Rightarrow> bool"
  ("_,_,_,_,_ \<turnstile> ((\<langle>_,_\<rangle>) \<rightarrow>/ _)" [51,51,0,0,0] 81)
  for A :: "'a absval_ty_fun" and M :: "'m proc_context" and \<Lambda> :: var_context and  \<Gamma> :: "'a fun_interp" and \<Omega> :: rtype_env
  where
    RedAssertOk: "\<lbrakk> A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e, n_s\<rangle> \<Down> LitV (LBool True) \<rbrakk> \<Longrightarrow> 
                 A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>Assert e, Normal n_s\<rangle> \<rightarrow> Normal n_s"
  | RedAssertFail: "\<lbrakk> A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e, n_s\<rangle> \<Down> LitV (LBool False) \<rbrakk> \<Longrightarrow> 
                  A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>Assert e, Normal n_s\<rangle> \<rightarrow> Failure"
  | RedAssumeOk: "\<lbrakk> A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e, n_s\<rangle> \<Down> LitV (LBool True) \<rbrakk> \<Longrightarrow> 
                A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>Assume e, Normal n_s\<rangle> \<rightarrow> Normal n_s"
  | RedAssumeMagic: "\<lbrakk> A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e, n_s\<rangle> \<Down> LitV (LBool False) \<rbrakk> \<Longrightarrow> 
                A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>Assume e, Normal n_s\<rangle> \<rightarrow> Magic"
  | RedAssign: "\<lbrakk> lookup_var_ty \<Lambda> x = Some ty; type_of_val A v = instantiate \<Omega> ty; 
                  A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e, n_s\<rangle> \<Down> v \<rbrakk> \<Longrightarrow>
               A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>Assign x e, Normal n_s\<rangle> \<rightarrow>  Normal (update_var \<Lambda> n_s x v)"
  | RedHavocNormal: "\<lbrakk> lookup_var_decl \<Lambda> x = Some (ty,w); 
                 type_of_val A v = instantiate \<Omega> ty;
                 \<And>cond. w = Some cond \<Longrightarrow> A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cond, (update_var \<Lambda> n_s x v)\<rangle> \<Down> BoolV True \<rbrakk> \<Longrightarrow>
                 A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>Havoc x, Normal n_s\<rangle> \<rightarrow> Normal (update_var \<Lambda> n_s x v)"
  | RedHavocMagic: "\<lbrakk> lookup_var_decl \<Lambda> x = Some (ty,Some(cond)); 
                 type_of_val A v = instantiate \<Omega> ty;
                 A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cond, (update_var \<Lambda> n_s x v)\<rangle> \<Down> BoolV False \<rbrakk> \<Longrightarrow>
                 A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>Havoc x, Normal n_s\<rangle> \<rightarrow> Magic"
(* TODO: where clauses for return variables *)
  | RedProcCallOkAndMagic: "\<lbrakk> map_of M m = Some msig; 
      A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>args, n_s\<rangle> [\<Down>] v_args;
      pre_ls = Map.empty( (map fst (proc_args msig )) [\<mapsto>] v_args  ) ;
      expr_all_sat A (fst \<Lambda>, proc_args msig) \<Gamma> \<Omega> (n_s\<lparr>local_state := new_ls\<rparr>) (proc_checked_pres msig);
      map (lookup_vdecls_ty (fst \<Lambda>)) (proc_modifs msig) = map Some ty_modifs;  
      map (type_of_val A) vs_modifs = map (instantiate \<Omega>) ty_modifs;
      map (type_of_val A) vs_ret = map (fst \<circ> snd) (proc_rets msig);      
      post_ls = pre_ls((map fst (proc_rets msig)) [\<mapsto>] vs_ret);
      post_gs = (global_state n_s)((proc_modifs msig) [\<mapsto>] vs_modifs);
      post_state = \<lparr>old_global_state = global_state n_s, global_state = post_gs, local_state = post_ls, binder_state = Map.empty\<rparr>;
      post_success = expr_all_sat A (fst \<Lambda>, (proc_args msig)@(proc_rets msig)) \<Gamma> \<Omega> post_state (proc_all_posts msig);
      post_fail = expr_exists_fail A (fst \<Lambda>, (proc_args msig)@(proc_rets msig)) \<Gamma> \<Omega> post_state (proc_all_posts msig);
      post_success \<or> post_fail;
      n_s' = n_s\<lparr>global_state := post_gs\<rparr>\<lparr>local_state := (local_state n_s)(rets [\<mapsto>] vs_ret)\<rparr> \<rbrakk> \<Longrightarrow>
               A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>ProcCall m args rets, Normal n_s\<rangle> \<rightarrow> (if post_success then Normal n_s' else Magic)"
  | RedProcCallFail: "\<lbrakk> map_of M m = Some msig;
      A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>args, n_s\<rangle> [\<Down>] v_args;
      pre_ls = Map.empty( (map fst (proc_args msig )) [\<mapsto>] v_args  ) ;
      expr_exists_fail A (fst \<Lambda>, proc_args msig) \<Gamma> \<Omega> (n_s\<lparr>local_state := new_ls\<rparr>) (proc_checked_pres msig) \<rbrakk> \<Longrightarrow>
               A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>ProcCall m args rets, Normal n_s\<rangle> \<rightarrow> Failure"
  | RedPropagateMagic: "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>s, Magic\<rangle> \<rightarrow> Magic"
  | RedPropagateFailure: "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>s, Failure\<rangle> \<rightarrow> Failure"

inductive_cases RedAssertOk_case [elim]: "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>Assert e, Normal n_s\<rangle> \<rightarrow> Normal n_s"
inductive_cases RedAssumeOk_case [elim]: "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>Assume e, Normal n_s\<rangle> \<rightarrow> Normal n_s"
inductive_cases RedAssign_case: "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>Assign x e, Normal n_s\<rangle> \<rightarrow> Normal (update_var \<Lambda> n_s x v)"
inductive_cases RedHavoc_case: "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>Havoc x, Normal n_s\<rangle> \<rightarrow> Normal (update_var \<Lambda> n_s x v)"

text \<open>Command list reduction (big-step semantics)\<close>

inductive red_cmd_list :: "'a absval_ty_fun \<Rightarrow> 'm proc_context \<Rightarrow> var_context \<Rightarrow> 'a fun_interp \<Rightarrow> rtype_env \<Rightarrow> cmd list \<Rightarrow> 'a state \<Rightarrow> 'a state \<Rightarrow> bool"
  ("_,_,_,_,_ \<turnstile> ((\<langle>_,_\<rangle>) [\<rightarrow>]/ _)" [51,0,0,0] 81)
  for A :: "'a absval_ty_fun" and M :: "'m proc_context" and \<Lambda> :: var_context and \<Gamma> :: "'a fun_interp" and \<Omega> :: rtype_env
  where
    RedCmdListNil: "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>[],s\<rangle> [\<rightarrow>] s"
  | RedCmdListCons: "\<lbrakk> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>c,s\<rangle> \<rightarrow> s''; A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs,s''\<rangle> [\<rightarrow>] s' \<rbrakk> \<Longrightarrow> 
                   A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(c # cs), s\<rangle> [\<rightarrow>] s'"

inductive_cases RedCmdListNil_case [elim]: "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>[],s\<rangle> [\<rightarrow>] s"
inductive_cases RedCmdListCons_case [elim]: "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(c # cs), s\<rangle> [\<rightarrow>] s''"

subsection \<open>CFG reduction (small-step semantics)\<close>

type_synonym 'a cfg_config = "(node+unit) \<times> 'a state"

inductive red_cfg :: "'a absval_ty_fun \<Rightarrow> mbodyCFG proc_context \<Rightarrow> var_context \<Rightarrow> 'a fun_interp \<Rightarrow> rtype_env \<Rightarrow> mbodyCFG \<Rightarrow> 'a cfg_config \<Rightarrow> 'a cfg_config \<Rightarrow> bool"
  ("_,_,_,_,_,_ \<turnstile> (_ -n\<rightarrow>/ _)" [51,0,0,0] 81)
  for A :: "'a absval_ty_fun" and M :: "mbodyCFG proc_context" and \<Lambda> :: var_context and \<Gamma> :: "'a fun_interp" and \<Omega> :: rtype_env and G :: mbodyCFG
  where
    RedNormalSucc: "\<lbrakk>node_to_block(G) ! n = cs; A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs,Normal ns\<rangle> [\<rightarrow>] Normal ns'; List.member (out_edges(G) ! n) n'  \<rbrakk> \<Longrightarrow> 
              A,M,\<Lambda>,\<Gamma>,\<Omega>,G  \<turnstile> (Inl n, Normal ns) -n\<rightarrow> (Inl n', Normal ns')"
  | RedNormalReturn: "\<lbrakk>node_to_block(G)! n = cs; A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs,Normal ns\<rangle> [\<rightarrow>] Normal ns'; (out_edges(G) ! n) = [] \<rbrakk> \<Longrightarrow> 
               A,M,\<Lambda>,\<Gamma>,\<Omega>,G  \<turnstile> (Inl n, Normal ns) -n\<rightarrow> (Inr (), Normal ns')"
  | RedFailure: "\<lbrakk>node_to_block(G) ! n = cs; A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs,Normal ns\<rangle> [\<rightarrow>] Failure \<rbrakk> \<Longrightarrow>
              A,M,\<Lambda>,\<Gamma>,\<Omega>,G  \<turnstile> (Inl n, Normal ns) -n\<rightarrow> (Inr (), Failure)"
  | RedMagic: "\<lbrakk>node_to_block(G) ! n = cs; A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs,Normal ns\<rangle> [\<rightarrow>] Magic \<rbrakk> \<Longrightarrow>
              A,M,\<Lambda>,\<Gamma>,\<Omega>,G  \<turnstile> (Inl n, Normal ns) -n\<rightarrow> (Inr (), Magic)"

fun is_final_config :: "'a cfg_config \<Rightarrow> bool"
  where
    "is_final_config (Inl n,_) = False"
  | "is_final_config (Inr n,_) = True"

inductive_cases RedNormalSucc_case: "A,M,\<Lambda>,\<Gamma>,G,\<Omega>  \<turnstile> (Inl n,s) -n\<rightarrow> (Inl n',s')"

text \<open>Reflexive and transitive closure of CFG reduction\<close>

abbreviation red_cfg_multi :: "'a absval_ty_fun \<Rightarrow> mbodyCFG proc_context \<Rightarrow> var_context \<Rightarrow> 'a fun_interp \<Rightarrow> rtype_env \<Rightarrow> mbodyCFG \<Rightarrow> 'a cfg_config \<Rightarrow> 'a cfg_config \<Rightarrow> bool"
  ("_,_,_,_,_,_ \<turnstile>_ -n\<rightarrow>*/ _" [51,0,0,0] 81)
  where "red_cfg_multi A M \<Lambda> \<Gamma> \<Omega> G \<equiv> rtranclp (red_cfg A M \<Lambda> \<Gamma> \<Omega> G)"

text \<open>N-step CFG reduction\<close>

abbreviation red_cfg_k_step :: "'a absval_ty_fun \<Rightarrow> mbodyCFG proc_context \<Rightarrow> var_context \<Rightarrow> 'a fun_interp \<Rightarrow> rtype_env \<Rightarrow> mbodyCFG \<Rightarrow> 'a cfg_config \<Rightarrow> nat \<Rightarrow> 'a cfg_config \<Rightarrow> bool"
  ("_,_,_,_,_,_ \<turnstile>_ -n\<rightarrow>^_/ _" [51,0,0,0,0] 81)
where "red_cfg_k_step A M \<Lambda> \<Gamma> \<Omega> G c1 n c2 \<equiv> ((red_cfg A M \<Lambda> \<Gamma> \<Omega> G)^^n) c1 c2"

(* if inputs types are correct, then function reduces to a value of correct output type *)
fun fun_interp_single_wf :: "'a absval_ty_fun \<Rightarrow> nat \<times> ty list \<times> ty \<Rightarrow> (ty list \<Rightarrow> 'a val list \<rightharpoonup> 'a val) \<Rightarrow> bool"
  where "fun_interp_single_wf A (n_ty_params, args_ty, ret_ty) f =
         (\<forall> ts. (length ts = n_ty_params \<and> list_all closed ts) \<longrightarrow>  
               (\<forall> vs. length vs = length args_ty \<and>
                      map (type_of_val A) vs = (map (instantiate ts) args_ty) \<longrightarrow> 
                        ((\<exists>v. f ts vs = Some v \<and> type_of_val A v = (instantiate ts ret_ty)))))
 "

(* if function reduces, then input types must have been correct *)
fun fun_interp_single_wf_2 :: "'a absval_ty_fun \<Rightarrow> nat \<times> ty list \<times> ty \<Rightarrow> (ty list \<Rightarrow> 'a val list \<rightharpoonup> 'a val) \<Rightarrow> bool"
  where "fun_interp_single_wf_2 A (n_ty_params, args_ty, ret_ty) f =
         (\<forall>ts vs v. (f ts vs = Some v \<longrightarrow> 
                       (type_of_val A v = instantiate ts ret_ty \<and>
                        length ts = n_ty_params \<and> list_all closed ts \<and> 
                        map (type_of_val A) vs = map (instantiate ts) args_ty))  )"
         

definition fun_interp_wf :: "'a absval_ty_fun \<Rightarrow> fdecls \<Rightarrow> 'a fun_interp \<Rightarrow> bool"
  where "fun_interp_wf A fds \<gamma>_interp = 
            (\<forall>fn fd. map_of fds fn = Some fd \<longrightarrow> 
                  (\<exists>f. \<gamma>_interp fn = Some f \<and> fun_interp_single_wf A fd f \<and> fun_interp_single_wf_2 A fd f))"

definition state_typ_wf :: "'a absval_ty_fun \<Rightarrow> rtype_env \<Rightarrow> 'a named_state \<Rightarrow> vdecls \<Rightarrow> bool"
  where "state_typ_wf A \<Omega> ns vs = 
           (\<forall> v t. lookup_vdecls_ty vs v = Some t  \<longrightarrow> 
                          Option.map_option (\<lambda>v. type_of_val A v) (ns(v)) = (Some (instantiate \<Omega> t)))"

lemma state_typ_wf_lookup:
  assumes S1: "state_typ_wf A \<Omega> (local_state ns) (snd \<Lambda>)" and 
          S2: "state_typ_wf A \<Omega> (global_state ns) (fst \<Lambda>)" and
          Lookup: "lookup_var_ty \<Lambda> x = Some \<tau>"
        shows "\<exists>v. lookup_var \<Lambda> ns x = Some v \<and> type_of_val A v = instantiate \<Omega> \<tau>"
proof -
  from Lookup have "lookup_vdecls_ty (snd \<Lambda>) x = Some \<tau> \<or> (map_of (snd \<Lambda>) x = None \<and> lookup_vdecls_ty (fst \<Lambda>) x = Some \<tau>)"
    unfolding lookup_var_ty_def lookup_vdecls_ty_def
    by (metis lookup_var_decl_global_3 lookup_var_decl_local option.collapse)
  thus ?thesis
  proof (rule disjE)
    assume A1:"lookup_vdecls_ty (snd \<Lambda>) x = Some \<tau>"
    with S1 obtain v where "(local_state ns) x = Some v" and "type_of_val A v = instantiate \<Omega> \<tau>"      
      using state_typ_wf_def 
      by blast      
    thus ?thesis using Lookup lookup_var_local
      by (metis (no_types, lifting) A1 lookup_vdecls_ty_def map_option_eq_Some prod.collapse) 
  next
    assume A2:"map_of (snd \<Lambda>) x = None \<and> lookup_vdecls_ty (fst \<Lambda>) x = Some \<tau>"
    with S2 obtain v where "(global_state ns) x = Some v" and "type_of_val A v = instantiate \<Omega> \<tau>"
      using state_typ_wf_def by blast
    thus ?thesis using Lookup A2 lookup_var_global
      by (metis A2 prod.exhaust_sel)
  qed
qed

subsection \<open>Procedure Correctness\<close>

definition valid_configuration 
  where "valid_configuration A \<Lambda> \<Gamma> \<Omega> posts m' s' \<equiv> 
         s' \<noteq> Failure \<and> 
         (is_final_config (m',s') \<longrightarrow> (\<forall>ns'. s' = Normal ns' \<longrightarrow> expr_all_sat A \<Lambda> \<Gamma> \<Omega> ns' posts))"

definition proc_body_satisfies_spec :: "'a absval_ty_fun \<Rightarrow> mbodyCFG proc_context \<Rightarrow> var_context \<Rightarrow> 'a fun_interp \<Rightarrow> rtype_env \<Rightarrow> expr list \<Rightarrow> expr list \<Rightarrow> mbodyCFG \<Rightarrow> 'a nstate \<Rightarrow> bool"
  where "proc_body_satisfies_spec A M \<Lambda> \<Gamma> \<Omega> pres posts mbody ns \<equiv>
         expr_all_sat A \<Lambda> \<Gamma> \<Omega> ns pres \<longrightarrow> 
          (\<forall> m' s'. (A, M, \<Lambda>, \<Gamma>, \<Omega>, mbody \<turnstile> (Inl (entry(mbody)), Normal ns) -n\<rightarrow>* (m',s')) \<longrightarrow> 
                    valid_configuration A \<Lambda> \<Gamma> \<Omega> posts m' s')
      "

text \<open>\<^term>\<open>proc_body_satisfies_spec\<close> states when a procedure's CFG is correct w.r.t. postconditions \<^term>\<open>posts\<close> 
under the assumption of preconditions \<^term>\<open>pres\<close>. To add support for where-clauses, one would need to 
add an additional assumption here (proof generation does not support where-clauses currently).\<close>

definition axioms_sat :: "'a absval_ty_fun \<Rightarrow> var_context \<Rightarrow> 'a fun_interp \<Rightarrow> 'a nstate \<Rightarrow> axiom list \<Rightarrow> bool"
  where "axioms_sat A \<Lambda> \<Gamma> n_s as = list_all (expr_sat A \<Lambda> \<Gamma> [] n_s) as"

definition state_restriction :: "'a named_state \<Rightarrow> vdecls \<Rightarrow> 'a named_state"
  where "state_restriction ns_orig vs x = 
         (if map_of vs x \<noteq> None then ns_orig x else None)"

definition nstate_global_restriction :: "'a nstate \<Rightarrow> vdecls \<Rightarrow> 'a nstate"
  where "nstate_global_restriction ns vs = global_to_nstate (state_restriction (global_state ns) vs)"

abbreviation axiom_assm
  where "axiom_assm A \<Gamma> consts ns axioms \<equiv> 
     (axioms_sat A (consts, []) \<Gamma> (nstate_global_restriction ns consts) axioms)"

text \<open>The following condition specifies what must hold for the list of constants with a unique modifier.
      The condition states that all corresponding values in the state must be distinct. Note that constants
      without unique modifiers may have values that clash with unique constants, which is consistent with the 
      verification condition generated by Boogie (status 21.10.2023).
      Note that the verification condition only forces distinctness between values of unique constants of 
      the \<^emph>\<open>same\<close> type. Here, we force distinctness between values of all unique constants. These two
      definitions are equivalent, since values of different types are distinct in Boogie by default
      (every value can have only one type as reflected by the function \<^term>\<open>type_of_val\<close>).\<close>

definition unique_constants_distinct :: "'a named_state \<Rightarrow> vname list \<Rightarrow> bool"
  where "unique_constants_distinct ns xs \<longleftrightarrow> distinct (map (\<lambda>x. the (ns x)) xs)"

fun proc_is_correct :: "'a absval_ty_fun \<Rightarrow> fdecls \<Rightarrow> vdecls \<Rightarrow> vname list \<Rightarrow> vdecls \<Rightarrow> axiom list \<Rightarrow> 'struct_ty2 procedure \<Rightarrow> 
                       ('a absval_ty_fun \<Rightarrow> 'struct_ty proc_context \<Rightarrow> var_context \<Rightarrow> 'a fun_interp \<Rightarrow> rtype_env \<Rightarrow> expr list \<Rightarrow> expr list \<Rightarrow> 'struct_ty2 \<Rightarrow> 'a nstate \<Rightarrow> bool) \<Rightarrow> 
                         bool"
  where 
    "proc_is_correct A fun_decls constants unique_consts global_vars axioms proc proc_body_satisfies_spec_general =  
      (case proc_body(proc) of
        Some (locals, struct) \<Rightarrow> 
          ( ( (\<forall>t. closed t \<longrightarrow> (\<exists>v. type_of_val A (v :: 'a val) = t)) \<and> (\<forall>v. closed ((type_of_val A) v)) ) \<longrightarrow>
          (\<forall> \<Gamma>. fun_interp_wf A fun_decls \<Gamma> \<longrightarrow>
          (
             (\<forall>\<Omega> gs ls. (list_all closed \<Omega> \<and> length \<Omega> = proc_ty_args proc) \<longrightarrow>        
             (state_typ_wf A \<Omega> gs (constants @ global_vars) \<longrightarrow>
              state_typ_wf A \<Omega> ls ((proc_args proc)@ (locals @ proc_rets proc)) \<longrightarrow>
              unique_constants_distinct gs unique_consts \<longrightarrow>
              (axioms_sat A (constants, []) \<Gamma> (global_to_nstate (state_restriction gs constants)) axioms) \<longrightarrow>            
              (proc_body_satisfies_spec_general 
                                        A [] (constants@global_vars, (proc_args proc)@(locals@(proc_rets proc))) \<Gamma> \<Omega> 
                                       (proc_all_pres proc) (proc_checked_posts proc) struct
                                       \<lparr>old_global_state = gs, global_state = gs, local_state = ls, binder_state = Map.empty\<rparr> ) )
            )
          )))
      | None \<Rightarrow> True)"

(*
fun proc_is_correct :: "'a absval_ty_fun \<Rightarrow> fdecls \<Rightarrow> vdecls \<Rightarrow> vdecls \<Rightarrow> axiom list \<Rightarrow> procedure \<Rightarrow> bool"
  where 
    "proc_is_correct A fun_decls constants global_vars axioms proc =
      (case proc_body(proc) of
        Some (locals, mCFG) \<Rightarrow>
          ( ( (\<forall>t. closed t \<longrightarrow> (\<exists>v. type_of_val A (v :: 'a val) = t)) \<and> (\<forall>v. closed ((type_of_val A) v)) ) \<longrightarrow>
          (\<forall> \<Gamma>. fun_interp_wf A fun_decls \<Gamma> \<longrightarrow>
          (
             (\<forall>\<Omega> gs ls. (list_all closed \<Omega> \<and> length \<Omega> = proc_ty_args proc) \<longrightarrow>        
             (state_typ_wf A \<Omega> gs (constants @ global_vars) \<longrightarrow>
              state_typ_wf A \<Omega> ls ((proc_args proc)@ (locals @ proc_rets proc)) \<longrightarrow>
              (axioms_sat A (constants, []) \<Gamma> (global_to_nstate (state_restriction gs constants)) axioms) \<longrightarrow>            
              proc_body_satisfies_spec A [] (constants@global_vars, (proc_args proc)@(locals@(proc_rets proc))) \<Gamma> \<Omega> 
                                       (proc_all_pres proc) (proc_checked_posts proc) mCFG 
                                       \<lparr>old_global_state = gs, global_state = gs, local_state = ls, binder_state = Map.empty\<rparr> )
            )
          )))
      | None \<Rightarrow> True)"
*)

text \<open>\<^term>\<open>proc_is_correct A fun_decls constants unique_consts global_vars axioms proc proc_body_satisfies_spec_general\<close> gives the definition
that a procedure \<^term>\<open>proc\<close> is correct w.r.t. the type interpretation \<^term>\<open>A\<close> the function declarations \<open>fun_decls\<close>, 
constants \<^term>\<open>constants\<close>, global variables \<^term>\<open>global_vars\<close> and Boogie axioms \<^term>\<open>axioms\<close>. 
\<^term>\<open>unique_consts\<close> denotes the list of constants with a unique modifier.

Since the current proof generation does not support procedure calls yet, we just instantiate the
procedure context to the empty list here. 

In our certificates, we prove (\<^term>\<open>\<And>A. proc_is_correct A fun_decls constants unique_consts global_vars axioms proc proc_body_satisfies_spec_general\<close>),
i.e., we prove procedure correctness for every type interpretation (\<And> is a universal quantifier at 
the meta level). Note that for certain type interpretations procedure correctness is trivial (see
the definition of \<^term>\<open>proc_is_correct\<close>).
\<close>

subsection \<open>Properties of the semantics\<close>

text \<open>Expression evaluation is deterministic\<close>

lemma expr_eval_determ: 
shows "((A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e1, s\<rangle> \<Down> v) \<Longrightarrow> ((A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e1, s\<rangle> \<Down> v') \<Longrightarrow> v = v'))"  
    and "(A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>es, s\<rangle> [\<Down>] vs) \<Longrightarrow> (A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>es, s\<rangle> [\<Down>] vs') \<Longrightarrow> vs = vs' "
proof (induction arbitrary: v' and vs' rule: red_expr_red_exprs.inducts)
  case (RedVar n_s x v \<Omega>)
  assume "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>Var x,n_s\<rangle> \<Down> v'"
  then show ?case using \<open>lookup_var \<Lambda> n_s x = Some v\<close> by (cases; simp)
next
  case (RedBVar n_s i v \<Omega>)
  assume "binder_state n_s i = Some v"
  assume "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>BVar i,n_s\<rangle> \<Down> v'"
  then show ?case using \<open>binder_state n_s i = Some v\<close> by (cases; simp)
next
  case (RedLit \<Omega> l n_s)
  assume "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>Lit l,n_s\<rangle> \<Down> v'"
  then show ?case by (cases; simp)
next
  case (RedBinOp \<Omega> e1 n_s v1 e2 v2 bop v)
  from RedBinOp.prems show ?case
  proof (cases)
    fix v1' v2'
    assume "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e1,n_s\<rangle> \<Down> v1'" hence "v1 = v1'" using RedBinOp.IH by simp
    assume "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e2,n_s\<rangle> \<Down> v2'" hence "v2 = v2'" using RedBinOp.IH by simp
    assume "binop_eval_val bop v1' v2' = Some v'"
    with \<open>v1 = v1'\<close> \<open>v2 = v2'\<close> show ?thesis using RedBinOp.hyps by simp
  qed
next
  case (RedUnOp \<Omega> e n_s v uop v' veval)
  from RedUnOp.prems show ?case
  proof (cases)
    fix v2
    assume "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e,n_s\<rangle> \<Down> v2" hence "v2 = v" using RedUnOp.IH by simp
    assume "unop_eval_val uop v2 = Some veval"
    with \<open>v2 = v\<close> show ?thesis using RedUnOp.hyps by simp
  qed
next
  case (RedFunOp f f_interp \<Omega> args n_s v_args ty_args v v')
  from RedFunOp.prems show ?case
  proof (cases)
    fix v_args' f_interp'
    assume "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>args,n_s\<rangle> [\<Down>] v_args'" hence "v_args = v_args'" using RedFunOp.IH by simp
    assume "\<Gamma> f = Some f_interp'" hence "f_interp = f_interp'" using RedFunOp.IH by simp
    assume "f_interp' (map (instantiate \<Omega>) ty_args) v_args' = Some v'"
    thus ?case using \<open>v_args = v_args'\<close> \<open>f_interp = f_interp'\<close> using RedFunOp.hyps by simp
  qed
next
  case (RedExpListNil n_s vs')
  thus ?case by (cases; simp)
next
  case (RedExpListCons \<Omega> e n_s v es vs' vs'')
  assume "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e # es,n_s\<rangle> [\<Down>] vs''"
  thus ?case 
  proof cases
    fix w ws      
    assume "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e,n_s\<rangle> \<Down> w" hence "v = w" using RedExpListCons.IH by simp
    assume "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>es,n_s\<rangle> [\<Down>] ws" hence "ws = vs'" using RedExpListCons.IH by simp  
    moreover assume "vs'' = w # ws"
    ultimately show ?thesis using \<open>v = w\<close>  by simp
  qed
next
  case (RedOld \<Omega> e n_s v) 
  thus ?case by (blast elim: red_expr.cases)
next
  case (RedCondExpTrue \<Omega> cond n_s thn v els)
  from RedCondExpTrue.prems
  show ?case 
    by (cases, insert RedCondExpTrue.IH, blast+)
next
  case (RedCondExpFalse \<Omega> cond n_s thn v els)
  from RedCondExpFalse.prems
  show ?case 
    by (cases, insert RedCondExpFalse.IH, blast+)
next
  case (RedForAllTrue ty e n_s v')
  thus ?case by (blast elim: red_expr.cases)
next
  case (RedForAllFalse v ty e n_s v')
  thus ?case by (blast elim: red_expr.cases)
next
  case (RedExistsTrue v ty e n_s v')
  thus ?case by (blast elim: red_expr.cases)
next
  case (RedExistsFalse ty e n_s v')
  thus ?case by (blast elim: red_expr.cases)
next
  case (RedForallT_True e n_s v')
  thus ?case by (blast elim: red_expr.cases)
next
  case (RedForallT_False ty e n_s)
  thus ?case by (blast elim: red_expr.cases)
next
  case (RedExistsT_True ty e n_s)
  thus ?case by (blast elim: red_expr.cases)
next
  case (RedExistsT_False e n_s)
  thus ?case by (blast elim: red_expr.cases)    
qed

lemma red_exprs_length: "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>es, n_s\<rangle> [\<Down>] vs \<Longrightarrow> length es = length vs"
  by (induction vs arbitrary: es; erule red_exprs.cases; simp)
   
lemma step_nil_same:
  assumes A1: "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>[], s\<rangle> [\<rightarrow>] s''"
  shows "s = s''"
proof -
  from A1 show ?thesis by (cases; auto)
qed

lemma no_out_edges_return:
  assumes 
    A1: "A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl n,s) -n\<rightarrow> (Inl n', s')" and 
    A2: "(out_edges(G) ! n) = []"
  shows False
  using A1 A2 
  by (simp add: red_cfg.simps member_rec(2)) 

lemma magic_stays_cmd:
  assumes "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>c, Magic\<rangle> \<rightarrow> s'"
  shows "s' = Magic"
  using assms
  by (cases rule: red_cmd.cases)

lemma magic_stays_cmd_list_aux:
  assumes "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs, s\<rangle> [\<rightarrow>] s'" and "s = Magic"
  shows   "s' = Magic"
  using assms
proof (induct rule: red_cmd_list.induct)
  case RedCmdListNil
  then show ?case by simp
next
  case (RedCmdListCons c s' cs s'')
  then show ?case using magic_stays_cmd by blast
qed

lemma magic_stays_cmd_list:
  assumes "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs, Magic\<rangle> [\<rightarrow>] s'"
  shows "s' = Magic"
  using assms
  by (simp add: magic_stays_cmd_list_aux)

lemma magic_red_cmd_list: "A,M,\<Lambda>',\<Gamma>,\<Omega> \<turnstile> \<langle>cs,Magic\<rangle> [\<rightarrow>] Magic"
  by (induction cs) (auto intro: red_cmd_list.intros RedPropagateMagic)

lemma failure_stays_cmd:
  assumes "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>c, Failure\<rangle> \<rightarrow> s'"
  shows "s' = Failure"
  using assms
  by (cases rule: red_cmd.cases)

lemma failure_stays_cmd_list_aux:
  assumes "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs, s\<rangle> [\<rightarrow>] s'" and "s = Failure"
  shows   "s' = Failure"
  using assms
proof (induct rule: red_cmd_list.induct)
  case RedCmdListNil
  then show ?case by simp
next
  case (RedCmdListCons c s' cs s'')
  then show ?case using failure_stays_cmd by blast
qed

lemma failure_stays_cmd_list:
  assumes "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs, Failure\<rangle> [\<rightarrow>] s'"
  shows "s' = Failure"
  using assms
  by (simp add: failure_stays_cmd_list_aux)

lemma failure_red_cmd_list: "A,M,\<Lambda>',\<Gamma>,\<Omega> \<turnstile> \<langle>cs,Failure\<rangle> [\<rightarrow>] Failure"
  by (induction cs) (auto intro: red_cmd_list.intros RedPropagateFailure)

lemma finished_remains: 
  assumes "A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inr (), s) -n\<rightarrow>* (m',n')"
  shows "(m',n') = (Inr(), s)"
  using assms
proof (induction rule: rtranclp_induct2)
  case refl
  then show ?case by simp
next
  case (step a b a' b')
  with step.hyps(2) show ?case
    by (cases; simp)
qed

lemma forall_red:
  assumes "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>Forall ty e, n_s\<rangle> \<Down> v"
  shows "\<exists>b. (v = LitV (LBool b)) \<and> (b = (\<forall>v'. type_of_val A v' = (instantiate \<Omega> ty) \<longrightarrow> A, \<Lambda>, \<Gamma>, \<Omega> \<turnstile> \<langle>e, full_ext_env n_s v'\<rangle> \<Down> LitV (LBool True)))"
  using assms
proof (cases)
  case RedForAllTrue
  thus ?thesis by auto
next
  case (RedForAllFalse v')
  thus ?thesis 
    by (blast dest: expr_eval_determ(1))
qed

lemma exists_red:
  assumes "A, \<Lambda>, \<Gamma>, \<Omega> \<turnstile> \<langle>Exists ty e, n_s\<rangle> \<Down> v"
  shows "\<exists>b. (v = LitV (LBool b)) \<and> (b = (\<exists>v'. (type_of_val A v' = (instantiate \<Omega> ty)) \<and> A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e, full_ext_env n_s v'\<rangle> \<Down> LitV (LBool True)))"
  using assms
proof (cases)
  case RedExistsTrue
  thus ?thesis by auto
next
  case (RedExistsFalse)
  thus ?thesis 
   by (blast dest: expr_eval_determ(1))
qed

(* TODO: make more precise *)
lemma forallt_red_bool:
  assumes "A, \<Lambda>, \<Gamma>, \<Omega> \<turnstile> \<langle>ForallT e, n_s\<rangle> \<Down> v"
  shows "\<exists>b. (v = LitV (LBool b))"
  using assms
  by (cases; auto)

(* TODO: make more precise *)
lemma existst_red_bool:
  assumes "A, \<Lambda>, \<Gamma>, \<Omega> \<turnstile> \<langle>ExistsT e, n_s\<rangle> \<Down> v"
  shows "\<exists>b. (v = LitV (LBool b))"
  using assms
  by (cases; auto)

end