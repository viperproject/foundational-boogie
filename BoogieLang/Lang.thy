section \<open>Syntax of the Boogie language\<close>

theory Lang
  imports Main HOL.Real
begin

type_synonym fname = string (* function name *)
type_synonym vname = nat (* variable name, de-bruijn index *)
type_synonym pname = string (* procedure name *)

datatype lit =  LBool bool  | LInt int | LReal real

datatype binop = Eq | Neq | Add | Sub | Mul | Div | RealDiv | Mod | Lt | Le | Gt | Ge | And | Or | Imp | Iff
datatype unop = Not | UMinus | IntToReal

datatype prim_ty 
 = TBool | TInt | TReal

type_synonym tcon_id = string (* type constructor id *)

datatype ty
  = TVar nat | (* type variables as de-bruijn indices *)
    TPrim prim_ty | (* primitive types *)
    TCon tcon_id "ty list" (* type constructor *)

primrec type_of_lit :: "lit \<Rightarrow> prim_ty"
  where 
    "type_of_lit (LBool _) = TBool"
  | "type_of_lit (LInt _)  = TInt"
  | "type_of_lit (LReal _) = TReal"

datatype expr
  =
    Var vname
  | BVar nat (* de-bruijn index *)
  | Lit lit
  | UnOp unop "expr"
  | BinOp "(expr)" binop "(expr)" ("_ \<guillemotleft>_\<guillemotright> _" [80,0,81] 80) 
  | FunExp fname "ty list" "(expr list)" (* second argument: type instantiation *)
  | CondExp expr expr expr
  | Old expr
(* value quantification *)
  | Forall ty expr
  | Exists ty expr
(* type quantification *)
  | ForallT expr 
  | ExistsT expr

text \<open>We use a De-Bruijn encoding for bound variables \<^term>\<open>BVar\<close> and names for local/global variables 
\<^term>\<open>Var\<close> (where names are natural numbers. While this setup suggests that we use the locally 
nameless encoding, this is not the case (see Semantics.thy for more details).\<close>

(* multi-assign and multi-havoc not supported for now *)
datatype cmd
 = Assert expr
 | Assume expr
 | Assign vname expr
 | Havoc vname
 | ProcCall pname "expr list" "vname list"

text \<open>Function declarations: number of type parameters, argument types and return type\<close>
type_synonym fdecl = "(fname \<times> nat \<times> ty list \<times> ty)"
type_synonym fdecls = "fdecl list"

text \<open>Variable declarations: the optional expression represents the where-clause\<close>
type_synonym vdecl = "vname \<times> ty \<times> (expr option)"
type_synonym vdecls = "vdecl list"

text \<open>Type constructor declarations: number of arguments for each constructor\<close>
type_synonym tdecls = "(tcon_id \<times> nat) list"

text \<open>Basic blocks as a list of commands\<close>
type_synonym block = "cmd list"

text \<open>Identify nodes in the CFG by natural numbers. We always use block identifiers from 0 to N-1 when
there N blocks in the CFG\<close>
type_synonym node = "nat"
 
record mbodyCFG =
  entry :: "node"
  out_edges :: "(node list) list"
  node_to_block :: "block list"

text \<open>
Let N be the number of blocks in the CFG.
CFG of a procedure body is represented by:
  1) A block id indicating the entry of the CFG (\<^term>\<open>entry\<close>)
  2) The outgoing edges for each block. We represent this is as a list of length N (\<^term>\<open>out_edges\<close>).
     The outgoing block ids for the block with id i are given by i-th element in the list.
  3) A mapping from block ids to the corresponding list of commands. We represent this as a list of
     length N, where the list of commands for the block with id i are given by the i-th element in
     the list.
\<close>

text \<open>Procedure pre- and postconditions contain a boolean to indicate whether they are free (true) or 
      checked (false).\<close>
record 'struct_ty procedure =
  proc_ty_args :: nat
  proc_args :: vdecls
  proc_rets :: vdecls
  proc_modifs :: "vname list"
  proc_pres :: "(expr \<times> bool) list" 
  proc_posts :: "(expr \<times> bool) list"
  proc_body :: "(vdecls \<times> 'struct_ty) option"

fun proc_checked_pres :: "'struct_ty procedure \<Rightarrow> expr list"
  where "proc_checked_pres p = map fst (filter (\<lambda>x. \<not> snd(x)) (proc_pres p))"

fun proc_free_pres :: "'struct_ty procedure \<Rightarrow> expr list"
  where "proc_free_pres p = map fst (filter (\<lambda>x. snd(x)) (proc_pres p))"

fun proc_all_pres :: "'struct_ty procedure \<Rightarrow> expr list"
  where "proc_all_pres p = map fst (proc_pres p)"

fun proc_checked_posts :: "'struct_ty procedure \<Rightarrow> expr list"
  where "proc_checked_posts p = map fst (filter (\<lambda>x. \<not> snd(x)) (proc_posts p))"

fun proc_all_posts :: "'struct_ty procedure \<Rightarrow> expr list"
  where "proc_all_posts p = map fst (proc_posts p)"

fun proc_free_posts :: "'struct_ty procedure \<Rightarrow> expr list"
  where "proc_free_posts p = map fst (filter (\<lambda>x. snd(x)) (proc_posts p))"

definition exprs_to_only_checked_spec :: "expr list \<Rightarrow> (expr \<times> bool) list"
  where "exprs_to_only_checked_spec es = map (\<lambda>e. (e, False)) es"
text \<open>For cases where there are no free pre- and postconditions, one can use
 \<^term>\<open>exprs_to_only_checked_spec\<close> to lift expressions to checked pre- and postconditions.
The proof generation currently does not support free specifications.\<close>

lemma exprs_to_only_checked_spec_1: "es = map fst (exprs_to_only_checked_spec es)"
  unfolding exprs_to_only_checked_spec_def
  by (induction es) auto

lemma exprs_to_only_checked_spec_2: "es = map fst (filter (\<lambda>x. \<not> snd x) (exprs_to_only_checked_spec es))"
  unfolding exprs_to_only_checked_spec_def
  by (induction es) auto

type_synonym 'struct_ty pdecl = "pname \<times> 'struct_ty procedure"

text \<open>An axiom is a boolean expression that can refer to constants.\<close>
type_synonym axiom = expr

record 'struct_ty prog =
  prog_ty_constr :: tdecls 
  prog_funcs :: fdecls
  prog_consts :: vdecls
  prog_globals :: vdecls
  prog_axioms :: "axiom list"
  prog_procs :: "'struct_ty pdecl list"

text \<open>Type declarations are ignored by the semantics (all possible types are taken into account, which
is more general and the resulting semantics can be reduced to the case where one only quantifies over 
those types that can be constructed via the type declarations that appear in the program).\<close>

primrec closed :: "ty \<Rightarrow> bool"
  where
    "closed (TVar i) = False"
  | "closed (TPrim prim_ty) = True"
  | "closed (TCon tcon_id ty_args) = list_all closed ty_args"

end