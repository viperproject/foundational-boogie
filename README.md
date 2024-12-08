# Isabelle formalization of Boogie
This is an Isabelle formalization of the Boogie intermediate verification language.
Moreover, it contains helper theory files to support the [validation of the Boogie 
verifier](https://github.com/gauravpartha/boogie_proofgen/), which is currently being
developed.

The theory files are compatible with Isabelle 2022 (and not backwards 
compatible with older versions).

## More details on the theory files
The theory files can be split into two categories: the formalization of the 
Boogie language and the theory files that help certifying the different phases.

The theory files for the Boogie language itself are given by:
* `Lang.thy`: Syntax of the Boogie language
* `BoogieDeBruijn.thy`: Some formalization on DeBruijn binders
* `Semantics.thy`: Semantics of the Boogie language and definition of procedure 
correctness (only describes control-flow graphs in terms of control flow)
* `Ast.thy`: Semantics of Boogie AST (uses `Semantics.thy` for control flow independent elements)
* `Util.thy`: Some helper lemmas
* `Typing.thy`: Boogie's type system
* `TypeSafety.thy`: Type safety proof for expressions

The theory files for helping the certification of the different phases are given by:
* `VCExprHelper.thy`: Theory that helps relate a Boogie expression with a corresponding 
expression in the verification condition (VC).
* `VCPhaseML.thy`: Isabelle tactics used to relate Boogie expressions with 
corresponding VC expressions. The tactics are written in SML as is common for Isabelle.
* `HelperML.thy`: Some helper ML functions.
* `VCHints.thy`: Defines a SML datatype that is used by the tactics in `VCPhaseML.thy`.
* `Passification.thy`: Main theory that helps deal with the certification of the passification phase.
* `PassificationEndToEnd.thy`: Provides lemmas and definitions that help lift the global block
theorem of the entry block in the passification phase to a theorem that shows
the passification source CFG is correct under the assumption of the VC.
* `PassificationML.thy`: Some ML tactics used in the certification of the 
passification phase.
* `BackedgeElim.thy`: Main theory that helps deal with the certification of the CFG-to-DAG phase.
* `CFGOptimizationsLoop.thy`: Main theory that helps deal with the certification of the CFG optimizations phase.
* `Ast_to_Cfg_Validation.thy`: Main theory that helps deal with the certification of the AST-to-CFG phase.
* `TypingHelper.thy`: Helper lemmas/definitions for proving that expressions are well-typed.
* `TypingML.thy`: ML tactic to prove that an expression is well-typed.

## Including as a session
The `BoogieLang/ROOT` file defines an Isabelle session that can be imported by adding the
`BoogieLang` directory to the `ROOTS` file in the Isabelle home directory.
