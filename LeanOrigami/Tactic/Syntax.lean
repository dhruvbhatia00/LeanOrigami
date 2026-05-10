import Lean

/-!
# Text syntax for origami construction scripts

This file only declares syntax.  Elaboration lives in
`LeanOrigami.Tactic.Elab`.
-/

declare_syntax_cat origami_step

syntax "point" ident ":=" "origin" : origami_step
syntax "point" ident ":=" "one" : origami_step
syntax "line" ident ":=" "axiom1" ident ident : origami_step
syntax "line" ident ":=" "axiom2" ident ident : origami_step
syntax "line" ident ":=" "axiom4" ident ident : origami_step
syntax "point" ident ":=" "intersection" ident ident : origami_step
syntax "exact_x" ident : origami_step
syntax "exact_y" ident : origami_step

syntax (name := origamiConstruct) "origami_construct" ppLine origami_step* : tactic
