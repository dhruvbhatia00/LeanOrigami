import HexNumberField

/-!
# Compiled exact arithmetic

This small, separately precompiled library loads Hex's executable number-field
implementation into Lean's interpreter and language server. It deliberately
imports no Mathlib proofs or origami tactics. Certification remains checked by
the kernel; native code is used only for discovery and certificate preparation.
-/
