import LeanOrigamiTests.Runtime

/-!
# Interpreter integration

Run with `lake lean LeanOrigamiTests/Interpreter.lean`. Lake supplies the
native libraries needed by Hex. Reuse the runtime suite to check the execution
path used by elaborators and widgets, separately from the compiled executable.
These assertions are not proof premises.
-/

#eval main
