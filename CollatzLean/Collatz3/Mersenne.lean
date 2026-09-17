import CollatzLean.Collatz3.Mersenne.Basic
import CollatzLean.Collatz3.Mersenne.OneZero
import CollatzLean.Collatz3.Mersenne.ExitDepth
import CollatzLean.Collatz3.Mersenne.Word
import CollatzLean.Collatz3.Mersenne.MacroLine
import CollatzLean.Collatz3.Mersenne.OneZeroRegions

/-!
# Collatz3 Mersenne

Mersenne block の純粋整数算術、one-zero family、fixed `(d,r)` affine lift、
および one-zero obstruction の三領域 reduction をまとめる。

actual `Runs` への接続は Bridge 層へ分離したままにする。
-/
