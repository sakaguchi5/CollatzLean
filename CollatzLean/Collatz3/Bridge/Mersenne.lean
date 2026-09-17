import CollatzLean.Collatz3.Mersenne
import CollatzLean.Collatz3.Bridge.MersenneRuns
import CollatzLean.Collatz3.Bridge.CycleResidue
import CollatzLean.Collatz3.Bridge.MersenneResidue
import CollatzLean.Collatz3.Bridge.MersenneCanonical
import CollatzLean.Collatz3.Bridge.OneZeroRunsDerived

/-!
# Collatz3 Bridge: Mersenne / residue obstruction

Mersenne block と actual odd-only `Runs` の接続に加え、
3進 residue lift、canonical lift、one-zero exact exponent word をまとめる集約 import。

低層 `Mersenne` package は semantics 非依存のまま保つ。
-/
