import CollatzLean.Collatz3.Mersenne
import CollatzLean.Collatz3.Bridge.MersenneRuns
import CollatzLean.Collatz3.Bridge.CycleResidue

/-!
# Collatz3 Bridge: Mersenne / residue obstruction

Mersenne block と actual odd-only `Runs` の接続に加え、
cycle residue の一歩必要条件をまとめる集約 import。

低層 `Mersenne` package は semantics 非依存のまま保つ。
-/
