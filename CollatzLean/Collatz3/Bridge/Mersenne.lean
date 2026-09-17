import CollatzLean.Collatz3.Mersenne
import CollatzLean.Collatz3.Bridge.MersenneRuns

/-!
# Collatz3 Bridge: Mersenne

M2 の Mersenne block と actual odd-only `Runs` の接続をまとめる集約 import。

低層の `Mersenne` package は semantics 非依存のまま保ち、
actual Collatz realization はこの Bridge 入口から読む。
-/
