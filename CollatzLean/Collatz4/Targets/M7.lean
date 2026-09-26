import CollatzLean.Collatz4.Targets.M7.Constants
import CollatzLean.Collatz4.Targets.M7.QBound
import CollatzLean.Collatz4.Targets.M7.LengthBound
import CollatzLean.Collatz4.Targets.M7.ResidualBounds
import CollatzLean.Collatz4.Targets.M7.ResidualBridge
import CollatzLean.Collatz4.Targets.M7.ForwardReduction
import CollatzLean.Collatz4.Targets.M7.Witness
import CollatzLean.Collatz4.Targets.M7.LivePruning
import CollatzLean.Collatz4.Targets.M7.FiniteCertificate
import CollatzLean.Collatz4.Targets.M7.Result

/-!
# Collatz4.Targets.M7

二進数族 `101, 1011, 10111, ...` の研究における `M = 7` 個別ケース。

このファイルは M=7 の特殊化だけを集約する。M=5,9,11,... は同じ階層に
独立した target directory として追加する。
-/
