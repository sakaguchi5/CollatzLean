import CollatzLean.Collatz4.Targets.M7.Constants
import CollatzLean.Collatz4.Targets.M7.QBound
import CollatzLean.Collatz4.Targets.M7.LengthBound
import CollatzLean.Collatz4.Targets.M7.ResidualBounds
import CollatzLean.Collatz4.Targets.M7.ResidualBridge
import CollatzLean.Collatz4.Targets.M7.ForwardReduction
import CollatzLean.Collatz4.Targets.M7.Witness
import CollatzLean.Collatz4.Targets.M7.LivePruning
import CollatzLean.Collatz4.Targets.M7.FiniteCertificate

import CollatzLean.Collatz4.Targets.M7.CompressionData
import CollatzLean.Collatz4.Targets.M7.StructuralCompression
import CollatzLean.Collatz4.Targets.M7.StructuralResult

import CollatzLean.Collatz4.Targets.M7.Result

import CollatzLean.Collatz4.Targets.M7.MasterWitness
import CollatzLean.Collatz4.Targets.M7.MasterBridge
import CollatzLean.Collatz4.Targets.M7.MasterToWitness

/-!
# Collatz4.Targets.M7

二進数族 `101, 1011, 10111, ...` の研究における `M = 7` 個別ケース。

finite exclusion は現在二系統ある。

* 従来の2179候補直接 certificate
* `2179 -> 97 -> (58 + 39)` の同期合流圧縮による構造証明

actual reachability からは

`OddQBranchReachable 7 -> HasM7MasterWitness`

まで exact に接続済み。

`MasterToWitness` では、その先に必要な fixed record extraction を型として明示し、
それが証明されれば `¬ OddQBranchReachable 7` まで直ちに閉じることを証明する。
現在、その extraction 自体は未証明であり、固定 record を仮定なしに強制することが
次の数学的課題である。
-/
