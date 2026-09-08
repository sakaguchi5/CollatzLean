import CollatzLean.Collatz3.Ferrers.RecordView
import CollatzLean.Collatz3.Critical.RecordFerrers

/-!
# 互換 import: RecordFerrers の責務分離

この filename は直前版との overlay 互換のため残す。

* `Ferrers.RecordView`:
  任意 profile に deterministic cut list を付ける弱い view。Profile と `Equiv`。
* `Critical.RecordFerrers`:
  positive roof anchor `[1]` から terminal まで strict record blocks を連結する強い幾何。

ここでは `Ferrers.RecordFerrers` という alias を再導入しない。
弱い view と強い Record--Ferrers を同じ型名で混同しないためである。
-/
