import CollatzLean.Collatz3.Ferrers.RecordView
import CollatzLean.Collatz3.Critical.RecordSkeleton
import CollatzLean.Collatz3.Critical.RecordFerrers

/-!
# 互換 import: Record/Ferrers の責務分離

この filename は直前版との overlay 互換のため残す。

* `Ferrers.RecordView`:
  任意 profile に deterministic cut list を付ける弱い view。Profile と `Equiv`。
* `Critical.CriticalRecordSkeleton`:
  positive roof anchor `[1]` から terminal までの strict rank/roof skeleton。
* `Critical.RecordFerrers`:
  width-only best-upper 算術により local critical blocks まで持ち上げた full 層。

`Ferrers.RecordFerrers` という alias は再導入しない。
異なる三層を同じ型名で混同しないためである。
-/
