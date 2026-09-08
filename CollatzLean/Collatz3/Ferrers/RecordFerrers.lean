import CollatzLean.Collatz3.Ferrers.RecordView
import CollatzLean.Collatz3.Critical.RecordSkeleton
import CollatzLean.Collatz3.Critical.RecordLocalGeometry

/-!
# 互換 import: Record/Ferrers の責務分離

この filename は直前版との overlay 互換のため残す。

現在確定している層は次の通り。

* `Ferrers.RecordView`:
  任意 profile に deterministic cut list を付ける弱い view。Profile と `Equiv`。
* `Critical.CriticalRecordSkeleton`:
  positive roof anchor `[1]` から terminal までの strict rank/roof skeleton。
* `Critical.RecordLocalGeometry`:
  skeleton から local critical geometry を導く定義・補題群。
  `IsBestUpperWidth` はここで構成を保証する十分条件として使う。

真の `Critical.RecordFerrers` structure は現段階では定義しない。
`Ferrers.RecordFerrers` という alias も再導入しない。
exact な record-level tie / local carry 条件を確定してから完成形を定義する。
-/
