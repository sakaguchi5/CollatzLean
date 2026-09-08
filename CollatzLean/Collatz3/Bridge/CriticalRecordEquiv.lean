import CollatzLean.Collatz3.Bridge.CriticalRecord

/-!
# 互換 import: old CriticalRecordEquiv

exact equivalence は

`CriticalWord <-> AdmissibleProfile <-> Ferrers.RecordView`

までである。

`CriticalRecordSkeleton` は追加条件を持つため Profile との `Equiv` は主張しない。
真の `RecordFerrers` は record-level tie と local carry の exact 条件を確定するまで
まだ定義しない。旧 filename は import 互換のためだけに残す。
-/
