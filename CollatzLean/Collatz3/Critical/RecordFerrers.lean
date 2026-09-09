import CollatzLean.Collatz3.Ferrers.RecordFerrers

/-!
# 互換 import: 真の RecordFerrers の正本

`RecordFerrers` の完成定義は `Collatz3.Ferrers.RecordFerrers` に置く。
この filename は旧 import との互換のためだけに残す。

現在の正本は

`AdmissibleProfile + (1 < width) + canonical exact carry law`

という最小 subtype である。

* deterministic cuts / lengths、
* `CriticalRecordSkeleton`、
* `NoRecordLevelTie`、
* local critical geometry、
* primitive / best-upper

は field に保存せず、すべて派生 theorem または十分条件として扱う。
-/
