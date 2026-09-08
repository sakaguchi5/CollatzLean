import CollatzLean.Collatz3.Critical.RecordLocalGeometry

/-!
# 互換 import: RecordFerrers の定義は一時的に未確定

この filename は直前版との import 互換のため残す。

現在ここでは `RecordFerrers` structure を定義しない。
直前版の structure は

* `CriticalRecordSkeleton`,
* `IsBestUpperWidth`,
* `TerminalMinimalFrom`

を束ねていたが、`IsBestUpperWidth` は genuine local critical geometry の必要条件ではなく、
構成を一括保証する十分条件であることが分かった。

そのため真の `RecordFerrers` は、record-level tie と local carry の exact 条件を
確定するまで再導入しない。
局所幾何の定義・派生定理・best-upper による十分条件は
`Critical.RecordLocalGeometry` に置く。
-/
