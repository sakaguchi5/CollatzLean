import CollatzLean.Collatz3.Critical.RecordCarryExact

/-!
# 互換 import: RecordFerrers の定義は一時的に未確定

この filename は直前版との import 互換のため残す。

現在ここでは `RecordFerrers` structure をまだ定義しない。
ただし local geometry に必要な exact 条件は `Critical.RecordCarryExact` で確定した。

* local prefix failure
  `<->` premature roof return + Beatty carry `1`,
* terminal minimality
  `<->` terminal Beatty carry `0`,
* `RecordCarryCompatibleFrom`
  `<->` `LocalCriticalBlocksFrom`。

従って次に真の `RecordFerrers` を再導入するときは、
`CriticalRecordSkeleton` と exact carry compatibility だけを独立条件として残し、
`IsPrimitiveWidth` / `IsBestUpperWidth` / local `CriticalWord` は
十分条件または派生 theorem として扱える。
-/
