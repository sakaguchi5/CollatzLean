import CollatzLean.Collatz3.Bridge.CriticalRecord

/-!
# 互換 import: old CriticalRecordEquiv

直前版では strong Record--Ferrers まで `Equiv` と呼んでいたが、その主張は撤回する。
現在の exact equivalence は `CriticalWord <-> AdmissibleProfile <-> Ferrers.RecordView`。
strong `Critical.RecordFerrers` への接続は forgetful map と存在定理として扱う。
-/
