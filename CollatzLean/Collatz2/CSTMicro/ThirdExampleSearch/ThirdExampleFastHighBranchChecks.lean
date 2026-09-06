import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleFastFamilyVerifier
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleHighBranchDispatch

/-!
Fast API 互換用の高枝定理。

`fastFamilyCheck` は現在 `familyCheck` の別名なので、
ここでは native_decide を再実行しない。
通常版で既に認証済みの10枝を定理として再利用する。
-/
namespace Collatz2.CSTMicro.ThirdExampleSearch.CertifiedHigh

theorem fastBranch65_checked : fastFamilyCheck 1000 (rootFamily 65) = true := by
  simpa [fastFamilyCheck] using branch65_checked

theorem fastBranch62_checked : fastFamilyCheck 1000 (rootFamily 62) = true := by
  simpa [fastFamilyCheck] using branch62_checked

theorem fastBranch59_checked : fastFamilyCheck 1000 (rootFamily 59) = true := by
  simpa [fastFamilyCheck] using branch59_checked

theorem fastBranch56_checked : fastFamilyCheck 1000 (rootFamily 56) = true := by
  simpa [fastFamilyCheck] using branch56_checked

theorem fastBranch54_checked : fastFamilyCheck 1000 (rootFamily 54) = true := by
  simpa [fastFamilyCheck] using branch54_checked

theorem fastBranch51_checked : fastFamilyCheck 1000 (rootFamily 51) = true := by
  simpa [fastFamilyCheck] using branch51_checked

theorem fastBranch48_checked : fastFamilyCheck 1000 (rootFamily 48) = true := by
  simpa [fastFamilyCheck] using branch48_checked

theorem fastBranch46_checked : fastFamilyCheck 1000 (rootFamily 46) = true := by
  simpa [fastFamilyCheck] using branch46_checked

theorem fastBranch43_checked : fastFamilyCheck 1000 (rootFamily 43) = true := by
  simpa [fastFamilyCheck] using branch43_checked

theorem fastBranch40_checked : fastFamilyCheck 1000 (rootFamily 40) = true := by
  simpa [fastFamilyCheck] using branch40_checked

theorem fastHighBranches_checked {a : Nat}
    (ha : a ∈ [65,62,59,56,54,51,48,46,43,40]) :
    fastFamilyCheck 1000 (rootFamily a) = true := by
  simpa [fastFamilyCheck] using (highBranches_checked ha)

end Collatz2.CSTMicro.ThirdExampleSearch.CertifiedHigh
