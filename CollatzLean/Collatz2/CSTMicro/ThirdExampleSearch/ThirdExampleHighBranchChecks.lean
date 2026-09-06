import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleFiniteFamilyVerifier

/-! 高い枝の再帰的affine-family検査。大きい候補リストは生成しない。 -/
namespace Collatz2.CSTMicro.ThirdExampleSearch.CertifiedHigh

set_option maxRecDepth 4096
set_option maxHeartbeats 0

theorem branch65_checked : familyCheck 1000 (rootFamily 65) = true := by decide
#eval IO.println "branch 65 certified"
theorem branch62_checked : familyCheck 1000 (rootFamily 62) = true := by decide
#eval IO.println "branch 62 certified"
theorem branch59_checked : familyCheck 1000 (rootFamily 59) = true := by decide
#eval IO.println "branch 59 certified"
theorem branch56_checked : familyCheck 1000 (rootFamily 56) = true := by decide
#eval IO.println "branch 56 certified"
theorem branch54_checked : familyCheck 1000 (rootFamily 54) = true := by native_decide
#eval IO.println "branch 54 certified"
theorem branch51_checked : familyCheck 1000 (rootFamily 51) = true := by native_decide
#eval IO.println "branch 51 certified"

--ここからは重い
--アルゴリズム改善が必要

theorem branch48_checked : familyCheck 1000 (rootFamily 48) = true := by native_decide
#eval IO.println "branch 48 certified"
theorem branch46_checked : familyCheck 1000 (rootFamily 46) = true := by native_decide
#eval IO.println "branch 46 certified"
theorem branch43_checked : familyCheck 1000 (rootFamily 43) = true := by native_decide
#eval IO.println "branch 43 certified"
/-
40は重いとかいう次元ではない
-/

theorem branch40_checked : familyCheck 1000 (rootFamily 40) = true := by native_decide
#eval IO.println "branch 40 certified"

end Collatz2.CSTMicro.ThirdExampleSearch.CertifiedHigh
