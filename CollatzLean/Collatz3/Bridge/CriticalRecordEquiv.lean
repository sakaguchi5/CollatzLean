import CollatzLean.Collatz3.Critical.WordProfileEquiv
import CollatzLean.Collatz3.Ferrers.RecordFerrers

/-!
# Collatz3: Word <-> Profile <-> RecordFerrers

有限 critical first-passage shape の三つの表現を exact `Equiv` で結ぶ。

  CriticalWord m
      <-> AdmissibleProfile m
      <-> RecordFerrers m

最初の同値は非自明で、prefix depth の有限差分による word/profile の相互復元を使う。
二つ目は admissible profile に deterministic な proper-record decomposition を付ける view 同値。

absolute Collatz start 値はこの同値には含めない。
actual `Runs` への意味論的 realization は別 Bridge として扱う。
-/

namespace Collatz3
namespace Bridge

/-- Word <-> finite profile の exact equivalence。 -/
def criticalWordProfileEquiv
    (m : ℕ)
    (hm : 0 < m) :
    Critical.CriticalWord m ≃ Critical.AdmissibleProfile m :=
  Critical.criticalWordEquivAdmissibleProfile m hm

/-- finite profile <-> canonical Record--Ferrers view の exact equivalence。 -/
noncomputable def profileRecordFerrersEquiv
    (m : ℕ) :
    Critical.AdmissibleProfile m ≃ Ferrers.RecordFerrers m :=
  Ferrers.admissibleProfileEquivRecordFerrers m

/--
positive width では CriticalWord と canonical Record--Ferrers view も exact `Equiv`。
二つの既証明同値を合成しただけで、新しい意味論的仮定は追加しない。
-/
noncomputable def criticalWordRecordFerrersEquiv
    (m : ℕ)
    (hm : 0 < m) :
    Critical.CriticalWord m ≃ Ferrers.RecordFerrers m :=
  (criticalWordProfileEquiv m hm).trans
    (profileRecordFerrersEquiv m)

/-- Word -> RecordFerrers -> underlying profile は直接 profile 抽出と一致。 -/
theorem criticalWordRecordFerrers_profile
    (m : ℕ)
    (hm : 0 < m)
    (W : Critical.CriticalWord m) :
    ((criticalWordRecordFerrersEquiv m hm W).profile :
      Critical.AdmissibleProfile m) =
      criticalWordProfileEquiv m hm W := by
  rfl

/-- RecordFerrers -> Word は underlying profile からの finite-difference reconstruction。 -/
theorem criticalWordRecordFerrers_symm_eq
    (m : ℕ)
    (hm : 0 < m)
    (R : Ferrers.RecordFerrers m) :
    (criticalWordRecordFerrersEquiv m hm).symm R =
      (criticalWordProfileEquiv m hm).symm R.profile := by
  rfl

end Bridge
end Collatz3
