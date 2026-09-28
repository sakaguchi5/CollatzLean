import CollatzLean.Collatz3.Ferrers.RecordFerrers
import CollatzLean.Collatz3.CSTCarry.RecordBlockRowFactorization
import CollatzLean.Collatz3.CSTCarry.CarryDeterministicSplit
import CollatzLean.Collatz3.CSTCarry.ZeroDefectHead

/-!
# Collatz3 CSTCarry: canonical Record rows と ternary digits の lossless split

row factorization が得られたので、deterministic carry recurrence の append lawを使って
canonical ternary digits / final carry も同じ場所で exact に分割する。
-/

namespace Collatz3
open Ferrers
namespace CSTCarry

--open Critical


namespace Ferrers.RecordFerrers

/-- canonical record rows を走り終えた時点の carry。 -/
def canonicalRecordRowsFinalCarry
    {m : ℕ}
    (R : RecordFerrers m)
    (H E : ℕ) : ℕ :=
  canonicalFinalCarry H (canonicalRecordCarryRows R) E

/-- canonical record rows に対応する ternary digit slice。 -/
def canonicalRecordRowsDigits
    {m : ℕ}
    (R : RecordFerrers m)
    (H E : ℕ) : List ℕ :=
  canonicalCarryDigits H (canonicalRecordCarryRows R) E

/-- whole canonical digits は record suffix digits と最後の zero-row digit に exact 分解される。 -/
theorem canonicalCarryDigits_profileRows_eq_record_append_zero
    {m : ℕ}
    (R : RecordFerrers m)
    (H E : ℕ) :
    canonicalCarryDigits H (profileCarryRows R.profile.1) E =
      (canonicalRecordRowsDigits R) H E ++
        canonicalCarryDigits H
          [profileFerrersRow R.profile.1
            ⟨0,
              lt_trans
                (by decide : 0 < (1 : ℕ))
                R.one_lt_width⟩]
          (canonicalRecordRowsFinalCarry R H E) := by
  have hmPos : 0 < m :=
    lt_trans
      (by decide : 0 < (1 : ℕ))
      R.one_lt_width
  rw [profileCarryRows_eq_canonicalRecordRows_append_zero R]
  exact canonicalCarryDigits_append
    H
    (canonicalRecordCarryRows R)
    [profileFerrersRow R.profile.1 ⟨0, hmPos⟩]
    E


/-- whole canonical final carry は record suffix final carry を zero row に渡したもの。 -/
theorem canonicalFinalCarry_profileRows_eq_zero_after_record
    {m : ℕ}
    (R : RecordFerrers m)
    (H E : ℕ) :
    canonicalFinalCarry H (profileCarryRows R.profile.1) E =
      canonicalFinalCarry H
        [profileFerrersRow R.profile.1
          ⟨0,
            lt_trans
              (by decide : 0 < (1 : ℕ))
              R.one_lt_width⟩]
        (canonicalRecordRowsFinalCarry R H E) := by
  have hmPos : 0 < m :=
    lt_trans
      (by decide : 0 < (1 : ℕ))
      R.one_lt_width
  rw [profileCarryRows_eq_canonicalRecordRows_append_zero R]
  exact canonicalFinalCarry_append
    H
    (canonicalRecordCarryRows R)
    [profileFerrersRow R.profile.1 ⟨0, hmPos⟩]
    E


/--
record suffix の final carry が strict modulus bound 内なら、whole profile の final carry も strict。
最後の index `0` row は defect `0` なので strictness を保存する。
-/
theorem canonicalFinalCarry_profileRows_lt_of_recordRows_lt
    {m : ℕ}
    (R : RecordFerrers m)
    (H E : ℕ)
    (hRecord : canonicalRecordRowsFinalCarry R H E < 2 ^ H) :
    canonicalFinalCarry H (profileCarryRows R.profile.1) E < 2 ^ H := by
  have hmPos : 0 < m :=
    lt_trans
      (by decide : 0 < (1 : ℕ))
      R.one_lt_width
  rw [canonicalFinalCarry_profileRows_eq_zero_after_record R H E]
  simpa [canonicalRecordRowsFinalCarry] using
    canonicalFinalCarry_profileZero_singleton_lt
      R.profile.1
      hmPos
      H
      (canonicalRecordRowsFinalCarry R H E)
      hRecord

end Ferrers.RecordFerrers

end CSTCarry
end Collatz3
