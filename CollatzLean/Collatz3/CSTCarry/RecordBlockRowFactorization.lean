import CollatzLean.Collatz3.CSTCarry.ProfileBlockRows
import CollatzLean.Collatz3.Ferrers.RecordArithmeticFactorization

/-!
# Collatz3 CSTCarry: canonical Record block と profile rows の exact factorization

canonical record lengths は forward に `1 -> m` を覆う。
carry rows は逆向きに読むので、各 block row list は terminal block から逆順に連結される。

最後に canonical anchor より前の critical index `0` row が一本だけ残る。
-/

namespace Collatz3
namespace CSTCarry

open Critical
open Ferrers

/--
forward block length 列を、carry 向きでは逆順 block concatenation として row list にする。
-/
def profileRowsFromLengths
    {m : ℕ}
    (h : Profile m) :
    (a : ℕ) → (rs : List ℕ) → a + rs.sum ≤ m → List FerrersRow
  | _a, [], _hEnd => []
  | a, r :: rs, hEnd =>
      profileRowsFromLengths h (a + r) rs (by
        simpa [List.sum_cons, Nat.add_assoc] using hEnd) ++
      profileBlockCarryRows h a r (by
        have : a + r ≤ a + (r + rs.sum) := by omega
        exact le_trans this (by
          simpa [List.sum_cons, Nat.add_assoc] using hEnd))

/-- block length 列全体の rows は、その covered interval の row list と exact に一致する。 -/
theorem profileRowsFromLengths_eq_blockRows
    {m : ℕ}
    (h : Profile m) :
    ∀ (a : ℕ) (rs : List ℕ) (hEnd : a + rs.sum ≤ m),
      profileRowsFromLengths h a rs hEnd =
        profileBlockCarryRows h a rs.sum hEnd
  | a, [], hEnd => by
      simp only [profileRowsFromLengths, List.sum_nil, profileBlockCarryRows_zero]
  | a, r :: rs, hEnd => by
      have hTailEnd : (a + r) + rs.sum ≤ m := by
        simpa [List.sum_cons, Nat.add_assoc] using hEnd
      rw [profileRowsFromLengths]
      rw [profileRowsFromLengths_eq_blockRows h (a + r) rs hTailEnd]
      have hAdd := profileBlockCarryRows_add
        h a r rs.sum (by
          simpa [List.sum_cons, Nat.add_assoc] using hEnd)
      simpa [List.sum_cons, Nat.add_assoc] using hAdd.symm

namespace Ferrers.RecordFerrers

/-- canonical record blocks を carry 順へ並べた row list。 -/
def canonicalRecordCarryRows
    {m : ℕ}
    (R : RecordFerrers m) : List FerrersRow :=
  profileRowsFromLengths
    R.profile.1
    initialRoofAnchor
    (canonicalRecordLengths R.profile.1)
    (by
      rw [R.initialRoofAnchor_add_sum_canonicalRecordLengths_eq_width])

/-- canonical record rows は interval `[1,m)` の profile rows 全体と一致する。 -/
theorem canonicalRecordCarryRows_eq_suffix
    {m : ℕ}
    (R : RecordFerrers m) :
    canonicalRecordCarryRows R =
      profileBlockCarryRows R.profile.1 1 (m - 1)
  (by
  have hm : 1 < m := R.one_lt_width
  omega) := by
  unfold canonicalRecordCarryRows
  rw [profileRowsFromLengths_eq_blockRows]
  have hSum := canonicalRecordLengths_sum
    (h := R.profile.1) R.one_lt_width
  simp [initialRoofAnchor, hSum]

/--
whole `profileCarryRows` は canonical record rows と index `0` の zero-defect row に分解される。
-/
theorem profileCarryRows_eq_canonicalRecordRows_append_zero
    {m : ℕ}
    (R : RecordFerrers m) :
    profileCarryRows R.profile.1 =
      canonicalRecordCarryRows R ++
        [profileFerrersRow R.profile.1
          ⟨0, lt_trans (by decide : 0 < (1 : ℕ)) R.one_lt_width⟩] := by
  have hmPos : 0 < m :=
    lt_trans (by decide : 0 < (1 : ℕ)) R.one_lt_width
  have hOneLe : 1 ≤ m :=
    Nat.le_of_lt R.one_lt_width
  have hWidth' : m - 1 + 1 = m :=
    Nat.sub_add_cancel hOneLe
  have hWidth : 1 + (m - 1) = m := by
    simpa [Nat.add_comm] using hWidth'
  have hOneEnd : 0 + 1 ≤ m := by
    simpa using hOneLe
  have hAddEnd : 0 + (1 + (m - 1)) ≤ m := by
    simp [hWidth]
  rw [← profileBlockCarryRows_zero_full R.profile.1]
  rw [canonicalRecordCarryRows_eq_suffix R]
  have hAdd :=
    profileBlockCarryRows_add
      R.profile.1
      0
      1
      (m - 1)
      hAddEnd
  have hHead :
      profileBlockCarryRows R.profile.1 0 1 hOneEnd =
        [profileFerrersRow R.profile.1 ⟨0, hmPos⟩] := by
    simp [profileBlockCarryRows]
  rw [hHead] at hAdd
  simpa [hWidth] using hAdd

end Ferrers.RecordFerrers

end CSTCarry
end Collatz3
