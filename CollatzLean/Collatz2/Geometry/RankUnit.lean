import CollatzLean.Collatz2.Geometry.Center
import CollatzLean.Collatz2.Geometry.RankPath
import Mathlib.Data.ZMod.Basic

/-!
# Collatz2 Geometry: rank-unit shadow

primitive exponent pair `(p,H)` に対して modular root `u` を選び

  u^p = 2
  u^H = 3

と読める場合、proper cut rank `d_k` と normalized translation monomial

  M_k = 2^h_k * 3^(p-k)

は exact に

  u^d_k * M_k = 3^p

を満たす。

このファイルは Bézoutによる `u` の具体選択とは分離し、unit packet を受け取った後の
rank geometry を lossless に証明する。
-/

namespace Collatz2
namespace Word

/-- terminal negative gap。FirstCrossing では正。 -/
def terminalGap (w : Word) : ℕ :=
  2 ^ twoSteps w - 3 ^ oddSteps w

/-- `terminalGap` は transfer の natural center gap そのもの。 -/
@[simp] theorem terminalGap_eq_centerGap (w : Word) :
    terminalGap w = (AffineTransfer.ofWord w).centerGap := by
  rfl

/-- FirstCrossing terminal gap は正。 -/
theorem FirstCrossing.terminalGap_pos
    {w : Word}
    (hF : FirstCrossing w) :
    0 < terminalGap w := by
  unfold terminalGap
  exact Nat.sub_pos_of_lt
    ((contracting_iff_threePow_lt_twoPow).1 hF.terminalContracting)

/--
rank unit packet。
`u^p=2`, `u^H=3` を terminal gap modulus 上で保持する。
-/
structure RankUnitData (w : Word) where
  gap_pos : 0 < terminalGap w
  unit : (ZMod (terminalGap w))ˣ
  unit_pow_oddSteps :
    ((↑unit : ZMod (terminalGap w)) ^ oddSteps w) =
      ((2 : ℕ) : ZMod (terminalGap w))
  unit_pow_twoSteps :
    ((↑unit : ZMod (terminalGap w)) ^ twoSteps w) =
      ((3 : ℕ) : ZMod (terminalGap w))

namespace RankUnitData

/--
proper FirstCrossing cut の normalized monomial は rank だけで unit-direction が決まる。

  u^d_k * M_k = 3^p.
-/
theorem cut_certificate
    {w : Word}
    (R : RankUnitData w)
    (hF : FirstCrossing w)
    {k : ℕ}
    (hkPos : 0 < k)
    (hkLt : k < oddSteps w) :
    ((↑R.unit : ZMod (terminalGap w)) ^ chordRank w k) *
        ((normalizedCutTerm w k : ℕ) : ZMod (terminalGap w)) =
      ((3 ^ oddSteps w : ℕ) : ZMod (terminalGap w)) := by
  have hlt := hF.prefixSlope_cross hkPos hkLt
  have hle :
      oddSteps w * prefixTwoDepth w k ≤ twoSteps w * k :=
    Nat.le_of_lt hlt
  have hrank :
      chordRank w k + oddSteps w * prefixTwoDepth w k =
        twoSteps w * k := by
    unfold chordRank
    exact Nat.sub_add_cancel hle
  have hExp :
      chordRank w k +
          oddSteps w * prefixTwoDepth w k +
          twoSteps w * (oddSteps w - k) =
        twoSteps w * oddSteps w := by
    rw [hrank]
    rw [← Nat.mul_add]
    have hkSum :
        k + (oddSteps w - k) = oddSteps w := by
      omega
    rw [hkSum]
  unfold normalizedCutTerm
  push_cast
  let u : ZMod (terminalGap w) := ↑R.unit
  have huP :
      u ^ oddSteps w = ((2 : ℕ) : ZMod (terminalGap w)) := by
    simpa [u] using R.unit_pow_oddSteps
  have huH :
      u ^ twoSteps w = ((3 : ℕ) : ZMod (terminalGap w)) := by
    simpa [u] using R.unit_pow_twoSteps
  change
    u ^ chordRank w k *
        (((2 : ℕ) : ZMod (terminalGap w)) ^ prefixTwoDepth w k *
          (((3 : ℕ) : ZMod (terminalGap w)) ^ (oddSteps w - k))) =
      (((3 : ℕ) : ZMod (terminalGap w)) ^ oddSteps w)
  calc
    u ^ chordRank w k *
          (((2 : ℕ) : ZMod (terminalGap w)) ^ prefixTwoDepth w k *
            (((3 : ℕ) : ZMod (terminalGap w)) ^ (oddSteps w - k)))
        =
      u ^ chordRank w k *
          ((u ^ oddSteps w) ^ prefixTwoDepth w k *
            (u ^ twoSteps w) ^ (oddSteps w - k)) := by
              rw [huP, huH]
    _ =
      u ^ (chordRank w k +
          oddSteps w * prefixTwoDepth w k +
          twoSteps w * (oddSteps w - k)) := by
            rw [← pow_mul, ← pow_mul]
            rw [← pow_add, ← pow_add]
            rw [Nat.add_assoc]
    _ = u ^ (twoSteps w * oddSteps w) := by
          rw [hExp]
    _ = (u ^ twoSteps w) ^ oddSteps w := by
          rw [pow_mul]
    _ = (((3 : ℕ) : ZMod (terminalGap w)) ^ oddSteps w) := by
          rw [huH]


end RankUnitData
end Word
end Collatz2
