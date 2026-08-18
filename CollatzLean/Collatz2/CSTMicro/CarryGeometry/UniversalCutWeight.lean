import CollatzLean.Collatz2.CSTMicro.CarryGeometry.ThreeQSmallStrip
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.ZMod.Basic

/-!
# Universal cut weight

primitive rank-unit を使わず、FirstCrossing word の各 cut に canonical modular weight を置く。

  X_k = normalizedCutTerm(k) * (3^m)^(-1)  (mod G)

ここで

  G = 2^H - 3^m.

FirstCrossing では `G` は 2,3 と互いに素なので `3^m` は常に unit である。
primitive `gcd(H,m)=1` がある場合には既存 `inverseRankWeight` と一致する。
-/

namespace Collatz2
namespace Word

namespace FirstCrossing

/-- FirstCrossing terminal gap は 2 と互いに素。 -/
theorem two_coprime_terminalGap
    {w : Word}
    (hF : FirstCrossing w) :
    Nat.Coprime 2 (terminalGap w) := by
  let H := twoSteps w
  let p := oddSteps w
  let G := terminalGap w
  have hpPos : 0 < p := by
    dsimp [p, oddSteps]
    exact List.length_pos_iff.mpr hF.nonempty
  have hPow : 3 ^ p < 2 ^ H := by
    dsimp [p, H]
    exact
      (contracting_iff_threePow_lt_twoPow).1
        hF.terminalContracting
  have hHPos : 0 < H := by
    by_contra hnot
    have hHzero : H = 0 := by omega
    rw [hHzero] at hPow
    simp at hPow
  have hEvenTwo : Even (2 ^ H) :=
    (show Even (2 : ℕ) by decide).pow_of_ne_zero
      (Nat.ne_of_gt hHPos)
  have hOddThree : Odd (3 ^ p) :=
    (show Odd (3 : ℕ) by decide).pow
  have hOddGap : Odd G := by
    dsimp [G, terminalGap]
    exact Nat.Even.sub_odd (Nat.le_of_lt hPow) hEvenTwo hOddThree
  exact hOddGap.coprime_two_left

/-- FirstCrossing terminal gap は 3 と互いに素。 -/
theorem three_coprime_terminalGap
    {w : Word}
    (hF : FirstCrossing w) :
    Nat.Coprime 3 (terminalGap w) := by
  let H := twoSteps w
  let p := oddSteps w
  let G := terminalGap w
  have hpPos : 0 < p := by
    dsimp [p, oddSteps]
    exact List.length_pos_iff.mpr hF.nonempty
  have hPow : 3 ^ p < 2 ^ H := by
    dsimp [p, H]
    exact
      (contracting_iff_threePow_lt_twoPow).1
        hF.terminalContracting
  have hHPos : 0 < H := by
    by_contra hnot
    have hHzero : H = 0 := by omega
    rw [hHzero] at hPow
    simp at hPow
  have hGapAdd : G + 3 ^ p = 2 ^ H := by
    dsimp [G, terminalGap]
    exact Nat.sub_add_cancel (Nat.le_of_lt hPow)
  apply (show Nat.Prime 3 by decide).coprime_iff_not_dvd.mpr
  intro hThreeDvdGap
  have hThreeDvdPow : 3 ∣ 3 ^ p :=
    dvd_pow_self 3 (Nat.ne_of_gt hpPos)
  have hThreeDvdSum : 3 ∣ G + 3 ^ p :=
    Nat.dvd_add hThreeDvdGap hThreeDvdPow
  have hThreeDvdTwoPow : 3 ∣ 2 ^ H := by
    rw [hGapAdd] at hThreeDvdSum
    exact hThreeDvdSum
  have hThreeDvdTwo : 3 ∣ 2 :=
    (show Nat.Prime 3 by decide).dvd_of_dvd_pow hThreeDvdTwoPow
  norm_num at hThreeDvdTwo

/-- terminal-gap modulus 上の canonical `2` unit。 -/
noncomputable def terminalTwoUnit
    {w : Word}
    (hF : FirstCrossing w) :
    (ZMod (terminalGap w))ˣ :=
  ZMod.unitOfCoprime 2 hF.two_coprime_terminalGap

/-- terminal-gap modulus 上の canonical `3` unit。 -/
noncomputable def terminalThreeUnit
    {w : Word}
    (hF : FirstCrossing w) :
    (ZMod (terminalGap w))ˣ :=
  ZMod.unitOfCoprime 3 hF.three_coprime_terminalGap

@[simp] theorem terminalTwoUnit_coe
    {w : Word}
    (hF : FirstCrossing w) :
    (↑hF.terminalTwoUnit : ZMod (terminalGap w)) = 2 := by
  simp [terminalTwoUnit]

@[simp] theorem terminalThreeUnit_coe
    {w : Word}
    (hF : FirstCrossing w) :
    (↑hF.terminalThreeUnit : ZMod (terminalGap w)) = 3 := by
  simp [terminalThreeUnit]

end FirstCrossing

/--
primitive 条件を使わない cut weight。
`3^m` の unit inverse で normalized cut term を割る。
-/
noncomputable def universalCutWeight
    {w : Word}
    (hF : FirstCrossing w)
    (k : ℕ) : ZMod (terminalGap w) :=
  ((normalizedCutTerm w k : ℕ) : ZMod (terminalGap w)) *
    (↑((hF.terminalThreeUnit ^ oddSteps w)⁻¹) :
      ZMod (terminalGap w))

/-- universal cut weight は `3^m X_k = normalizedCutTerm(k)` を満たす。 -/
theorem FirstCrossing.threePow_mul_universalCutWeight
    {w : Word}
    (hF : FirstCrossing w)
    (k : ℕ) :
    (((3 ^ oddSteps w : ℕ)) : ZMod (terminalGap w)) *
        universalCutWeight hF k =
      ((normalizedCutTerm w k : ℕ) : ZMod (terminalGap w)) := by
  let U : (ZMod (terminalGap w))ˣ :=
    hF.terminalThreeUnit ^ oddSteps w
  have hU :
      (↑U : ZMod (terminalGap w)) =
        (((3 ^ oddSteps w : ℕ)) : ZMod (terminalGap w)) := by
    dsimp [U]
    simp
  unfold universalCutWeight
  rw [← hU]
  have hUdef :
      hF.terminalThreeUnit ^ oddSteps w = U := by
    rfl
  rw [hUdef]
  calc
    (↑U : ZMod (terminalGap w)) *
        ((((normalizedCutTerm w k : ℕ)) : ZMod (terminalGap w)) *
          (↑(U⁻¹) : ZMod (terminalGap w)))
        =
      (((normalizedCutTerm w k : ℕ)) : ZMod (terminalGap w)) *
        ((↑U : ZMod (terminalGap w)) *
          (↑(U⁻¹) : ZMod (terminalGap w))) := by
            ring
    _ = ((normalizedCutTerm w k : ℕ) : ZMod (terminalGap w)) := by
      simp

/-- `3^m` は universal cut weight の比較で cancel できる。 -/
theorem FirstCrossing.cancel_threePow
    {w : Word}
    (hF : FirstCrossing w)
    {x y : ZMod (terminalGap w)}
    (hEq :
      (((3 ^ oddSteps w : ℕ)) : ZMod (terminalGap w)) * x =
        (((3 ^ oddSteps w : ℕ)) : ZMod (terminalGap w)) * y) :
    x = y := by
  let U : (ZMod (terminalGap w))ˣ :=
    hF.terminalThreeUnit ^ oddSteps w
  have hU :
      (↑U : ZMod (terminalGap w)) =
        (((3 ^ oddSteps w : ℕ)) : ZMod (terminalGap w)) := by
    dsimp [U]
    simp
  have hEq' :
      (↑U : ZMod (terminalGap w)) * x =
        (↑U : ZMod (terminalGap w)) * y := by
    simpa [hU] using hEq
  have h := congrArg
    (fun z : ZMod (terminalGap w) =>
      (↑(U⁻¹) : ZMod (terminalGap w)) * z) hEq'
  simpa [← mul_assoc] using h

/-- terminal gap が nontrivial なら universal cut weight は zero ではない。 -/
theorem FirstCrossing.universalCutWeight_ne_zero
    {w : Word}
    (hF : FirstCrossing w)
    (hGap : 1 < terminalGap w)
    (k : ℕ) :
    universalCutWeight hF k ≠ 0 := by
  let G := terminalGap w
  let U2 : (ZMod G)ˣ := hF.terminalTwoUnit
  let U3 : (ZMod G)ˣ := hF.terminalThreeUnit
  haveI : Nontrivial (ZMod G) :=
    (ZMod.nontrivial_iff.mpr (by omega : G ≠ 1))
  have hTerm :
      ((normalizedCutTerm w k : ℕ) : ZMod G) =
        (↑(U2 ^ prefixTwoDepth w k *
            U3 ^ (oddSteps w - k)) : ZMod G) := by
    dsimp [U2, U3, G]
    unfold normalizedCutTerm
    push_cast
    simp [FirstCrossing.terminalTwoUnit,
      FirstCrossing.terminalThreeUnit]
  have hTermNe :
      ((normalizedCutTerm w k : ℕ) : ZMod G) ≠ 0 := by
    rw [hTerm]
    exact Units.ne_zero _
  intro hZero
  have hThree := hF.threePow_mul_universalCutWeight k
  change
    (((3 ^ oddSteps w : ℕ)) : ZMod G) *
        universalCutWeight hF k =
      ((normalizedCutTerm w k : ℕ) : ZMod G) at hThree
  rw [hZero] at hThree
  simp at hThree
  exact hTermNe hThree.symm

/-- universal cut weights の全 proper-cut sum。 -/
noncomputable def universalCutWeightSum
    {w : Word}
    (hF : FirstCrossing w) : ZMod (terminalGap w) :=
  Finset.sum (Finset.range (oddSteps w))
    (fun k => universalCutWeight hF k)

/--
全 cut の universal weight を `3^m` 倍すると exact に `3*affineConst`。
-/
theorem FirstCrossing.threePow_mul_universalCutWeightSum
    {w : Word}
    (hF : FirstCrossing w) :
    (((3 ^ oddSteps w : ℕ)) : ZMod (terminalGap w)) *
        universalCutWeightSum hF =
      (((3 * affineConst w : ℕ)) : ZMod (terminalGap w)) := by
  unfold universalCutWeightSum
  rw [Finset.mul_sum]
  calc
    Finset.sum (Finset.range (oddSteps w))
        (fun k =>
          (((3 ^ oddSteps w : ℕ)) : ZMod (terminalGap w)) *
            universalCutWeight hF k)
        =
      Finset.sum (Finset.range (oddSteps w))
        (fun k =>
          ((normalizedCutTerm w k : ℕ) : ZMod (terminalGap w))) := by
            apply Finset.sum_congr rfl
            intro k hk
            exact hF.threePow_mul_universalCutWeight k
    _ =
      ((Finset.sum (Finset.range (oddSteps w))
        (fun k => normalizedCutTerm w k) : ℕ) :
          ZMod (terminalGap w)) := by
            push_cast
            rfl
    _ = (((3 * affineConst w : ℕ)) : ZMod (terminalGap w)) := by
      rw [sum_normalizedCutTerm_eq_three_mul_affineConst]

/--
primitive rank-unit がある場合、universal weight は既存 inverse rank weight と一致する。
-/
theorem RankUnitData.universalCutWeight_eq_inverseRankWeight
    {w : Word}
    (R : RankUnitData w)
    (hF : FirstCrossing w)
    {k : ℕ}
    (hkLt : k < oddSteps w) :
    universalCutWeight hF k = inverseRankWeight R k := by
  apply hF.cancel_threePow
  calc
    (((3 ^ oddSteps w : ℕ)) : ZMod (terminalGap w)) *
          universalCutWeight hF k
        =
      ((normalizedCutTerm w k : ℕ) : ZMod (terminalGap w)) :=
        hF.threePow_mul_universalCutWeight k
    _ =
      (((3 ^ oddSteps w : ℕ)) : ZMod (terminalGap w)) *
        inverseRankWeight R k :=
          R.normalizedCutTerm_eq_threePow_mul_inverseRankWeight hF hkLt

end Word

namespace CSTMicro
namespace FirstFailureEdge

/--
actual first-failure upper では primitive 条件なしで

  sum X_k = 3 q  (mod G)

が成り立つ。
-/
theorem universalCutWeightSum_eq_three_mul_upperNormalizedDefectNat
    (F : FirstFailureEdge) :
    Collatz2.Word.universalCutWeightSum F.upperExponentWord_firstCrossing =
      (3 : ZMod (Collatz2.Word.terminalGap F.upperExponentWord)) *
        ((F.upperNormalizedDefectNat : ℕ) :
          ZMod (Collatz2.Word.terminalGap F.upperExponentWord)) := by
  let w := F.upperExponentWord
  let hF : Collatz2.Word.FirstCrossing w := F.upperExponentWord_firstCrossing
  have hSum := hF.threePow_mul_universalCutWeightSum
  have hB := F.upperExponentWord_affineConst_cast_eq_threePow_mul_upperQ
  have hScaled :
      (((3 ^ Collatz2.Word.oddSteps w : ℕ)) :
          ZMod (Collatz2.Word.terminalGap w)) *
        Collatz2.Word.universalCutWeightSum hF =
      (((3 ^ Collatz2.Word.oddSteps w : ℕ)) :
          ZMod (Collatz2.Word.terminalGap w)) *
        ((3 : ZMod (Collatz2.Word.terminalGap w)) *
          ((F.upperNormalizedDefectNat : ℕ) :
            ZMod (Collatz2.Word.terminalGap w))) := by
    calc
      (((3 ^ Collatz2.Word.oddSteps w : ℕ)) :
            ZMod (Collatz2.Word.terminalGap w)) *
          Collatz2.Word.universalCutWeightSum hF
          =
        (((3 * Collatz2.Word.affineConst w : ℕ)) :
          ZMod (Collatz2.Word.terminalGap w)) := by
            simpa [w, hF] using hSum
      _ =
        (3 : ZMod (Collatz2.Word.terminalGap w)) *
          ((Collatz2.Word.affineConst w : ℕ) :
            ZMod (Collatz2.Word.terminalGap w)) := by
              push_cast
              ring
      _ =
        (3 : ZMod (Collatz2.Word.terminalGap w)) *
          ((((3 ^ Collatz2.Word.oddSteps w : ℕ)) :
              ZMod (Collatz2.Word.terminalGap w)) *
            ((F.upperNormalizedDefectNat : ℕ) :
              ZMod (Collatz2.Word.terminalGap w))) := by
                rw [hB]
      _ =
        (((3 ^ Collatz2.Word.oddSteps w : ℕ)) :
            ZMod (Collatz2.Word.terminalGap w)) *
          ((3 : ZMod (Collatz2.Word.terminalGap w)) *
            ((F.upperNormalizedDefectNat : ℕ) :
              ZMod (Collatz2.Word.terminalGap w))) := by ring
  have hCancel := hF.cancel_threePow hScaled
  simpa [w, hF] using hCancel

end FirstFailureEdge
end CSTMicro
end Collatz2
