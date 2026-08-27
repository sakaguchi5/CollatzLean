import CollatzLean.Collatz2.RecordFerrers.Perturbation.P23FlexibleAdjacentPairPerturbation

/-!
# Record–Ferrers 摂動理論 24: canonical interior pair の rigid 排除

P22 では outer length `L` に defect split が存在しないことを
`CriticalLowerBestDenominator L` と同値にした。
P23 では defect split が与えられれば actual fixed-chord perturbation と
canonical skeleton change を構成した。

本ファイルでは、その間に残っていた「canonical record anchor では rigid branch が
本当に起こり得るか」を調べる。

critical phase を

  3^n / 2^(criticalHeight n)

で読むと、interior RecordBlock の carry one は endpoint phase を strict に下げる。
したがって cut 1 から record edge を辿って得られる anchor `a` の phase は
cut 1 の phase以下である。

一方 `L ≥ 2` が lower-best なら、その phase は cut 2 の phase以下である。

  phase(a) ≤ phase(1) = 3/2
  phase(L) ≤ phase(2) = 9/8

なので

  phase(a) * phase(L) ≤ 27/16 < 2.

ところが genuine adjacent interior RecordBlocks では outer carry `criticalCarry a L = 1`
であり、これは同じ積が 2 以上であることを強制する。矛盾。

従って canonical に到達可能な anchor 上の adjacent interior pair は lower-best rigid ではなく、
P22 の defect split を必ず持つ。primitive + StripReduced + FirstCrossing を追加すれば、
P23 により actual perturbation と canonical skeleton change まで自動的に得られる。
-/

namespace Collatz2
namespace RecordFerrers

open Word

/--
anchor `a` の critical phase が cut 1 の phase以下であること。

`a = 1` を equality case とし、それ以外は P22 の strict cross-product order を使う。
-/
def CriticalPhaseAtMostOne (a : ℕ) : Prop :=
  a = 1 ∨ CriticalLowerPhaseLess a 1

/-- cut 1 自身は当然 `CriticalPhaseAtMostOne`。 -/
theorem criticalPhaseAtMostOne_one :
    CriticalPhaseAtMostOne 1 :=
  Or.inl rfl

/-- `criticalHeight 1 = 1`。後段の小さい phase 定数を pure integer 化する。 -/
theorem criticalHeight_one_recordFerrers :
    criticalHeight 1 = 1 := by
  norm_num [criticalHeight]
  decide

/-- `criticalHeight 2 = 3`。従って cut 2 の phase は `9/8`。 -/
theorem criticalHeight_two_recordFerrers :
    criticalHeight 2 = 3 := by
  norm_num [criticalHeight]
  decide

/--
critical lower phase の strict order は推移的。

cross-product を二回掛け、middle denominator の positive 2 冪を cancel するだけ。
-/
theorem criticalLowerPhaseLess_trans
    {x y z : ℕ}
    (hXY : CriticalLowerPhaseLess x y)
    (hYZ : CriticalLowerPhaseLess y z) :
    CriticalLowerPhaseLess x z := by
  unfold CriticalLowerPhaseLess at hXY hYZ ⊢
  have hMulXY :
      (3 ^ x * 2 ^ criticalHeight y) *
          2 ^ criticalHeight z <
        (3 ^ y * 2 ^ criticalHeight x) *
          2 ^ criticalHeight z :=
    (Nat.mul_lt_mul_right
      (by positivity : 0 < 2 ^ criticalHeight z)).2 hXY
  have hMulYZ :
      (3 ^ y * 2 ^ criticalHeight z) *
          2 ^ criticalHeight x <
        (3 ^ z * 2 ^ criticalHeight y) *
          2 ^ criticalHeight x :=
    (Nat.mul_lt_mul_right
      (by positivity : 0 < 2 ^ criticalHeight x)).2 hYZ
  have hCombined :
      (3 ^ x * 2 ^ criticalHeight z) *
          2 ^ criticalHeight y <
        (3 ^ z * 2 ^ criticalHeight x) *
          2 ^ criticalHeight y := by
    calc
      (3 ^ x * 2 ^ criticalHeight z) *
          2 ^ criticalHeight y
          =
        (3 ^ x * 2 ^ criticalHeight y) *
          2 ^ criticalHeight z := by ring
      _ <
        (3 ^ y * 2 ^ criticalHeight x) *
          2 ^ criticalHeight z := hMulXY
      _ =
        (3 ^ y * 2 ^ criticalHeight z) *
          2 ^ criticalHeight x := by ring
      _ <
        (3 ^ z * 2 ^ criticalHeight y) *
          2 ^ criticalHeight x := hMulYZ
      _ =
        (3 ^ z * 2 ^ criticalHeight x) *
          2 ^ criticalHeight y := by ring
  exact
    (Nat.mul_lt_mul_right
      (by positivity : 0 < 2 ^ criticalHeight y)).1 hCombined

/--
carry one の record edge は critical phase を strict に下げる。

  carry(a,r)=1
    => phase(a+r) < phase(a).
-/
theorem criticalLowerPhaseLess_add_left_of_carry_one
    {a r : ℕ}
    (hCarry : criticalCarry a r = 1) :
    CriticalLowerPhaseLess (a + r) a := by
  have hAdd := criticalHeight_add_eq a r
  rw [hCarry] at hAdd
  have hUpper :
      3 ^ r < 2 ^ (criticalHeight r + 1) :=
    threePow_lt_twoPow_criticalHeight_succ_strict
  unfold CriticalLowerPhaseLess
  calc
    3 ^ (a + r) * 2 ^ criticalHeight a
        =
      (3 ^ a * 2 ^ criticalHeight a) * 3 ^ r := by
        rw [pow_add]
        ring
    _ <
      (3 ^ a * 2 ^ criticalHeight a) *
        2 ^ (criticalHeight r + 1) := by
          exact
            (Nat.mul_lt_mul_left
              (by positivity :
                0 < 3 ^ a * 2 ^ criticalHeight a)).2 hUpper
    _ =
      3 ^ a *
        (2 ^ criticalHeight a *
          2 ^ (criticalHeight r + 1)) := by ring
    _ =
      3 ^ a *
        2 ^ (criticalHeight a + (criticalHeight r + 1)) := by
          rw [← pow_add]
    _ =
      3 ^ a * 2 ^ criticalHeight (a + r) := by
        have hExp :
            criticalHeight a + (criticalHeight r + 1) =
              criticalHeight (a + r) := by
          omega
        rw [hExp]

namespace CriticalPhaseAtMostOne

/--
cut 1 以下の phase にいる anchor から interior carry-one record edge を進むと、
次の anchor も cut 1 より下に残る。
-/
theorem step_of_carry_one
    {a r : ℕ}
    (hA : CriticalPhaseAtMostOne a)
    (hCarry : criticalCarry a r = 1) :
    CriticalPhaseAtMostOne (a + r) := by
  right
  have hStep : CriticalLowerPhaseLess (a + r) a :=
    criticalLowerPhaseLess_add_left_of_carry_one hCarry
  rcases hA with hEq | hLess
  · subst a
    exact hStep
  · exact criticalLowerPhaseLess_trans hStep hLess

end CriticalPhaseAtMostOne

/--
`CriticalPhaseAtMostOne a` を division のない整数不等式へ展開する。

  phase(a) ≤ 3/2

の cross-multiplied form。
-/
theorem two_mul_threePow_le_three_mul_twoPow_of_phaseAtMostOne
    {a : ℕ}
    (hA : CriticalPhaseAtMostOne a) :
    2 * 3 ^ a ≤ 3 * 2 ^ criticalHeight a := by
  rcases hA with hEq | hLess
  · subst a
    rw [criticalHeight_one_recordFerrers]
    norm_num
  · unfold CriticalLowerPhaseLess at hLess
    rw [criticalHeight_one_recordFerrers] at hLess
    norm_num at hLess
    simpa [Nat.mul_comm] using Nat.le_of_lt hLess

/--
`L ≥ 2` が lower-best denominator なら cut 2 より phase は上に行けない。

  phase(L) ≤ 9/8

の cross-multiplied form。
-/
theorem eight_mul_threePow_le_nine_mul_twoPow_of_lowerBest
    {L : ℕ}
    (hBest : CriticalLowerBestDenominator L)
    (hTwo : 2 ≤ L) :
    8 * 3 ^ L ≤ 9 * 2 ^ criticalHeight L := by
  by_cases hEq : L = 2
  · subst L
    rw [criticalHeight_two_recordFerrers]
    norm_num
  · have hTwoLt : 2 < L := by omega
    have hAll :=
      (criticalLowerBest_iff_all_proper_carry_one hBest.1).1 hBest
    have hCarry :
        criticalCarry 2 (L - 2) = 1 :=
      hAll 2 (by omega) hTwoLt
    have hPhase :
        CriticalLowerPhaseLess (2 + (L - 2)) 2 :=
      criticalLowerPhaseLess_add_left_of_carry_one hCarry
    have hSum : 2 + (L - 2) = L := by omega
    rw [hSum] at hPhase
    unfold CriticalLowerPhaseLess at hPhase
    rw [criticalHeight_two_recordFerrers] at hPhase
    norm_num at hPhase
    simpa [Nat.mul_comm] using Nat.le_of_lt hPhase

/--
anchor が cut 1 以下、outer length が lower-best なら、その phase 積は

  phase(a) * phase(L) ≤ (3/2)*(9/8) = 27/16

を満たす。
-/
theorem sixteen_mul_threePow_add_le_twentySeven_mul_twoPow_add
    {a L : ℕ}
    (hA : CriticalPhaseAtMostOne a)
    (hBest : CriticalLowerBestDenominator L)
    (hTwo : 2 ≤ L) :
    16 * 3 ^ (a + L) ≤
      27 * 2 ^ (criticalHeight a + criticalHeight L) := by
  have hAnchor :=
    two_mul_threePow_le_three_mul_twoPow_of_phaseAtMostOne hA
  have hOuter :=
    eight_mul_threePow_le_nine_mul_twoPow_of_lowerBest hBest hTwo
  have hMul := Nat.mul_le_mul hAnchor hOuter
  calc
    16 * 3 ^ (a + L)
        =
      (2 * 3 ^ a) * (8 * 3 ^ L) := by
        rw [pow_add]
        ring
    _ ≤
      (3 * 2 ^ criticalHeight a) *
        (9 * 2 ^ criticalHeight L) := hMul
    _ =
      27 * 2 ^ (criticalHeight a + criticalHeight L) := by
        rw [pow_add]
        ring

namespace AdjacentInteriorRecordPair

/--
genuine adjacent interior pair では anchor から outer endpoint までの carry も 1。
-/
theorem outerCarry_one
    {P : Word.ContractingExponentPair}
    {u : FiberPoint P.oddCount P.twoDepth}
    {a r s : ℕ}
    (A : AdjacentInteriorRecordPair P u a r s) :
    criticalCarry a (r + s) = 1 := by
  have hLeft : criticalCarry a r = 1 :=
    A.anchorLeftCarry_one
  have hRight : criticalCarry (a + r) s = 1 :=
    A.rightSource.criticalCarry_eq_one_of_interior A.outerInterior
  have hLocal : criticalCarry r s = 1 :=
    A.sourceLocalCarry_one
  have hCoc := criticalCarry_cocycle a r s
  rw [hLeft, hRight, hLocal] at hCoc
  have hOuter := criticalCarry_le_one a (r + s)
  omega

/--
## 主定理 1: canonical interior rigid branch の排除

anchor phase が cut 1 以下にある genuine adjacent interior pair では、
outer length `r+s` は lower-best denominator ではあり得ない。

この定理自体は primitive / StripReduced / whole FirstCrossing を要求しない。
RecordBlock の carry-one 幾何と P22 の lower-best 算術だけで閉じる。
-/
theorem not_criticalLowerBest_of_phaseAtMostOne
    {P : Word.ContractingExponentPair}
    {u : FiberPoint P.oddCount P.twoDepth}
    {a r s : ℕ}
    (A : AdjacentInteriorRecordPair P u a r s)
    (hA : CriticalPhaseAtMostOne a) :
    ¬ CriticalLowerBestDenominator (r + s) := by
  intro hBest
  have hrPos : 0 < r := A.leftSource.length_pos
  have hsPos : 0 < s := A.rightSource.length_pos
  have hTwo : 2 ≤ r + s := by omega
  have hScaled :=
    sixteen_mul_threePow_add_le_twentySeven_mul_twoPow_add
      hA hBest hTwo
  have hYPos :
      0 < 2 ^ (criticalHeight a + criticalHeight (r + s)) := by
    positivity
  have hTwentySeven :
      27 * 2 ^ (criticalHeight a + criticalHeight (r + s)) <
        32 * 2 ^ (criticalHeight a + criticalHeight (r + s)) :=
    (Nat.mul_lt_mul_right hYPos).2 (by norm_num)
  have hSixteen :
      16 * 3 ^ (a + (r + s)) <
        16 *
          (2 * 2 ^ (criticalHeight a + criticalHeight (r + s))) := by
    calc
      16 * 3 ^ (a + (r + s))
          ≤
        27 * 2 ^ (criticalHeight a + criticalHeight (r + s)) :=
          hScaled
      _ <
        32 * 2 ^ (criticalHeight a + criticalHeight (r + s)) :=
          hTwentySeven
      _ =
        16 *
          (2 * 2 ^ (criticalHeight a + criticalHeight (r + s))) := by
            ring
  have hPowerUpper :
      3 ^ (a + (r + s)) <
        2 ^ (criticalHeight a + criticalHeight (r + s) + 1) := by
    have hCancel :
        3 ^ (a + (r + s)) <
          2 * 2 ^ (criticalHeight a + criticalHeight (r + s)) :=
      (Nat.mul_lt_mul_left (by norm_num : 0 < 16)).1 hSixteen
    calc
      3 ^ (a + (r + s))
          <
        2 * 2 ^ (criticalHeight a + criticalHeight (r + s)) :=
          hCancel
      _ =
        2 ^ (criticalHeight a + criticalHeight (r + s) + 1) := by
          rw [pow_succ]
          ring
  have hOuterCarry : criticalCarry a (r + s) = 1 :=
    A.outerCarry_one
  have hAdd := criticalHeight_add_eq a (r + s)
  rw [hOuterCarry] at hAdd
  have hIndexPos : 0 < a + (r + s) := by omega
  have hPowerLower :
      2 ^ (criticalHeight a + criticalHeight (r + s) + 1) <
        3 ^ (a + (r + s)) := by
    have h := criticalHeight_pow_lt_threePow hIndexPos
    rw [hAdd] at h
    exact h
  exact (Nat.lt_asymm hPowerUpper hPowerLower).elim

/-- canonical interior pair には P22 defect split が自動的に存在する。 -/
theorem exists_defectSplit_of_phaseAtMostOne
    {P : Word.ContractingExponentPair}
    {u : FiberPoint P.oddCount P.twoDepth}
    {a r s : ℕ}
    (A : AdjacentInteriorRecordPair P u a r s)
    (hA : CriticalPhaseAtMostOne a) :
    ∃ x : ℕ, DefectSplit (r + s) x := by
  have hLPos : 0 < r + s := by
    have hr := A.leftSource.length_pos
    omega
  exact
    (exists_defectSplit_iff_not_criticalLowerBest hLPos).2
      (A.not_criticalLowerBest_of_phaseAtMostOne hA)

end AdjacentInteriorRecordPair

/--
## 主定理 2: canonical interior pair の automatic actual perturbation

P24 の rigid 排除で defect split を自動生成し、P23 へそのまま渡す。
したがって primitive + StripReduced FirstCrossing fiber では、anchor phase が cut 1 以下の
adjacent interior pair は必ず actual fixed-chord perturbation を持ち、canonical length skeleton が変わる。
-/
theorem exists_automaticInteriorAdjacentPairPerturbation
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (hFu : FirstCrossing u.word)
    {a r s : ℕ}
    (A : AdjacentInteriorRecordPair P u a r s)
    (hA : CriticalPhaseAtMostOne a) :
    ∃ v : FiberPoint P.oddCount P.twoDepth,
      ∃ k : ℕ,
        RealizedAdjacentCutTransfer u v a r s k ∧
        FirstCrossing v.word ∧
        criticalCarry
            (k - a)
            (((a + r) + s) - k) = 0 ∧
        ActualOneBitDefectAtCut v a ((a + r) + s) k ∧
        ∃ Du : RecordDecomposition u a,
          ∃ Dv : RecordDecomposition v a,
            Du.lengths ≠ Dv.lengths := by
  obtain ⟨x, D⟩ := A.exists_defectSplit_of_phaseAtMostOne hA
  exact
    exists_flexibleAdjacentPairPerturbation
      P hPrimitive hReduced u hFu A D

end RecordFerrers
end Collatz2
