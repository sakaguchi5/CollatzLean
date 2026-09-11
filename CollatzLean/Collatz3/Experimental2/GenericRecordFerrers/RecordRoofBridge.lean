import CollatzLean.Collatz3.Experimental2.GenericRecordFerrers.RecordPartition
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Collatz3 Experimental2: canonical record cut は roof cut

`GenericRecordFerrers.ChordRank` と `RecordPartition` で定義した一般の弦順位について、
0/1-carry 屋根と admissible roof path を仮定すると、標準 anchor `1` より後の
strict record cut が実際の roof cut になることを示す。

このファイルで初めて

* `HasUnitCarry β`,
* `IsAdmissibleRoofPath β m height`,
* `β 1 = 1`

を record partition に接続する。

証明の核心は次の二つの順位評価である。

1. proper cut `k` が roof 上でなければ
   `m < chordRank β m height k`。
2. `β 1 = 1` かつ admissible なら標準 anchor `1` では
   `chordRank β m height 1 ≤ m`。

したがって anchor より strict に低い record cut は非-roof ではあり得ない。

この段階でも `Critical.beattyIndex`、`Critical.Profile`、`Ferrers.RecordFerrers`、
実際の Collatz 軌道には依存しない。
-/

namespace Collatz3
namespace Experimental2
namespace GenericRecordFerrers

/--
`HasUnitCarry` と roof bound の下では、原点の高さは `0` に固定される。
-/
theorem height_zero_eq_zero
    {β : ℕ → ℕ}
    {m : ℕ}
    {height : ℕ → ℕ}
    (U : HasUnitCarry β)
    (A : IsAdmissibleRoofPath β m height)
    (hm : 0 < m) :
    height 0 = 0 := by
  have hLe : height 0 ≤ β 0 := A.1 0 hm
  have hβ0 : β 0 = 0 := U.zero_eq
  omega

/--
`β 1 = 1` なら、幅 `m > 1` の admissible path は標準 anchor `1` で
高さも正確に `1` になる。
-/
theorem height_one_eq_one
    {β : ℕ → ℕ}
    {m : ℕ}
    {height : ℕ → ℕ}
    (U : HasUnitCarry β)
    (A : IsAdmissibleRoofPath β m height)
    (hβ1 : β 1 = 1)
    (hm : 1 < m) :
    height 1 = 1 := by
  have h0 : height 0 = 0 :=
    height_zero_eq_zero U A (by omega)
  have hStrict0 : height 0 < height 1 := by
    simpa using A.2.1 0 (by omega : 0 < m)
  have hUpper1 : height 1 ≤ 1 := by
    have h := A.1 1 hm
    simpa [hβ1] using h
  omega

/--
標準 anchor `1` は、`β 1 = 1` の下で admissible path の proper roof cut になる。
-/
theorem canonicalAnchor_isProperRoofCut
    {β : ℕ → ℕ}
    {m : ℕ}
    {height : ℕ → ℕ}
    (U : HasUnitCarry β)
    (A : IsAdmissibleRoofPath β m height)
    (hβ1 : β 1 = 1)
    (hm : 1 < m) :
    IsProperRoofCut β m height canonicalAnchor := by
  refine ⟨?_, ?_, ?_⟩
  · simp [canonicalAnchor]
  · simpa [canonicalAnchor] using hm
  · unfold IsOnRoof
    have hHeight : height 1 = 1 := height_one_eq_one U A hβ1 hm
    simpa [canonicalAnchor, hβ1] using hHeight

/--
`β 1 = 1` のとき、幅 `m > 1` では終端臨界深さは `2m` 以下。

これは unit-carry の反復上界を `r = 1` に適用しただけの一般算術である。
-/
theorem criticalDepth_le_two_mul
    {β : ℕ → ℕ}
    {m : ℕ}
    (U : HasUnitCarry β)
    (hβ1 : β 1 = 1)
    (hm : 1 < m) :
    criticalDepth β m ≤ 2 * m := by
  have hUpper := U.mul_upper_succ (m - 1) 1
  have hmOne : 1 ≤ m := by omega
  have hPred : m - 1 + 1 = m := Nat.sub_add_cancel hmOne
  rw [hPred] at hUpper
  simp [hβ1] at hUpper
  unfold criticalDepth
  omega

/--
標準 anchor `1` の弦順位は幅 `m` 以下。

後段の record-cut 排除で必要なのは exact 値ではなく、この上界だけである。
-/
theorem canonicalAnchor_chordRank_le_width
    {β : ℕ → ℕ}
    {m : ℕ}
    {height : ℕ → ℕ}
    (U : HasUnitCarry β)
    (A : IsAdmissibleRoofPath β m height)
    (hβ1 : β 1 = 1)
    (hm : 1 < m) :
    chordRank β m height canonicalAnchor ≤ (m : ℤ) := by
  have hHeight : height 1 = 1 := height_one_eq_one U A hβ1 hm
  have hDepth : criticalDepth β m ≤ 2 * m :=
    criticalDepth_le_two_mul U hβ1 hm
  have hDepthZ :
      (criticalDepth β m : ℤ) ≤ 2 * (m : ℤ) := by
    exact_mod_cast hDepth
  have hAnchorLt : canonicalAnchor < m := by
    simpa [canonicalAnchor] using hm
  rw [chordRank_of_lt (β := β) (height := height) hAnchorLt]
  simp only [canonicalAnchor, Nat.cast_one, mul_one]
  rw [hHeight]
  simp only [Nat.cast_one, mul_one]
  linarith

/--
proper positive cut が roof 上にいなければ、その弦順位は幅 `m` より strict に大きい。

証明は一般の strict critical chord

`m * β k < criticalDepth β m * k`

と `height k < β k` を組み合わせるだけである。
-/
theorem width_lt_chordRank_of_not_roof
    {β : ℕ → ℕ}
    {m : ℕ}
    {height : ℕ → ℕ}
    (U : HasUnitCarry β)
    (A : IsAdmissibleRoofPath β m height)
    {k : ℕ}
    (hkPos : 0 < k)
    (hkLt : k < m)
    (hNotRoof : ¬ IsOnRoof β height k) :
    (m : ℤ) < chordRank β m height k := by
  have hLe : height k ≤ β k := A.1 k hkLt
  have hNe : height k ≠ β k := by
    intro hEq
    exact hNotRoof hEq
  have hLt : height k < β k := lt_of_le_of_ne hLe hNe
  have hChord :
      m * β k < criticalDepth β m * k :=
    U.below_criticalChord hkPos
  have hScaled :
      m * height k + m < criticalDepth β m * k := by
    calc
      m * height k + m = m * (height k + 1) := by ring
      _ ≤ m * β k :=
        Nat.mul_le_mul_left m (Nat.succ_le_of_lt hLt)
      _ < criticalDepth β m * k := hChord
  have hScaledZ :
      (m : ℤ) * (height k : ℤ) + (m : ℤ) <
        (criticalDepth β m : ℤ) * (k : ℤ) := by
    exact_mod_cast hScaled
  rw [chordRank_of_lt (β := β) (height := height) hkLt]
  linarith

/--
任意 anchor について、その anchor の弦順位が幅以下なら、
そこから見た strict record cut は必ず proper roof cut になる。

標準 anchor `1` に特殊化する前の一般形。
-/
theorem isProperRoofCut_of_isRecordCutAfter_of_anchorRank_le_width
    {β : ℕ → ℕ}
    {m : ℕ}
    {height : ℕ → ℕ}
    (U : HasUnitCarry β)
    (A : IsAdmissibleRoofPath β m height)
    {anchor k : ℕ}
    (hAnchorRank : chordRank β m height anchor ≤ (m : ℤ))
    (R : IsRecordCutAfter β m height anchor k) :
    IsProperRoofCut β m height k := by
  have hR :=
    (isRecordCutAfter_iff
      (β := β) (m := m) (height := height)
      (anchor := anchor) (k := k)).1 R
  have hkPos : 0 < k := by
    omega
  refine ⟨hkPos, hR.2.1, ?_⟩
  by_contra hNotRoof
  have hAbove :
      (m : ℤ) < chordRank β m height k :=
    width_lt_chordRank_of_not_roof U A hkPos hR.2.1 hNotRoof
  have hDrop :
      chordRank β m height k < chordRank β m height anchor :=
    hR.2.2 anchor (Nat.le_refl anchor) hR.1
  linarith

/--
標準 anchor `1` より後の strict record cut は、`β 1 = 1` の下で必ず proper roof cut。

これが一般 RecordFerrers 実験の第3段階の中心定理。
-/
theorem canonicalRecordCut_isProperRoofCut
    {β : ℕ → ℕ}
    {m : ℕ}
    {height : ℕ → ℕ}
    (U : HasUnitCarry β)
    (A : IsAdmissibleRoofPath β m height)
    (hβ1 : β 1 = 1)
    (hm : 1 < m)
    {k : ℕ}
    (R : IsRecordCutAfter β m height canonicalAnchor k) :
    IsProperRoofCut β m height k := by
  exact
    isProperRoofCut_of_isRecordCutAfter_of_anchorRank_le_width
      U A
      (canonicalAnchor_chordRank_le_width U A hβ1 hm)
      R

/--
`canonicalRecordCuts` に実際に含まれる全 cut は proper roof cut。

有限計算で抽出した canonical partition を、屋根への genuine return 列として読める。
-/
theorem isProperRoofCut_of_mem_canonicalRecordCuts
    {β : ℕ → ℕ}
    {m : ℕ}
    {height : ℕ → ℕ}
    (U : HasUnitCarry β)
    (A : IsAdmissibleRoofPath β m height)
    (hβ1 : β 1 = 1)
    (hm : 1 < m)
    {k : ℕ}
    (hk : k ∈ canonicalRecordCuts β m height) :
    IsProperRoofCut β m height k := by
  unfold canonicalRecordCuts at hk
  have hSpec :=
    (mem_recordCutsAfter_iff
      (β := β) (m := m) (height := height)
      (anchor := canonicalAnchor) (k := k)).1 hk
  exact canonicalRecordCut_isProperRoofCut U A hβ1 hm hSpec.2

end GenericRecordFerrers
end Experimental2
end Collatz3
