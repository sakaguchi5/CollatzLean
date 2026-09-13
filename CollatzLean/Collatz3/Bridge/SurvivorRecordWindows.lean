import CollatzLean.Collatz3.Bridge.SurvivorCriticalCompletion
import CollatzLean.Collatz3.Bridge.Experimental2BeattyLog
import CollatzLean.Collatz3.Ferrers.RecordFerrers

import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.Finset.Interval
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Collatz3 Bridge: survivor completion の RecordFerrers windows

finite survivor prefix を critical terminal まで completion すると admissible profile が得られる。
幅 `m` が primitive best-upper なら、既存の `RecordFerrers.ofPrimitiveBestUpper` により
この profile は自動的に真の `RecordFerrers` になる。

後半では

`H_m = criticalTwoDepth m`

の upper slope `H_m / m` を考える。これは常に `log₂ 3` より strict に上にあり、
任意の正幅の後にはさらに小さい upper slope が存在する。従って strict record-low 幅は
無限に現れる。strict best-upper 幅が非primitiveなら gcd で縮約した小幅が同じか
より小さい slope を持つため矛盾し、strict record-low はすべて primitive になる。
-/

namespace Collatz3
namespace Bridge

/-- survivor completion profile を admissible profile として束ねる。 -/
def survivorCriticalCompletionAdmissibleProfile
    {n : ℕ}
    (hn : 0 < n)
    (S : SurvivorParityCode n) :
    Critical.AdmissibleProfile S.1.length := by
  let P := survivorCriticalCompletionPartition hn S
  exact ⟨RestrictedCriticalPartition.profile P,
    RestrictedCriticalPartition.admissible_profile P⟩

/--
primitive best-upper width の survivor completion は RecordFerrers window を与える。
-/
def survivorRecordWindow
    {n : ℕ}
    (hn : 0 < n)
    (S : SurvivorParityCode n)
    (hm : 2 < S.1.length)
    (P : Critical.IsPrimitiveWidth S.1.length)
    (B : Critical.IsBestUpperWidth S.1.length) :
    Ferrers.RecordFerrers S.1.length :=
  Ferrers.RecordFerrers.ofPrimitiveBestUpper
    (survivorCriticalCompletionAdmissibleProfile hn S) hm P B

/-! ## strict best-upper widths -/

/-- それ以前の全 positive width より slope が strict に小さい幅。 -/
def IsStrictBestUpperWidth (m : ℕ) : Prop :=
  ∀ r : ℕ,
    0 < r →
    r < m →
    Critical.criticalTwoDepth m * r <
      m * Critical.criticalTwoDepth r

namespace IsStrictBestUpperWidth

/-- strict best-upper は通常の best-upper。 -/
theorem bestUpper
    {m : ℕ}
    (S : IsStrictBestUpperWidth m) :
    Critical.IsBestUpperWidth m := by
  intro r hr hrm
  exact Nat.le_of_lt (S r hr hrm)

end IsStrictBestUpperWidth

/-- 実数で読む critical upper slope。 -/
noncomputable def criticalUpperSlope (m : ℕ) : ℝ :=
  (Critical.criticalTwoDepth m : ℝ) / (m : ℝ)

/-- positive width の upper slope は `log₂3` より strict に上。 -/
theorem logb_two_three_lt_criticalUpperSlope
    {m : ℕ}
    (hm : 0 < m) :
    Real.logb 2 3 < criticalUpperSlope m := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hCell := beattyIndex_isLowerMechanical_logb_two_three m
  unfold criticalUpperSlope Critical.criticalTwoDepth
  apply (lt_div_iff₀ hmR).2
  push_cast
  nlinarith [hCell.2]

/-- upper slope は `log₂3 + 1/m` 以下。 -/
theorem criticalUpperSlope_le_logb_two_three_add_inv
    {m : ℕ}
    (hm : 0 < m) :
    criticalUpperSlope m ≤
      Real.logb 2 3 + 1 / (m : ℝ) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hCell := beattyIndex_isLowerMechanical_logb_two_three m
  unfold criticalUpperSlope Critical.criticalTwoDepth
  apply (div_le_iff₀ hmR).2
  push_cast
  have hm0 : (m : ℝ) ≠ 0 := ne_of_gt hmR
  have hInv : (1 / (m : ℝ)) * (m : ℝ) = 1 := by
    field_simp [hm0]
  rw [add_mul, hInv]
  nlinarith [hCell.1]

/-- 任意の positive width より後に、さらに小さい upper slope が現れる。 -/
theorem exists_later_criticalUpperSlope_lt
    {m : ℕ}
    (hm : 0 < m) :
    ∃ n : ℕ, m < n ∧ criticalUpperSlope n < criticalUpperSlope m := by
  let ε : ℝ := criticalUpperSlope m - Real.logb 2 3
  have hε : 0 < ε := by
    dsimp [ε]
    exact sub_pos.mpr (logb_two_three_lt_criticalUpperSlope hm)
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  let n := max (m + 1) (k + 1)
  have hmn : m < n := by
    dsimp [n]
    have h := le_max_left (m + 1) (k + 1)
    omega
  have hn : 0 < n := lt_trans hm hmn
  have hkN : k + 1 ≤ n := by
    dsimp [n]
    exact le_max_right _ _
  have hkR : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  have hknR : ((k + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hkN
  have hInv :
      1 / (n : ℝ) ≤ 1 / ((k + 1 : ℕ) : ℝ) :=
    one_div_le_one_div_of_le hkR hknR
  have hUpper := criticalUpperSlope_le_logb_two_three_add_inv hn
  have hk' : 1 / ((k + 1 : ℕ) : ℝ) < ε := by
    simpa [Nat.cast_add, Nat.cast_one] using hk
  have hSmall : 1 / (n : ℝ) < ε := lt_of_le_of_lt hInv hk'
  dsimp [ε] at hSmall
  exact ⟨n, hmn, by linarith⟩

/--
線形順序値の列で「任意の正 index の後にさらに小さい値がある」なら、
strict record-low index は任意の bound より先に存在する。
-/
theorem exists_strict_record_beyond_of_later_lower
    (f : ℕ → ℝ)
    (hLater : ∀ m : ℕ, 0 < m → ∃ n : ℕ, m < n ∧ f n < f m)
    (L : ℕ) :
    ∃ m : ℕ,
      L < m ∧ 0 < m ∧
        ∀ r : ℕ, 0 < r → r < m → f m < f r := by
  classical
  let s : Finset ℕ := Finset.Icc 1 (L + 1)
  have hs : s.Nonempty := by
    refine ⟨1, ?_⟩
    simp [s]
  obtain ⟨r0, hr0s, hr0min⟩ := s.exists_min_image f hs
  have hr0pos : 0 < r0 := by
    have := (Finset.mem_Icc.mp hr0s).1
    omega
  obtain ⟨n, hr0n, hnLower⟩ := hLater r0 hr0pos
  have hLn : L + 1 < n := by
    by_contra h
    have hnLe : n ≤ L + 1 := by omega
    have hnMem : n ∈ s := by
      apply Finset.mem_Icc.mpr
      constructor <;> omega
    have := hr0min n hnMem
    linarith
  let t : Finset ℕ := Finset.Icc 1 n
  have ht : t.Nonempty := by
    refine ⟨1, ?_⟩
    simp [t]
    omega
  obtain ⟨j, hjs, hjmin⟩ := t.exists_min_image f ht
  have hPexists :
      ∃ k : ℕ,
        0 < k ∧ k ≤ n ∧
          ∀ r : ℕ, 0 < r → r ≤ n → f k ≤ f r := by
    refine ⟨j, ?_, ?_, ?_⟩
    · have := (Finset.mem_Icc.mp hjs).1
      omega
    · exact (Finset.mem_Icc.mp hjs).2
    · intro r hr hrn
      exact hjmin r (Finset.mem_Icc.mpr ⟨by omega, hrn⟩)
  let m : ℕ := Nat.find hPexists
  have hmSpec :
      0 < m ∧ m ≤ n ∧
        ∀ r : ℕ, 0 < r → r ≤ n → f m ≤ f r := by
    simpa [m] using (Nat.find_spec hPexists)
  have hmpos : 0 < m := hmSpec.1
  have hmle : m ≤ n := hmSpec.2.1
  have hmMin : ∀ r : ℕ, 0 < r → r ≤ n → f m ≤ f r := hmSpec.2.2
  have hmBeyond : L < m := by
    by_contra h
    have hmLeL : m ≤ L := by omega
    have hmMem : m ∈ s := by
      apply Finset.mem_Icc.mpr
      constructor <;> omega
    have hR0Le := hr0min m hmMem
    have hMLeN := hmMin n (by omega) (le_rfl)
    linarith
  refine ⟨m, hmBeyond, hmpos, ?_⟩
  intro r hr hrm
  have hrn : r ≤ n := le_trans (Nat.le_of_lt hrm) hmle
  have hle : f m ≤ f r := hmMin r hr hrn
  exact lt_of_le_of_ne hle (by
    intro hEq
    have hPr :
        0 < r ∧ r ≤ n ∧
          ∀ q : ℕ, 0 < q → q ≤ n → f r ≤ f q := by
      refine ⟨hr, hrn, ?_⟩
      intro q hq hqn
      have hmq := hmMin q hq hqn
      rw [← hEq]
      exact hmq
    have hFind : m ≤ r := by
      simpa [m] using (Nat.find_min' hPexists hPr)
    omega)

/-- strict real slope record-low と cross-multiplied strict best-upper は同じ向き。 -/
theorem strictBestUpperWidth_of_realSlope
    {m : ℕ}
    (hm : 0 < m)
    (S : ∀ r : ℕ, 0 < r → r < m →
      criticalUpperSlope m < criticalUpperSlope r) :
    IsStrictBestUpperWidth m := by
  intro r hr hrm
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have h := S r hr hrm
  unfold criticalUpperSlope at h
  have hCross :
      (Critical.criticalTwoDepth m : ℝ) * (r : ℝ) <
        (Critical.criticalTwoDepth r : ℝ) * (m : ℝ) :=
    (div_lt_div_iff₀ hmR hrR).1 h
  have hCrossNat :
      Critical.criticalTwoDepth m * r <
        Critical.criticalTwoDepth r * m := by
    exact_mod_cast hCross
  simpa [Nat.mul_comm] using hCrossNat

/-- strict best-upper width は primitive。 -/
theorem IsStrictBestUpperWidth.primitive
    {m : ℕ}
    (hm : 0 < m)
    (S : IsStrictBestUpperWidth m) :
    Critical.IsPrimitiveWidth m := by
  by_contra hNot
  have hContentNe : Critical.widthContent m ≠ 1 := by
    intro hOne
    apply hNot
    change Nat.Coprime (Critical.criticalTwoDepth m) m
    change Nat.gcd (Critical.criticalTwoDepth m) m = 1
    rw [Nat.gcd_comm]
    exact hOne
  let g := Critical.widthContent m
  let p := Critical.primitiveWidth m
  let q := Critical.criticalTwoDepth m / g
  have hgPos : 0 < g := by simpa [g] using Critical.widthContent_pos m
  have hgGt : 1 < g := by
    have : g ≠ 1 := by simpa [g] using hContentNe
    omega
  have hgp : g * p = m := by
    simpa [g, p] using Critical.widthContent_mul_primitiveWidth m
  have hgDvdH : g ∣ Critical.criticalTwoDepth m := by
    dsimp [g, Critical.widthContent]
    exact Nat.gcd_dvd_right m (Critical.criticalTwoDepth m)
  have hgq : g * q = Critical.criticalTwoDepth m := by
    dsimp [q]
    exact Nat.mul_div_cancel' hgDvdH
  have hpPos : 0 < p := by
    by_contra hp
    have hp0 : p = 0 := by omega
    rw [hp0, Nat.mul_zero] at hgp
    omega
  have hpLt : p < m := by
    nlinarith
  have hCellM := beattyIndex_isLowerMechanical_logb_two_three m
  have hCellP := beattyIndex_isLowerMechanical_logb_two_three p
  have hPq :
      (p : ℝ) * Real.logb 2 3 < (q : ℝ) := by
    have hgR : (0 : ℝ) < (g : ℝ) := by exact_mod_cast hgPos
    have hgpR : (g : ℝ) * (p : ℝ) = (m : ℝ) := by exact_mod_cast hgp
    have hgqR : (g : ℝ) * (q : ℝ) =
        (Critical.criticalTwoDepth m : ℝ) := by exact_mod_cast hgq
    have hTop :
        (m : ℝ) * Real.logb 2 3 <
          (Critical.criticalTwoDepth m : ℝ) := by
      unfold Critical.criticalTwoDepth
      push_cast
      linarith [hCellM.2]
    have hScaled :
        (g : ℝ) * ((p : ℝ) * Real.logb 2 3) <
          (g : ℝ) * (q : ℝ) := by
      calc
        (g : ℝ) * ((p : ℝ) * Real.logb 2 3) =
            (m : ℝ) * Real.logb 2 3 := by
              rw [← hgpR]
              ring
        _ < (Critical.criticalTwoDepth m : ℝ) := hTop
        _ = (g : ℝ) * (q : ℝ) := hgqR.symm
    have hTarget :
        (p : ℝ) * Real.logb 2 3 < (q : ℝ) := by
      nlinarith [hScaled, hgR]
    exact hTarget
  have hBeatLtQ : Critical.beattyIndex p < q := by
    have hBeatR :
        (Critical.beattyIndex p : ℝ) < (q : ℝ) :=
      lt_of_le_of_lt hCellP.1 hPq
    exact_mod_cast hBeatR
  have hHpLeQ : Critical.criticalTwoDepth p ≤ q := by
    unfold Critical.criticalTwoDepth
    omega
  have hStrict := S p hpPos hpLt
  have hEqCross :
      Critical.criticalTwoDepth m * p = m * q := by
    calc
      Critical.criticalTwoDepth m * p = (g * q) * p := by rw [hgq]
      _ = (g * p) * q := by ring
      _ = m * q := by rw [hgp]
  have hUpper :
      m * Critical.criticalTwoDepth p ≤ m * q :=
    Nat.mul_le_mul_left m hHpLeQ
  rw [hEqCross] at hStrict
  omega

/-- primitive best-upper widths は任意の bound より先に存在する。 -/
theorem exists_primitive_bestUpperWidth_gt
    (L : ℕ) :
    ∃ m : ℕ,
      L < m ∧
      Critical.IsPrimitiveWidth m ∧
      Critical.IsBestUpperWidth m := by
  obtain ⟨m, hLm, hm, hRecord⟩ :=
    exists_strict_record_beyond_of_later_lower
      criticalUpperSlope
      (fun r hr => exists_later_criticalUpperSlope_lt hr)
      L
  have hStrict : IsStrictBestUpperWidth m :=
    strictBestUpperWidth_of_realSlope hm hRecord
  exact ⟨m, hLm, hStrict.primitive hm, hStrict.bestUpper⟩

end Bridge
end Collatz3
