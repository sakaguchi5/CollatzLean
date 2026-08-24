import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.BeattyFactorRepeat
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Critical Beatty の cyclic carry arithmetic

zero scaled-state branch では、長さ `p` の Beatty rise が連続する `p` 個の start で
同じ値 `p + Delta` を持つ。このとき offset `0,...,p-1` に対する加法 carry の個数は
一つ start を進めるごとに modulo `p` で `Delta` だけ進む。

このファイルでは、その有限算術だけを切り出す。

* cyclic carry set / rank
* rank の exact telescoping formula
* `p.Coprime Delta` のとき p 個の rotation rank が `Fin p` を全て走る
* Beatty cycle numerator を base part + carry part に分解

Collatz / Pure B / restarted geometry はここには入らない。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

open scoped BigOperators

/-- period `p` の cycle numerator で使う offsets `0,...,p-1` の carry set。 -/
def beattyCyclicCarrySet (s p : ℕ) : Finset ℕ :=
  (Finset.range p).filter (fun u => BeattyCarryOne s u)

/-- cyclic carry set の cardinality。 -/
def beattyCyclicCarryRank (s p : ℕ) : ℕ :=
  (beattyCyclicCarrySet s p).card

/-- offset `0` では carry は起こらない。 -/
theorem not_beattyCarryOne_zero (s : ℕ) :
    ¬ BeattyCarryOne s 0 := by
  simp [BeattyCarryOne]

/-- `p>0` なら cyclic rank は strict に `p` 未満。 -/
theorem beattyCyclicCarryRank_lt
    (s p : ℕ)
    (hp : 0 < p) :
    beattyCyclicCarryRank s p < p := by
  unfold beattyCyclicCarryRank beattyCyclicCarrySet
  have hsub :
      (Finset.range p).filter (fun u => BeattyCarryOne s u) ⊆
        Finset.range p :=
    Finset.filter_subset _ _
  have hne :
      (Finset.range p).filter (fun u => BeattyCarryOne s u) ≠
        Finset.range p := by
    intro hEq
    have hZeroMem : 0 ∈ Finset.range p := by simp [hp]
    have hZeroFilter :
        0 ∈ (Finset.range p).filter (fun u => BeattyCarryOne s u) := by
      rw [hEq]
      exact hZeroMem
    simp [not_beattyCarryOne_zero] at hZeroFilter
  have hss :
      (Finset.range p).filter (fun u => BeattyCarryOne s u) ⊂
        Finset.range p :=
    (Finset.ssubset_iff_subset_ne).2 ⟨hsub, hne⟩
  have hCard := Finset.card_lt_card hss
  simpa using hCard

/-- Beatty addition の carry を整数 `0/1` として書いたもの。 -/
def beattyCarryValue (s r : ℕ) : ℤ :=
  (beattyIndex (s + r) : ℤ) -
    (beattyIndex s : ℤ) -
    (beattyIndex r : ℤ)

/-- carry value は proposition indicator と exact に一致する。 -/
theorem beattyCarryValue_eq_indicator
    (s r : ℕ) :
    beattyCarryValue s r =
      if BeattyCarryOne s r then 1 else 0 := by
  by_cases hCarry : BeattyCarryOne s r
  · rw [if_pos hCarry]
    unfold beattyCarryValue
    change
      beattyIndex (s + r) =
        beattyIndex s + beattyIndex r + 1 at hCarry
    rw [hCarry]
    push_cast
    ring
  · rcases beattyIndex_add_eq_add_or_add_one s r with hZero | hOne
    · unfold beattyCarryValue
      rw [hZero]
      push_cast
      simp [hCarry]
    · exact (hCarry hOne).elim

/-- cyclic rank の整数 cast は carry values の有限和。 -/
theorem beattyCyclicCarryRank_cast_eq_sum
    (s p : ℕ) :
    (beattyCyclicCarryRank s p : ℤ) =
      ∑ u ∈ Finset.range p, beattyCarryValue s u := by
  classical
  have hNat :
      beattyCyclicCarryRank s p =
        ∑ u ∈ Finset.range p,
          if BeattyCarryOne s u then 1 else 0 := by
    unfold beattyCyclicCarryRank beattyCyclicCarrySet
    exact
      (Finset.sum_boole
        (R := ℕ)
        (fun u => BeattyCarryOne s u)
        (Finset.range p)).symm
  have hCast := congrArg (fun n : ℕ => (n : ℤ)) hNat
  push_cast at hCast
  rw [hCast]
  apply Finset.sum_congr rfl
  intro u hu
  rw [beattyCarryValue_eq_indicator]
/--
cyclic rank の one-step exact formula。

  R(s+1,p) - R(s,p)
    = (beta(s+p)-beta(s))
      - p * (beta(s+1)-beta(s)).
-/
theorem beattyCyclicCarryRank_step_cast
    (s p : ℕ) :
    (beattyCyclicCarryRank (s + 1) p : ℤ) -
        (beattyCyclicCarryRank s p : ℤ) =
      ((beattyIndex (s + p) : ℤ) - (beattyIndex s : ℤ)) -
        (p : ℤ) *
          ((beattyIndex (s + 1) : ℤ) - (beattyIndex s : ℤ)) := by
  rw [beattyCyclicCarryRank_cast_eq_sum,
      beattyCyclicCarryRank_cast_eq_sum]
  have hTerm :
      ∀ u : ℕ,
        beattyCarryValue (s + 1) u - beattyCarryValue s u =
          ((beattyIndex (s + u + 1) : ℤ) -
              (beattyIndex (s + u) : ℤ)) -
            ((beattyIndex (s + 1) : ℤ) -
              (beattyIndex s : ℤ)) := by
    intro u
    unfold beattyCarryValue
    have h0 : s + 1 + u = s + u + 1 := by omega
    rw [h0]
    ring
  have hDiff :
      (∑ u ∈ Finset.range p, beattyCarryValue (s + 1) u) -
          (∑ u ∈ Finset.range p, beattyCarryValue s u) =
        ∑ u ∈ Finset.range p,
          (beattyCarryValue (s + 1) u - beattyCarryValue s u) := by
    rw [← Finset.sum_sub_distrib]
  rw [hDiff]
  simp_rw [hTerm]
  induction p with
  | zero =>
      simp
  | succ p ih =>
      rw [Finset.sum_range_succ]
      have hIdx : s + p + 1 = s + (p + 1) := by omega
      rw [hIdx]
      push_cast
      rw [ih]
      · ring
      · simp

/--
length `p` rise が successive `k` starts で constant `p+Delta` なら、
cyclic rank difference は telescoping して

  R(s+k)-R(s)
    = k*(p+Delta) - p*(beta(s+k)-beta(s))

となる。
-/
theorem beattyCyclicCarryRank_shift_cast
    {s p Delta k : ℕ}
    (hRise :
      ∀ r : ℕ, r < k →
        beattyIndex (s + r + p) =
          beattyIndex (s + r) + p + Delta) :
    (beattyCyclicCarryRank (s + k) p : ℤ) -
        (beattyCyclicCarryRank s p : ℤ) =
      (k : ℤ) * ((p : ℤ) + (Delta : ℤ)) -
        (p : ℤ) *
          ((beattyIndex (s + k) : ℤ) - (beattyIndex s : ℤ)) := by
  revert hRise
  induction k with
  | zero =>
      intro hRise
      simp
  | succ k ih =>
      intro hRise
      have hPrev :
          ∀ r : ℕ, r < k →
            beattyIndex (s + r + p) =
              beattyIndex (s + r) + p + Delta := by
        intro r hr
        exact hRise r (by omega)
      have hIH := ih hPrev
      have hStep := beattyCyclicCarryRank_step_cast (s + k) p
      have hRiseK := hRise k (by omega)
      have hIndex : s + k + p = s + k + p := rfl
      rw [hRiseK] at hStep
      push_cast at hStep
      have hSk : s + (k + 1) = s + k + 1 := by
        omega
      rw [hSk]
      push_cast
      linear_combination hIH + hStep

/-- residual phase order に沿って cyclic carry set も包含する。 -/
theorem beattyCyclicCarrySet_subset_of_residualLE
    {s t p : ℕ}
    (hst : BeattyResidualLE s t) :
    beattyCyclicCarrySet s p ⊆ beattyCyclicCarrySet t p := by
  intro u hu
  simp only [beattyCyclicCarrySet, Finset.mem_filter, Finset.mem_range] at hu ⊢
  exact ⟨hu.1, beattyCarryOne_mono_of_residualLE hst hu.2⟩

/-- cyclic rank が同じ二 start は cyclic carry set 自体が同じ。 -/
theorem beattyCyclicCarrySet_eq_of_rank_eq
    {s t p : ℕ}
    (hRank : beattyCyclicCarryRank s p = beattyCyclicCarryRank t p) :
    beattyCyclicCarrySet s p = beattyCyclicCarrySet t p := by
  rcases beattyResidualLE_total s t with hst | hts
  · have hsub := beattyCyclicCarrySet_subset_of_residualLE (p := p) hst
    apply Finset.eq_of_subset_of_card_le hsub
    unfold beattyCyclicCarryRank at hRank
    omega
  · have hsub := beattyCyclicCarrySet_subset_of_residualLE (p := p) hts
    have hEq : beattyCyclicCarrySet t p = beattyCyclicCarrySet s p := by
      apply Finset.eq_of_subset_of_card_le hsub
      unfold beattyCyclicCarryRank at hRank
      omega
    exact hEq.symm

/-- cyclic carry set equality から、全 offset `<p` の relative Beatty rise が一致。 -/
theorem beattyDisplacement_eq_of_cyclicCarrySet_eq
    {s t p : ℕ}
    (hSet : beattyCyclicCarrySet s p = beattyCyclicCarrySet t p) :
    ∀ r : ℕ, r < p →
      beattyIndex (s + r) - beattyIndex s =
        beattyIndex (t + r) - beattyIndex t := by
  intro r hr
  have hMem :
      (r ∈ beattyCyclicCarrySet s p) ↔
        (r ∈ beattyCyclicCarrySet t p) := by
    rw [hSet]
  have hCarry : BeattyCarryOne s r ↔ BeattyCarryOne t r := by
    simpa [beattyCyclicCarrySet, hr] using hMem
  exact beattyDisplacement_eq_of_carry_iff hCarry


/--
`p` と `Delta` が互いに素で、長さ `p` の Beatty rise が一定量
`p + Delta` だけ増加すると仮定する。

このとき、同一周期内の異なる二つの offset `a < c < p` では、
cyclic carry rank は一致しない。

実際、rank が一致すると shift formula から

  p ∣ (c - a) * Delta

が従う。`p` と `Delta` は互いに素なので `p ∣ c-a` となるが、
`0 < c-a < p` に反する。
-/
theorem beattyCyclicCarryRank_ne_of_coprime
    {s p Delta a c : ℕ}
    (hCoprime : p.Coprime Delta)
    (ha : a < c)
    (hc : c < p)
    (hRise :
      ∀ r : ℕ, r < p →
        beattyIndex (s + r + p) =
          beattyIndex (s + r) + p + Delta) :
    beattyCyclicCarryRank (s + a) p ≠
      beattyCyclicCarryRank (s + c) p := by
  intro hRank
  let k := c - a
  have hkPos : 0 < k := by
    dsimp [k]
    omega
  have hkLt : k < p := by
    dsimp [k]
    omega
  have hShiftRise :
      ∀ r : ℕ, r < k →
        beattyIndex ((s + a) + r + p) =
          beattyIndex ((s + a) + r) + p + Delta := by
    intro r hr
    have har : a + r < p := by
      omega
    simpa [Nat.add_assoc] using hRise (a + r) har
  have hShift :=
    beattyCyclicCarryRank_shift_cast
      (s := s + a)
      (p := p)
      (Delta := Delta)
      (k := k)
      hShiftRise
  have hEnd :
      s + a + k = s + c := by
    dsimp [k]
    omega
  rw [hEnd, hRank] at hShift
  have hDivInt :
      (p : ℤ) ∣ ((k * Delta : ℕ) : ℤ) := by
    refine ⟨
      ((beattyIndex (s + c) : ℤ) -
          (beattyIndex (s + a) : ℤ) - (k : ℤ)), ?_⟩
    push_cast at hShift ⊢
    linear_combination -hShift
  have hDivNat :
      p ∣ k * Delta := by
    exact_mod_cast hDivInt
  have hPdvdK :
      p ∣ k :=
    hCoprime.dvd_of_dvd_mul_right hDivNat
  rcases hPdvdK with ⟨t, ht⟩
  have ht0 : t = 0 := by
    by_contra htNe
    have htPos : 0 < t :=
      Nat.pos_of_ne_zero htNe
    rw [ht] at hkLt
    nlinarith
  subst t
  simp only [mul_zero] at ht
  exact (Nat.ne_of_gt hkPos) ht

/--
primitive period `p` の p rotations では cyclic rank が `0,...,p-1` を全て取る。
-/
theorem exists_rotation_of_cyclicCarryRank_eq
    {s p Delta target : ℕ}
    (hp : 0 < p)
    (hTarget : target < p)
    (hCoprime : p.Coprime Delta)
    (hRise :
      ∀ r : ℕ, r < p →
        beattyIndex (s + r + p) =
          beattyIndex (s + r) + p + Delta) :
    ∃ r : ℕ, r < p ∧
      beattyCyclicCarryRank (s + r) p = target := by
  let f : Fin p → Fin p := fun r =>
    ⟨beattyCyclicCarryRank (s + r.1) p,
      beattyCyclicCarryRank_lt (s + r.1) p hp⟩
  have hInj : Function.Injective f := by
    intro a c hEq
    by_cases hac : a.1 = c.1
    · exact Fin.ext hac
    · rcases lt_or_gt_of_ne hac with hacLt | hcaLt
      · exfalso
        have hVal := congrArg Fin.val hEq
        exact
          (beattyCyclicCarryRank_ne_of_coprime
            hCoprime hacLt c.2 hRise) hVal
      · exfalso
        have hVal := congrArg Fin.val hEq
        exact
          (beattyCyclicCarryRank_ne_of_coprime
            hCoprime hcaLt a.2 hRise) hVal.symm
  have hSurj : Function.Surjective f :=
    Finite.surjective_of_injective hInj
  let y : Fin p := ⟨target, hTarget⟩
  rcases hSurj y with ⟨r, hr⟩
  refine ⟨r.1, r.2, ?_⟩
  exact congrArg Fin.val hr

/-- Beatty cycle numerator の universal base part。 -/
def beattyCycleBasePhi (p : ℕ) : ℤ :=
  ∑ u ∈ Finset.range p,
    (3 : ℤ) ^ (p - 1 - u) *
      (2 : ℤ) ^ beattyIndex u

/-- start `s` の carry が追加する cycle numerator part。 -/
def beattyCycleCarryPhi (s p : ℕ) : ℤ :=
  ∑ u ∈ beattyCyclicCarrySet s p,
    (3 : ℤ) ^ (p - 1 - u) *
      (2 : ℤ) ^ beattyIndex u

/-- actual Beatty displacement から作る cycle numerator。 -/
def beattyCyclePhi (s p : ℕ) : ℤ :=
  ∑ u ∈ Finset.range p,
    (3 : ℤ) ^ (p - 1 - u) *
      (2 : ℤ) ^ (beattyIndex (s + u) - beattyIndex s)

/-- Beatty cycle numerator の right-end recurrence。 -/
theorem beattyCyclePhi_succ
    (s n : ℕ) :
    beattyCyclePhi s (n + 1) =
      3 * beattyCyclePhi s n +
        (2 : ℤ) ^ (beattyIndex (s + n) - beattyIndex s) := by
  unfold beattyCyclePhi
  rw [Finset.sum_range_succ]
  have hOld :
      (∑ u ∈ Finset.range n,
        (3 : ℤ) ^ (n + 1 - 1 - u) *
          (2 : ℤ) ^ (beattyIndex (s + u) - beattyIndex s)) =
        3 *
          (∑ u ∈ Finset.range n,
            (3 : ℤ) ^ (n - 1 - u) *
              (2 : ℤ) ^ (beattyIndex (s + u) - beattyIndex s)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u hu
    have huLt : u < n := Finset.mem_range.mp hu
    have hExp : n + 1 - 1 - u = (n - 1 - u) + 1 := by omega
    rw [hExp, pow_succ]
    ring
  rw [hOld]
  have hLast : n + 1 - 1 - n = 0 := by omega
  rw [hLast]
  simp

/-- actual cycle numerator = universal base + carry contribution。 -/
theorem beattyCyclePhi_eq_base_add_carry
    (s p : ℕ) :
    beattyCyclePhi s p =
      beattyCycleBasePhi p + beattyCycleCarryPhi s p := by
  classical
  unfold beattyCyclePhi beattyCycleBasePhi beattyCycleCarryPhi
  unfold beattyCyclicCarrySet
  rw [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u hu
  by_cases hCarry : BeattyCarryOne s u
  · have hEq := hCarry
    unfold BeattyCarryOne at hEq
    have hLe : beattyIndex s ≤ beattyIndex (s + u) := by
      rw [hEq]
      omega
    have hDisp :
        beattyIndex (s + u) - beattyIndex s =
          beattyIndex u + 1 := by
      omega
    rw [hDisp, pow_succ]
    simp [hCarry]
    ring
  · rcases beattyIndex_add_eq_add_or_add_one s u with hZero | hOne
    · have hDisp :
          beattyIndex (s + u) - beattyIndex s = beattyIndex u := by
        rw [hZero]
        omega
      rw [hDisp]
      simp [hCarry]
    · exact (hCarry hOne).elim

/-- cyclic rank zero なら carry contribution は zero。 -/
theorem beattyCycleCarryPhi_eq_zero_of_rank_eq_zero
    {s p : ℕ}
    (hRank : beattyCyclicCarryRank s p = 0) :
    beattyCycleCarryPhi s p = 0 := by
  unfold beattyCyclicCarryRank at hRank
  have hEmpty : beattyCyclicCarrySet s p = ∅ :=
    Finset.card_eq_zero.mp hRank
  simp [beattyCycleCarryPhi, hEmpty]

/-- cyclic rank one なら carry contribution は単一の `2^a 3^b` term。 -/
theorem exists_beattyCycleCarryPhi_eq_single_of_rank_eq_one
    {s p : ℕ}
    (hRank : beattyCyclicCarryRank s p = 1) :
    ∃ u : ℕ,
      u < p ∧
      beattyCycleCarryPhi s p =
        (3 : ℤ) ^ (p - 1 - u) *
          (2 : ℤ) ^ beattyIndex u := by
  unfold beattyCyclicCarryRank at hRank
  rcases Finset.card_eq_one.mp hRank with ⟨u, hSet⟩
  have huMem : u ∈ beattyCyclicCarrySet s p := by
    rw [hSet]
    simp
  have huLt : u < p := by
    have := huMem
    simp only [beattyCyclicCarrySet, Finset.mem_filter, Finset.mem_range] at this
    exact this.1
  refine ⟨u, huLt, ?_⟩
  simp [beattyCycleCarryPhi, hSet]

/-- `p>0` の Beatty cycle numerator は正。 -/
theorem beattyCyclePhi_pos
    (s p : ℕ)
    (hp : 0 < p) :
    0 < beattyCyclePhi s p := by
  unfold beattyCyclePhi
  have hZeroMem : 0 ∈ Finset.range p := by simp [hp]
  have hTermNonneg :
      ∀ u ∈ Finset.range p,
        0 ≤
          (3 : ℤ) ^ (p - 1 - u) *
            (2 : ℤ) ^ (beattyIndex (s + u) - beattyIndex s) := by
    intro u hu
    positivity
  have hTerm0 :
      0 <
        (3 : ℤ) ^ (p - 1 - 0) *
          (2 : ℤ) ^ (beattyIndex (s + 0) - beattyIndex s) := by
    simp
  have hLe :
      (3 : ℤ) ^ (p - 1 - 0) *
          (2 : ℤ) ^ (beattyIndex (s + 0) - beattyIndex s) ≤
        ∑ u ∈ Finset.range p,
          (3 : ℤ) ^ (p - 1 - u) *
            (2 : ℤ) ^ (beattyIndex (s + u) - beattyIndex s) := by
    exact Finset.single_le_sum hTermNonneg hZeroMem
  exact lt_of_lt_of_le hTerm0 hLe

end ExternalArithmetic
end CSTMicro
end Collatz2
