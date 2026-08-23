import CollatzLean.Collatz2.CSTMicro.BeattyPositions
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Beatty gap factor repeat

`beattyIndex n` の first difference は mechanical/Sturmian word になるが、
ここでは一般の Sturmian factor-complexity theorem や実数 logarithm を使わない。

加法 carry

  beta(s+r) = beta(s) + beta(r)       または
  beta(s+r) = beta(s) + beta(r) + 1

を power inequality だけから取り出す。

固定した長さ `m` では、start `s` に対応する carry 集合は residual phase の順序に
沿って包含関係で並ぶ。その cardinality は `0,...,m` の `m+1` 通りしかないので、
`m+2` 個の start の中には同じ carry 集合を持つ二つがある。

従って長さ `m` の Beatty displacement block は必ず反復する。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/-- `beta(s+r)` の加法 carry が 1 であること。 -/
def BeattyCarryOne (s r : ℕ) : Prop :=
  beattyIndex (s + r) = beattyIndex s + beattyIndex r + 1

/-- Beatty index の加法誤差は高々 1。 -/
theorem beattyIndex_add_eq_add_or_add_one
    (s r : ℕ) :
    beattyIndex (s + r) = beattyIndex s + beattyIndex r ∨
      beattyIndex (s + r) = beattyIndex s + beattyIndex r + 1 := by
  have hUpper :
      beattyIndex (s + r) ≤ beattyIndex s + beattyIndex r + 1 := by
    apply beattyIndex_le_of_upper
    calc
      3 ^ (s + r) = 3 ^ s * 3 ^ r := by rw [pow_add]
      _ ≤ 2 ^ (beattyIndex s + 1) * 2 ^ (beattyIndex r + 1) :=
        Nat.mul_le_mul (beattyIndex_upper s) (beattyIndex_upper r)
      _ = 2 ^ ((beattyIndex s + beattyIndex r + 1) + 1) := by
        rw [← pow_add]
        congr 1
        omega
  have hLower :
      beattyIndex s + beattyIndex r ≤ beattyIndex (s + r) := by
    by_cases hs0 : s = 0
    · subst s
      simp
    · by_cases hr0 : r = 0
      · subst r
        simp
      · have hsPos : 0 < s := Nat.pos_of_ne_zero hs0
        have hrPos : 0 < r := Nat.pos_of_ne_zero hr0
        have hsStrict := beattyIndex_lower_strict_of_pos hsPos
        have hrLower := beattyIndex_lower r
        have hMulStrict :
            2 ^ (beattyIndex s + beattyIndex r) < 3 ^ (s + r) := by
          rw [pow_add, pow_add]
          have hPowPos :
              0 < 2 ^ beattyIndex r := by
            positivity
          have h1 :
              2 ^ beattyIndex s * 2 ^ beattyIndex r <
                3 ^ s * 2 ^ beattyIndex r := by
            exact
              (Nat.mul_lt_mul_right hPowPos).2 hsStrict
          have h2 :
              3 ^ s * 2 ^ beattyIndex r ≤
                3 ^ s * 3 ^ r := by
            exact Nat.mul_le_mul_left _ hrLower
          exact lt_of_lt_of_le h1 h2
        by_contra hnot
        have hExp :
            beattyIndex (s + r) + 1 ≤ beattyIndex s + beattyIndex r := by
          omega
        have hPowLe :
            2 ^ (beattyIndex (s + r) + 1) ≤
              2 ^ (beattyIndex s + beattyIndex r) :=
          Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) hExp
        have hBeattyUpper := beattyIndex_upper (s + r)
        omega
  omega

/-- carry=1 は residual products が threshold `2` を越えることと同値。 -/
theorem beattyCarryOne_iff_threshold
    (s r : ℕ) :
    BeattyCarryOne s r ↔
      2 ^ (beattyIndex s + beattyIndex r + 1) < 3 ^ (s + r) := by
  constructor
  · intro hCarry
    have hPos : 0 < s + r := by
      by_contra hnot
      have hs : s = 0 := by omega
      have hr : r = 0 := by omega
      subst s
      subst r
      simp [BeattyCarryOne] at hCarry
    have hStrict := beattyIndex_lower_strict_of_pos hPos
    unfold BeattyCarryOne at hCarry
    rw [hCarry] at hStrict
    exact hStrict
  · intro hThreshold
    rcases beattyIndex_add_eq_add_or_add_one s r with hZero | hOne
    · have hUpper := beattyIndex_upper (s + r)
      rw [hZero] at hUpper
      exact (not_lt_of_ge hUpper hThreshold).elim
    · exact hOne

/-- residual phase の power-form order。 -/
def BeattyResidualLE (s t : ℕ) : Prop :=
  3 ^ s * 2 ^ beattyIndex t ≤
    3 ^ t * 2 ^ beattyIndex s

/-- residual phase order は total。 -/
theorem beattyResidualLE_total
    (s t : ℕ) :
    BeattyResidualLE s t ∨ BeattyResidualLE t s := by
  unfold BeattyResidualLE
  exact le_total _ _

/-- residual phase を右へ増やすと、既に発生した carry は失われない。 -/
theorem beattyCarryOne_mono_of_residualLE
    {s t r : ℕ}
    (hst : BeattyResidualLE s t)
    (hCarry : BeattyCarryOne s r) :
    BeattyCarryOne t r := by
  have hThreshold := (beattyCarryOne_iff_threshold s r).1 hCarry
  have hMul :
      2 ^ (beattyIndex s + beattyIndex r + 1) * 2 ^ beattyIndex t <
        3 ^ (s + r) * 2 ^ beattyIndex t := by
    have hPowPosT :
        0 < 2 ^ beattyIndex t := by
      positivity
    exact
      (Nat.mul_lt_mul_right hPowPosT).2 hThreshold
  have hPhaseMul :
      (3 ^ s * 2 ^ beattyIndex t) * 3 ^ r ≤
        (3 ^ t * 2 ^ beattyIndex s) * 3 ^ r :=
    Nat.mul_le_mul_right _ hst
  have hCombined :
      2 ^ (beattyIndex s + beattyIndex r + 1) * 2 ^ beattyIndex t <
        (3 ^ t * 2 ^ beattyIndex s) * 3 ^ r := by
    have hMid :
        3 ^ (s + r) * 2 ^ beattyIndex t =
          (3 ^ s * 2 ^ beattyIndex t) * 3 ^ r := by
      rw [pow_add]
      ring
    rw [hMid] at hMul
    exact lt_of_lt_of_le hMul hPhaseMul
  have hScaled :
      2 ^ (beattyIndex t + beattyIndex r + 1) * 2 ^ beattyIndex s <
        3 ^ (t + r) * 2 ^ beattyIndex s := by
    rw [pow_add]
    simpa [pow_add, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hCombined
  have hPos : 0 < 2 ^ beattyIndex s :=
    Nat.pow_pos (by norm_num)
  have hTarget :
      2 ^ (beattyIndex t + beattyIndex r + 1) < 3 ^ (t + r) :=
    (Nat.mul_lt_mul_right hPos).1 hScaled
  exact (beattyCarryOne_iff_threshold t r).2 hTarget

/-- `BeattyCarryOne` は Nat equality なので decidable。 -/
private instance beattyCarryOne_decidable
    (s r : ℕ) :
    Decidable (BeattyCarryOne s r) := by
  unfold BeattyCarryOne
  infer_instance

/-- length `m` で carry=1 になる offsets `1,...,m`。 -/
def beattyCarrySet (s m : ℕ) : Finset ℕ :=
  (Finset.range m).filter (fun u => BeattyCarryOne s (u + 1))

/-- carry set の cardinality。 -/
def beattyCarryRank (s m : ℕ) : ℕ :=
  (beattyCarrySet s m).card

/-- carry rank は `m` 以下。 -/
theorem beattyCarryRank_le
    (s m : ℕ) :
    beattyCarryRank s m ≤ m := by
  unfold beattyCarryRank beattyCarrySet
  calc
    ((Finset.range m).filter
        (fun u : ℕ => BeattyCarryOne s (u + 1))).card
        ≤ (Finset.range m).card := by
          exact Finset.card_le_card
            (Finset.filter_subset
              (fun u : ℕ => BeattyCarryOne s (u + 1))
              (Finset.range m))
    _ = m := by
      simp

/-- residual phase order に沿って carry set は包含する。 -/
theorem beattyCarrySet_subset_of_residualLE
    {s t m : ℕ}
    (hst : BeattyResidualLE s t) :
    beattyCarrySet s m ⊆ beattyCarrySet t m := by
  intro u hu
  simp only [beattyCarrySet, Finset.mem_filter, Finset.mem_range] at hu ⊢
  exact ⟨hu.1, beattyCarryOne_mono_of_residualLE hst hu.2⟩

/-- 同じ rank を持つ start は同じ carry set を持つ。 -/
theorem beattyCarrySet_eq_of_rank_eq
    {s t m : ℕ}
    (hRank : beattyCarryRank s m = beattyCarryRank t m) :
    beattyCarrySet s m = beattyCarrySet t m := by
  rcases beattyResidualLE_total s t with hst | hts
  · have hsub := beattyCarrySet_subset_of_residualLE (m := m) hst
    apply Finset.eq_of_subset_of_card_le hsub
    unfold beattyCarryRank at hRank
    omega
  · have hsub := beattyCarrySet_subset_of_residualLE (m := m) hts
    have hEq : beattyCarrySet t m = beattyCarrySet s m := by
      apply Finset.eq_of_subset_of_card_le hsub
      unfold beattyCarryRank at hRank
      omega
    exact hEq.symm

/-- carry status が一致すれば、その offset までの Beatty displacement も一致する。 -/
theorem beattyDisplacement_eq_of_carry_iff
    {s t r : ℕ}
    (hCarry : BeattyCarryOne s r ↔ BeattyCarryOne t r) :
    beattyIndex (s + r) - beattyIndex s =
      beattyIndex (t + r) - beattyIndex t := by
  by_cases hs : BeattyCarryOne s r
  · have ht : BeattyCarryOne t r := hCarry.mp hs
    unfold BeattyCarryOne at hs ht
    omega
  · have ht : ¬ BeattyCarryOne t r := by
      intro htc
      exact hs (hCarry.mpr htc)
    rcases beattyIndex_add_eq_add_or_add_one s r with hs0 | hs1
    · rcases beattyIndex_add_eq_add_or_add_one t r with ht0 | ht1
      · omega
      · exact (ht ht1).elim
    · exact (hs hs1).elim

/-- 同じ carry set なら length `m` の cumulative Beatty displacement block が一致。 -/
theorem beattyDisplacementBlock_eq_of_carrySet_eq
    {s t m : ℕ}
    (hSet : beattyCarrySet s m = beattyCarrySet t m) :
    ∀ r : ℕ, r ≤ m →
      beattyIndex (s + r) - beattyIndex s =
        beattyIndex (t + r) - beattyIndex t := by
  intro r hr
  by_cases hr0 : r = 0
  · subst r
    simp
  · let u := r - 1
    have hu : u < m := by
      dsimp [u]
      omega
    have hur : u + 1 = r := by
      dsimp [u]
      omega
    have hMem :
        (u ∈ beattyCarrySet s m) ↔
          (u ∈ beattyCarrySet t m) := by
      rw [hSet]
    have hCarry : BeattyCarryOne s r ↔ BeattyCarryOne t r := by
      simpa [beattyCarrySet, hu, hur] using hMem
    exact beattyDisplacement_eq_of_carry_iff hCarry

/--
任意の `m+2` 個の consecutive start の中には、長さ `m` の Beatty displacement block が
一致する二つがある。

これは必要な `p(m) ≤ m+1` の power-form version。
-/
theorem exists_repeated_beattyDisplacementBlock
    (b m : ℕ) :
    ∃ i j : ℕ,
      i < j ∧
      j ≤ m + 1 ∧
      ∀ r : ℕ, r ≤ m →
        beattyIndex (b + j + r) - beattyIndex (b + j) =
          beattyIndex (b + i + r) - beattyIndex (b + i) := by
  let f : Fin (m + 2) → Fin (m + 1) := fun k =>
    ⟨beattyCarryRank (b + k.1) m,
      Nat.lt_succ_of_le (beattyCarryRank_le (b + k.1) m)⟩
  have hPair : ∃ a c : Fin (m + 2), a ≠ c ∧ f a = f c := by
    by_contra hNo
    have hInj : Function.Injective f := by
      intro a c hac
      by_contra hne
      exact hNo ⟨a, c, hne, hac⟩
    have hCard := Fintype.card_le_of_injective f hInj
    simp at hCard
  rcases hPair with ⟨a, c, hac, hRankFin⟩
  have hacVal : a.1 ≠ c.1 := by
    intro h
    apply hac
    exact Fin.ext h
  have hRank :
      beattyCarryRank (b + a.1) m =
        beattyCarryRank (b + c.1) m := by
    exact congrArg Fin.val hRankFin
  have hSet := beattyCarrySet_eq_of_rank_eq hRank
  have hBlocks := beattyDisplacementBlock_eq_of_carrySet_eq hSet
  rcases lt_or_gt_of_ne hacVal with hacLt | hcaLt
  · refine ⟨a.1, c.1, hacLt, ?_, ?_⟩
    · have hcLt := c.2
      omega
    · intro r hr
      simpa [Nat.add_assoc] using (hBlocks r hr).symm
  · refine ⟨c.1, a.1, hcaLt, ?_, ?_⟩
    · have haLt := a.2
      omega
    · intro r hr
      have h := hBlocks r hr
      simpa [Nat.add_assoc] using h

end ExternalArithmetic
end CSTMicro
end Collatz2
