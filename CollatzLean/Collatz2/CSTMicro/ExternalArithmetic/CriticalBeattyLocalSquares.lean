import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.CriticalPrefixOstrowski

/-!
# Critical Beatty local squares

critical Beatty/Sturmian exponent sequence

  e_s = beattyIndex (s+1) - beattyIndex s

の length-r block が二回連続することを、relative Beatty rise の一致として表す。
この表現なら affine interval numerator の一致を直接証明できる。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

open scoped BigOperators

/--
`[s,s+r)` と `[s+r,s+2r)` が同じ critical Beatty exponent block を持つ。

one-cell increments の一致と同値だが、後段で使う cumulative rise を field にする。
-/
structure CriticalBeattySquareAt (s r : ℕ) : Prop where
  root_pos : 0 < r
  prefixRise_eq :
    ∀ k : ℕ, k ≤ r →
      beattyIndex (s + k) - beattyIndex s =
        beattyIndex (s + r + k) - beattyIndex (s + r)

namespace CriticalBeattySquareAt

/-- square の最初の one-cell two-depth は一致する。 -/
theorem firstStep_eq
    {s r : ℕ}
    (B : CriticalBeattySquareAt s r) :
    beattyIndex (s + 1) - beattyIndex s =
      beattyIndex (s + r + 1) - beattyIndex (s + r) := by
  exact B.prefixRise_eq 1
    (Nat.succ_le_iff.mpr B.root_pos)

/-- square の total two-depth は一致する。 -/
theorem totalRise_eq
    {s r : ℕ}
    (B : CriticalBeattySquareAt s r) :
    beattyIndex (s + r) - beattyIndex s =
      beattyIndex (s + 2 * r) - beattyIndex (s + r) := by
  have h := B.prefixRise_eq r le_rfl
  simpa [two_mul, Nat.add_assoc] using h

/--
最初の文字を落とした二つの suffix block も一致する。
root `r>=2` のとき length `r-1` の block

  [s+1, s+r)  と  [s+r+1, s+2r)

の relative Beatty rise が全 prefix で一致する。
-/
theorem tailPrefixRise_eq
    {s r k : ℕ}
    (B : CriticalBeattySquareAt s r)
    (hk : k ≤ r - 1) :
    beattyIndex (s + 1 + k) - beattyIndex (s + 1) =
      beattyIndex (s + r + 1 + k) - beattyIndex (s + r + 1) := by
  have hrPredLt :
      r - 1 < r := by
    exact Nat.sub_lt B.root_pos (by norm_num)
  have hkLt :
      k < r :=
    lt_of_le_of_lt hk hrPredLt
  have hk1 :
      k + 1 ≤ r :=
    Nat.succ_le_iff.mpr hkLt
  have h1 := B.prefixRise_eq 1 (by omega)
  have hk1eq := B.prefixRise_eq (k + 1) hk1
  have hMonoS : beattyIndex s ≤ beattyIndex (s + 1) :=
    le_of_lt (beattyIndex_strictMono (by omega))
  have hMonoSk : beattyIndex (s + 1) ≤ beattyIndex (s + 1 + k) := by
    by_cases hk0 : k = 0
    · subst k
      simp
    · exact le_of_lt (beattyIndex_strictMono (by omega))
  have hMonoR : beattyIndex (s + r) ≤ beattyIndex (s + r + 1) :=
    le_of_lt (beattyIndex_strictMono (by omega))
  have hMonoRk :
      beattyIndex (s + r + 1) ≤ beattyIndex (s + r + 1 + k) := by
    by_cases hk0 : k = 0
    · subst k
      simp
    · exact le_of_lt (beattyIndex_strictMono (by omega))
  have hA :
      beattyIndex (s + 1) - beattyIndex s =
        beattyIndex (s + r + 1) - beattyIndex (s + r) := by
    simpa [Nat.add_assoc] using h1
  have hB :
      beattyIndex (s + 1 + k) - beattyIndex s =
        beattyIndex (s + r + 1 + k) - beattyIndex (s + r) := by
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hk1eq
  omega

end CriticalBeattySquareAt

/-- `Ico a (a+n)` を local offset range に移す。 -/
private theorem square_sum_Ico_eq_sum_range
    {α : Type*}
    [AddCommMonoid α]
    (f : ℕ → α)
    (a n : ℕ) :
    Finset.sum (Finset.Ico a (a + n)) f =
      Finset.sum (Finset.range n) (fun i => f (a + i)) := by
  symm
  refine Finset.sum_bij (fun i _ => a + i) ?_ ?_ ?_ ?_
  · intro i hi
    have hiLt : i < n := Finset.mem_range.mp hi
    exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
  · intro i₁ hi₁ i₂ hi₂ hEq
    omega
  · intro k hk
    have hkIco := Finset.mem_Ico.mp hk
    refine ⟨k - a, Finset.mem_range.mpr ?_, ?_⟩
    · omega
    · omega
  · intro i hi
    rfl

/--
同じ長さの二 interval で全 relative Beatty prefix height が一致すれば、
critical interval numerator も exact に一致する。
-/
theorem criticalIntervalPhiZ_eq_of_relativeBeatty
    {s t n : ℕ}
    (hRise :
      ∀ k : ℕ, k < n →
        beattyIndex (s + k) - beattyIndex s =
          beattyIndex (t + k) - beattyIndex t) :
    criticalIntervalPhiZ s (s + n) =
      criticalIntervalPhiZ t (t + n) := by
  unfold criticalIntervalPhiZ
  rw [square_sum_Ico_eq_sum_range
    (fun k =>
      (2 : ℤ) ^ (beattyIndex k - beattyIndex s) *
        (3 : ℤ) ^ (s + n - 1 - k)) s n]
  rw [square_sum_Ico_eq_sum_range
    (fun k =>
      (2 : ℤ) ^ (beattyIndex k - beattyIndex t) *
        (3 : ℤ) ^ (t + n - 1 - k)) t n]
  apply Finset.sum_congr rfl
  intro k hk
  have hkLt : k < n := Finset.mem_range.mp hk
  have hThreeS : s + n - 1 - (s + k) = n - 1 - k := by omega
  have hThreeT : t + n - 1 - (t + k) = n - 1 - k := by omega
  rw [hRise k hkLt, hThreeS, hThreeT]

/--
Beatty index は一列進むごとに少なくとも 1 増えるので、
shifted interval の total two-depth は interval length 以上。
-/
theorem intervalLength_le_beattyRise
    (a n : ℕ) :
    n ≤ beattyIndex (a + n) - beattyIndex a := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hStep :
          beattyIndex (a + n) < beattyIndex (a + (n + 1)) := by
        exact beattyIndex_strictMono (by omega)
      have hBase : beattyIndex a ≤ beattyIndex (a + n) := by
        by_cases hn0 : n = 0
        · subst n
          simp
        · exact le_of_lt (beattyIndex_strictMono (by omega))
      omega

/--
root `r>=2` の square の最初の文字を落とした length `r-1` blocks は
critical interval numerator まで exact に一致する。
-/
theorem CriticalBeattySquareAt.tailPhi_eq
    {s r : ℕ}
    (B : CriticalBeattySquareAt s r) :
    criticalIntervalPhiZ
        (s + 1) (s + 1 + (r - 1)) =
      criticalIntervalPhiZ
        (s + r + 1) (s + r + 1 + (r - 1)) := by
  apply criticalIntervalPhiZ_eq_of_relativeBeatty
  intro k hk
  exact B.tailPrefixRise_eq (by omega)

/--
同じ tail blocks の total two-depth も一致する。
-/
theorem CriticalBeattySquareAt.tailTotalRise_eq
    {s r : ℕ}
    (B : CriticalBeattySquareAt s r) :
    beattyIndex (s + 1 + (r - 1)) - beattyIndex (s + 1) =
      beattyIndex (s + r + 1 + (r - 1)) - beattyIndex (s + r + 1) := by
  exact B.tailPrefixRise_eq (k := r - 1) le_rfl

end ExternalArithmetic
end CSTMicro
end Collatz2
