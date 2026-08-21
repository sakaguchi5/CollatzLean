import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.BHZCriticalProposition33Port

/-!
# critical Beatty の one-short square

完全な square は period `r` の一致を `2*r` 文字まで要求する。
Pure B の局所剛性では最後の一文字を使わずに差分輸送を組めるため、
ここでは一文字だけ短い

  prefix length >= 2*r - 1

を独立な構造として定式化する。

`CriticalBeattyOneShortSquareAt s r` は、二つの period block のうち
最後の一文字だけを落とした範囲で relative Beatty rise が一致することを表す。
root は後段で `r-2` 長の tail transfer を使うため `r>=2` を要求する。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/--
phase `s` から period `r` の one-short square が始まる。

`k <= r-1` まで cumulative rise が一致するので、binary word としては
最初の `2*r-1` 文字が period `r` を持つ。
-/
structure CriticalBeattyOneShortSquareAt (s r : ℕ) : Prop where
  root_two : 2 ≤ r
  prefixRise_eq :
    ∀ k : ℕ, k ≤ r - 1 →
      beattyIndex (s + k) - beattyIndex s =
        beattyIndex (s + r + k) - beattyIndex (s + r)

namespace CriticalBeattyOneShortSquareAt

/-- root は正。 -/
theorem root_pos
    {s r : ℕ}
    (B : CriticalBeattyOneShortSquareAt s r) :
    0 < r := by
  have hrTwo : 2 ≤ r := B.root_two
  omega

/-- one-short square でも最初の一文字は二 block で一致する。 -/
theorem firstStep_eq
    {s r : ℕ}
    (B : CriticalBeattyOneShortSquareAt s r) :
    beattyIndex (s + 1) - beattyIndex s =
      beattyIndex (s + r + 1) - beattyIndex (s + r) := by
  apply B.prefixRise_eq 1
  have hrTwo : 2 ≤ r := B.root_two
  omega

/--
最初の文字を落とした後は、さらに最後の一文字も落とした
length `r-2` の二 block が一致する。
-/
theorem tailPrefixRise_eq
    {s r k : ℕ}
    (B : CriticalBeattyOneShortSquareAt s r)
    (hk : k ≤ r - 2) :
    beattyIndex (s + 1 + k) - beattyIndex (s + 1) =
      beattyIndex (s + r + 1 + k) - beattyIndex (s + r + 1) := by
  have hrTwo : 2 ≤ r := B.root_two
  have hk1 : k + 1 ≤ r - 1 := by
    omega
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

/-- one-short square の tail interval numerator は exact に一致する。 -/
theorem tailPhi_eq
    {s r : ℕ}
    (B : CriticalBeattyOneShortSquareAt s r) :
    criticalIntervalPhiZ
        (s + 1) (s + 1 + (r - 2)) =
      criticalIntervalPhiZ
        (s + r + 1) (s + r + 1 + (r - 2)) := by
  apply criticalIntervalPhiZ_eq_of_relativeBeatty
  intro k hk
  exact B.tailPrefixRise_eq (by omega)

/-- one-short square の tail total rise も一致する。 -/
theorem tailTotalRise_eq
    {s r : ℕ}
    (B : CriticalBeattyOneShortSquareAt s r) :
    beattyIndex (s + 1 + (r - 2)) - beattyIndex (s + 1) =
      beattyIndex (s + r + 1 + (r - 2)) - beattyIndex (s + r + 1) := by
  exact B.tailPrefixRise_eq (k := r - 2) le_rfl

end CriticalBeattyOneShortSquareAt

/-- 完全な square は root `r>=2` なら one-short square でもある。 -/
theorem CriticalBeattySquareAt.toOneShort
    {s r : ℕ}
    (B : CriticalBeattySquareAt s r)
    (hrTwo : 2 ≤ r) :
    CriticalBeattyOneShortSquareAt s r := by
  refine ⟨hrTwo, ?_⟩
  intro k hk
  exact B.prefixRise_eq k (by omega)

/--
shifted BHZ bit が `i<r-1` の範囲で period `r` を持てば、
actual Beatty one-short square になる。
-/
theorem criticalBeattyOneShortSquareAt_of_criticalShiftBit_blocks
    {s r : ℕ}
    (hrTwo : 2 ≤ r)
    (hBlock :
      ∀ i : ℕ, i < r - 1 →
        criticalShiftBit s i =
          criticalShiftBit s (r + i)) :
    CriticalBeattyOneShortSquareAt s r := by
  refine ⟨hrTwo, ?_⟩
  intro k hk
  induction k with
  | zero =>
      simp
  | succ k ih =>
      have hkLe : k ≤ r - 1 := by
        omega
      have hkLt : k < r - 1 := by
        omega
      have hPrev := ih hkLe
      have hBit := hBlock k hkLt
      have hInc0 :=
        beattyIncrement_eq_of_incrementBit_eq
          (by simpa [criticalShiftBit, Nat.add_assoc] using hBit)
      have hInc :
          beattyIndex (s + k + 1) - beattyIndex (s + k) =
            beattyIndex (s + r + k + 1) - beattyIndex (s + r + k) := by
        simpa [Nat.add_assoc] using hInc0
      have hLeft := beattyRelativeRise_succ s k
      have hRight := beattyRelativeRise_succ (s + r) k
      calc
        beattyIndex (s + (k + 1)) - beattyIndex s
            =
          (beattyIndex (s + k) - beattyIndex s) +
            (beattyIndex (s + k + 1) - beattyIndex (s + k)) := hLeft
        _ =
          (beattyIndex (s + r + k) - beattyIndex (s + r)) +
            (beattyIndex (s + r + k + 1) - beattyIndex (s + r + k)) := by
              rw [hPrev, hInc]
        _ =
          beattyIndex (s + r + (k + 1)) - beattyIndex (s + r) := by
            simpa [Nat.add_assoc] using hRight.symm

namespace CriticalShiftInitialPeriod

/--
initial period の長さが `2*root-1` 以上なら one-short square を得る。
完全 square に必要な最後の一文字は要求しない。
-/
theorem toCriticalBeattyOneShortSquareAt
    {s root length : ℕ}
    (H : CriticalShiftInitialPeriod s root length)
    (hRootTwo : 2 ≤ root)
    (hOneShort : 2 * root - 1 ≤ length) :
    CriticalBeattyOneShortSquareAt s root := by
  apply criticalBeattyOneShortSquareAt_of_criticalShiftBit_blocks hRootTwo
  intro i hi
  have hDomain : i + root < length := by
    have hBefore : i + root < 2 * root - 1 := by
      omega
    exact lt_of_lt_of_le hBefore hOneShort
  have hEq := H.periodic i hDomain
  simpa [Nat.add_comm] using hEq

end CriticalShiftInitialPeriod

end ExternalArithmetic
end CSTMicro
end Collatz2
