import CollatzLean.Collatz2.CSTMicro.CarryGeometry.ColumnLayerCostDynamics
import CollatzLean.Collatz2.CSTMicro.CarryGeometry.CriticalBoundaryExtraDepth

/-!
# Admissible critical Sturmian profiles

critical Beatty roof

  beta_k = beattyIndex k = criticalHeight k

から extra-depth profile `h(k)` を引いた checkpoint

  p_k = beta_k - h(k)

を純粋 object として扱う。

actual odd-only word では `h = parityExtraDepth` であり、prefix depth が critical roof 以下なら
この checkpoint は exact に `prefixTwoDepth` と一致する。

admissible profile は

* `h(k) <= beta_k`,
* checkpoint `p_k` が strict に増加する

という二条件だけを保持する。
Beatty gap は exact に 1 または 2 なので、admissible profile は局所的に

* gap 1 なら height は増えない、
* gap 2 でも高々 1 しか増えない

という Ferrers/Sturmian 制約を満たす。
-/

namespace Collatz2
namespace CSTMicro

/-- `k=0` を含め、Beatty position と odd-only critical roof は常に一致する。 -/
theorem beattyIndex_eq_wordCriticalHeight_all
    (k : ℕ) :
    beattyIndex k = Collatz2.Word.criticalHeight k := by
  by_cases hk0 : k = 0
  · subst k
    simp [Collatz2.Word.criticalHeight]
  · exact beattyIndex_eq_wordCriticalHeight (Nat.pos_of_ne_zero hk0)

/-- profile `h` から復元する odd checkpoint。 -/
def profileCheckpoint
    (h : ℕ → ℕ)
    (k : ℕ) : ℕ :=
  beattyIndex k - h k

/--
critical roof の下にある column-height profile の純粋 admissibility 条件。
-/
def AdmissibleSturmianProfile
    (m : ℕ)
    (h : ℕ → ℕ) : Prop :=
  (∀ k : ℕ, k < m → h k ≤ beattyIndex k) ∧
  (∀ k : ℕ, k + 1 < m →
    profileCheckpoint h k < profileCheckpoint h (k + 1))

namespace AdmissibleSturmianProfile

/-- admissible profile は各 relevant column で Beatty roof 以下。 -/
theorem depth_le
    {m : ℕ}
    {h : ℕ → ℕ}
    (A : AdmissibleSturmianProfile m h)
    {k : ℕ}
    (hk : k < m) :
    h k ≤ beattyIndex k :=
  A.1 k hk

/-- admissible profile の checkpoint は consecutive columns で strict。 -/
theorem checkpoint_strict
    {m : ℕ}
    {h : ℕ → ℕ}
    (A : AdmissibleSturmianProfile m h)
    {k : ℕ}
    (hk : k + 1 < m) :
    profileCheckpoint h k < profileCheckpoint h (k + 1) :=
  A.2 k hk

end AdmissibleSturmianProfile

/-- Beatty index は一 step で高々 2 増える。 -/
theorem beattyIndex_succ_le_add_two
    (k : ℕ) :
    beattyIndex (k + 1) ≤ beattyIndex k + 2 := by
  apply beattyIndex_le_of_upper
  have hUpper := beattyIndex_upper k
  calc
    3 ^ (k + 1)
        = 3 ^ k * 3 := by rw [pow_succ]
    _ ≤ 2 ^ (beattyIndex k + 1) * 4 := by
          exact Nat.mul_le_mul hUpper (by norm_num)
    _ = 2 ^ ((beattyIndex k + 2) + 1) := by
          rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]

/-- Beatty gap は exact に 1 または 2。 -/
theorem beattyIndex_succ_eq_add_one_or_two
    (k : ℕ) :
    beattyIndex (k + 1) = beattyIndex k + 1 ∨
      beattyIndex (k + 1) = beattyIndex k + 2 := by
  have hStrict := beattyIndex_lt_succ k
  have hUpper := beattyIndex_succ_le_add_two k
  omega

/-- canonical column position は Beatty roof で書いても同じ。 -/
theorem columnLayerPosition_eq_beattyIndex
    (k j : ℕ) :
    columnLayerPosition k j = beattyIndex k - j - 1 := by
  unfold columnLayerPosition
  rw [← beattyIndex_eq_wordCriticalHeight_all k]

/--
actual parity profile の checkpoint は prefix depth に戻る。
-/
theorem profileCheckpoint_parityExtraDepth_eq_prefixTwoDepth
    (v : ParityWord)
    (k : ℕ)
    (hRoof :
      Collatz2.Word.prefixTwoDepth (exponentWordOfParity v) k ≤
        Collatz2.Word.criticalHeight k) :
    profileCheckpoint (parityExtraDepth v) k =
      Collatz2.Word.prefixTwoDepth (exponentWordOfParity v) k := by
  unfold profileCheckpoint parityExtraDepth Collatz2.Word.extraDepth
  rw [beattyIndex_eq_wordCriticalHeight_all]
  omega

/--
actual parity profileについて、roof condition と checkpoint strictness だけ与えれば
pure admissible profile へ落ちる。
-/
theorem admissibleSturmianProfile_of_parityExtraDepth
    (v : ParityWord)
    (m : ℕ)
    (hRoof :
      ∀ k : ℕ, k < m →
        Collatz2.Word.prefixTwoDepth (exponentWordOfParity v) k ≤
          Collatz2.Word.criticalHeight k)
    (hStrict :
      ∀ k : ℕ, k + 1 < m →
        Collatz2.Word.prefixTwoDepth (exponentWordOfParity v) k <
          Collatz2.Word.prefixTwoDepth (exponentWordOfParity v) (k + 1)) :
    AdmissibleSturmianProfile m (parityExtraDepth v) := by
  constructor
  · intro k hk
    have hLe := hRoof k hk
    unfold parityExtraDepth Collatz2.Word.extraDepth
    rw [← beattyIndex_eq_wordCriticalHeight_all k]
    omega
  · intro k hk
    rw [profileCheckpoint_parityExtraDepth_eq_prefixTwoDepth
      v k (hRoof k (by omega))]
    rw [profileCheckpoint_parityExtraDepth_eq_prefixTwoDepth
      v (k + 1) (hRoof (k + 1) hk)]
    exact hStrict k hk

namespace AdmissibleSturmianProfile

/-- Beatty gap 1 の column boundary では profile height は増えない。 -/
theorem next_depth_le_of_gap_one
    {m : ℕ}
    {h : ℕ → ℕ}
    (A : AdmissibleSturmianProfile m h)
    {k : ℕ}
    (hk : k + 1 < m)
    (hGap : beattyIndex (k + 1) = beattyIndex k + 1) :
    h (k + 1) ≤ h k := by
  have hk0 : k < m := by omega
  have hRoof0 := A.depth_le hk0
  have hRoof1 := A.depth_le hk
  have hStep := A.checkpoint_strict hk
  unfold profileCheckpoint at hStep
  rw [hGap] at hStep
  omega

/-- Beatty gap 2 の column boundary でも profile height は高々 1 だけ増える。 -/
theorem next_depth_le_add_one_of_gap_two
    {m : ℕ}
    {h : ℕ → ℕ}
    (A : AdmissibleSturmianProfile m h)
    {k : ℕ}
    (hk : k + 1 < m)
    (hGap : beattyIndex (k + 1) = beattyIndex k + 2) :
    h (k + 1) ≤ h k + 1 := by
  have hk0 : k < m := by omega
  have hRoof0 := A.depth_le hk0
  have hRoof1 := A.depth_le hk
  have hStep := A.checkpoint_strict hk
  unfold profileCheckpoint at hStep
  rw [hGap] at hStep
  omega

/-- 任意の adjacent relevant columns で profile height は高々 1 増える。 -/
theorem next_depth_le_add_one
    {m : ℕ}
    {h : ℕ → ℕ}
    (A : AdmissibleSturmianProfile m h)
    {k : ℕ}
    (hk : k + 1 < m) :
    h (k + 1) ≤ h k + 1 := by
  rcases beattyIndex_succ_eq_add_one_or_two k with hGap | hGap
  · have h := A.next_depth_le_of_gap_one hk hGap
    omega
  · exact A.next_depth_le_add_one_of_gap_two hk hGap

end AdmissibleSturmianProfile

end CSTMicro
end Collatz2
