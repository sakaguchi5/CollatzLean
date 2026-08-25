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
  simpa using
    (beattyIndex_add_upper_of_threePow_le_twoPow
      (k := k) (r := 1) (s := 2)
      (by norm_num : 3 ^ 1 ≤ 2 ^ 2))

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

/--
admissible profile で `b` が最初の positive-depth index なら、その depth は exact に 1。

SingleCorner 固有ではなく、Beatty roof と one-step depth bound だけの帰結。
-/
theorem firstPositiveDepth_eq_one
    {m : ℕ}
    {h : ℕ → ℕ}
    (A : AdmissibleSturmianProfile m h)
    {b : ℕ}
    (hbM : b < m)
    (hbPos : 0 < h b)
    (hBefore : ∀ k : ℕ, k < b → h k = 0) :
    h b = 1 := by
  by_cases hb0 : b = 0
  · subst b
    have hDepth := A.depth_le hbM
    rw [beattyIndex_zero] at hDepth
    omega
  · have hbPosIndex : 0 < b := Nat.pos_of_ne_zero hb0
    have hbOneLe : 1 ≤ b := Nat.succ_le_iff.mpr hbPosIndex
    have hPrevZero : h (b - 1) = 0 :=
      hBefore (b - 1) (by omega)
    have hIdx : (b - 1) + 1 < m := by
      rw [Nat.sub_add_cancel hbOneLe]
      exact hbM
    have hStep :=
      A.next_depth_le_add_one (k := b - 1) hIdx
    rw [Nat.sub_add_cancel hbOneLe, hPrevZero] at hStep
    omega

/--
二点の checkpoint 差が rank 差そのものなら、signed depth 差は
signed Beatty excess そのもの。

Nat subtraction の向きを仮定しない exact identity。
-/
theorem depthDifference_int_eq_of_checkpoint_add
    {m : ℕ}
    {h : ℕ → ℕ}
    (A : AdmissibleSturmianProfile m h)
    {k l : ℕ}
    (hkM : k < m)
    (hlM : l < m)
    (_hkl : k ≤ l)
    (hCheckpoint :
      profileCheckpoint h l =
        profileCheckpoint h k + (l - k)) :
    (beattyIndex l : ℤ) - (beattyIndex k : ℤ) =
      ((l - k : ℕ) : ℤ) + ((h l : ℤ) - (h k : ℤ)) := by
  have hDepthK := A.depth_le hkM
  have hDepthL := A.depth_le hlM
  have hZ := congrArg (fun n : ℕ => (n : ℤ)) hCheckpoint
  unfold profileCheckpoint at hZ
  rw [
    Nat.cast_add,
    Nat.cast_sub hDepthL,
    Nat.cast_sub hDepthK
  ] at hZ
  linarith

/--
二点の checkpoint 差が rank 差そのものなら、depth 差は Beatty excess そのもの。

affine checkpoint line から使える SingleCorner 非依存の Nat form。
-/
theorem depthDifference_eq_of_checkpoint_add
    {m : ℕ}
    {h : ℕ → ℕ}
    (A : AdmissibleSturmianProfile m h)
    {k l : ℕ}
    (hkM : k < m)
    (hlM : l < m)
    (hkl : k ≤ l)
    (hMono : h k ≤ h l)
    (hCheckpoint :
      profileCheckpoint h l =
        profileCheckpoint h k + (l - k)) :
    beattyIndex l - beattyIndex k =
      (l - k) + (h l - h k) := by
  have hDepthK := A.depth_le hkM
  have hDepthL := A.depth_le hlM
  unfold profileCheckpoint at hCheckpoint
  omega

end AdmissibleSturmianProfile

end CSTMicro
end Collatz2
