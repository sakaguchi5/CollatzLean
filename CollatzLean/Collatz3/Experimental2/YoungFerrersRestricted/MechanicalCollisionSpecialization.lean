import CollatzLean.Collatz3.Experimental2.YoungFerrersRestricted.CollisionArithmetic
import CollatzLean.Collatz3.Experimental2.GenericRecordFerrers.IrrationalRotationRoof

/-!
# Collatz3 Experimental2: collision 算術の無理回転特殊化

F9--F10 で得た rank-drop / collision 算術を、任意の無理回転
`α ∈ (0,1)` の lifted roof

`β(n) = n + floor(n α)`

へ特殊化する。

整数線形成分 `n` は rank drop 内で相殺されるため、各 block の縦落差は
fractional slope `α` の floor data だけで書ける。

このファイルは `Experimental2` 内で閉じ、Collatz 固有の
`log₂(3/2)` 特殊化は Bridge 層へ分離する。
-/

namespace Collatz3
namespace Experimental2
namespace GenericRecordFerrers

/--
任意の lifted irrational-rotation roof の rank drop の floor 公式。
無理性自体はこの代数恒等式には不要で、roof の concrete formula だけを使う。
-/
theorem rankDropInt_irrationalRotationRoof_eq_floorFormula
    (α : ℝ)
    (m r : ℕ) :
    rankDropInt (irrationalRotationRoof α) m r =
      (m : ℤ) * (⌊(r : ℝ) * α⌋₊ : ℤ) -
        (r : ℤ) * (⌊(m : ℝ) * α⌋₊ : ℤ) +
          (m : ℤ) - (r : ℤ) := by
  rw [rankDropInt_eq_roofFormula]
  simp only [irrationalRotationRoof_eq]
  push_cast
  ring

/--
rank drop は終端 critical vector と block critical vector の determinant そのもの。
Ostrowski / continued-fraction 側との接続に使いやすい形を公開する。
-/
theorem rankDropInt_eq_criticalDeterminant
    (β : ℕ → ℕ)
    (m r : ℕ) :
    rankDropInt β m r =
      (m : ℤ) * (criticalDepth β r : ℤ) -
        (r : ℤ) * (criticalDepth β m : ℤ) := by
  unfold rankDropInt
  ring

/-- 無理回転 roof の一 block rank drop を floor data だけで読む summand。 -/
noncomputable def rotationRankDropSummand
    (α : ℝ)
    (m r : ℕ) : ℤ :=
  (m : ℤ) * (⌊(r : ℝ) * α⌋₊ : ℤ) -
    (r : ℤ) * (⌊(m : ℝ) * α⌋₊ : ℤ) +
      (m : ℤ) - (r : ℤ)

/-- rotation summand は一般 rank drop と exact に一致する。 -/
theorem rotationRankDropSummand_eq_rankDropInt
    (α : ℝ)
    (m r : ℕ) :
    rotationRankDropSummand α m r =
      rankDropInt (irrationalRotationRoof α) m r := by
  exact (rankDropInt_irrationalRotationRoof_eq_floorFormula α m r).symm

/-- rotation roof の rank-drop list sum も summand の通常の和になる。 -/
theorem rankDropIntSum_irrationalRotationRoof_eq_sum_rotationSummand
    (α : ℝ)
    (m : ℕ) :
    ∀ rs : List ℕ,
      rankDropIntSum (irrationalRotationRoof α) m rs =
        (rs.map (rotationRankDropSummand α m)).sum
  | [] => by rfl
  | r :: rs => by
      simp only [rankDropIntSum, List.map_cons, List.sum_cons]
      rw [← rotationRankDropSummand_eq_rankDropInt α m r]
      rw [rankDropIntSum_irrationalRotationRoof_eq_sum_rotationSummand α m rs]

namespace RecordFerrers

/--
任意無理回転 RecordFerrers の rank-drop boundary は、
reverse canonical suffix 上の rotation floor summand の和として exact に書ける。
-/
theorem rankDropHeightBoundaryAt_exists_rotationFloorEquation
    {α : ℝ}
    {m t : ℕ}
    (R : RecordFerrers (irrationalRotationRoof α) m)
    (hB : R.rankDropHeightBoundaryAt t) :
    ∃ pre suf : List ℕ,
      (canonicalRecordLengths (irrationalRotationRoof α) m R.height).reverse = pre ++ suf ∧
        pre ≠ [] ∧
          (t : ℤ) = (pre.map (rotationRankDropSummand α m)).sum := by
  rcases R.rankDropHeightBoundaryAt_exists_rankDropIntSum hB with
    ⟨pre, suf, hSplit, hNonempty, hEq⟩
  refine ⟨pre, suf, hSplit, hNonempty, ?_⟩
  rw [hEq]
  exact rankDropIntSum_irrationalRotationRoof_eq_sum_rotationSummand α m pre

/--
任意無理回転の canonical collision を、左 prefix width と右 rotation-floor suffix sum の
同一 level equation として明示する。
-/
theorem hasCanonicalBoundaryCollision_exists_rotationFloorEquation
    {α : ℝ}
    {m t : ℕ}
    (R : RecordFerrers (irrationalRotationRoof α) m)
    (hC : R.HasCanonicalBoundaryCollision t) :
    ∃ pre preRest revTail revRest : List ℕ,
      canonicalRecordLengths (irrationalRotationRoof α) m R.height = pre ++ preRest ∧
        pre ≠ [] ∧
        (canonicalRecordLengths (irrationalRotationRoof α) m R.height).reverse =
          revTail ++ revRest ∧
        revTail ≠ [] ∧
        pre.sum = t ∧
        (pre.sum : ℤ) = (revTail.map (rotationRankDropSummand α m)).sum := by
  rcases R.canonicalWidthBoundaryAt_exists_prefixSum hC.1 with
    ⟨pre, preRest, hPreSplit, hPreNonempty, hPreSum⟩
  rcases R.rankDropHeightBoundaryAt_exists_rotationFloorEquation hC.2 with
    ⟨revTail, revRest, hRevSplit, hRevNonempty, hEq⟩
  refine ⟨pre, preRest, revTail, revRest,
    hPreSplit, hPreNonempty, hRevSplit, hRevNonempty, hPreSum, ?_⟩
  have hPreSumZ : (pre.sum : ℤ) = (t : ℤ) := by
    exact_mod_cast hPreSum
  rw [hPreSumZ]
  exact hEq

end RecordFerrers
end GenericRecordFerrers
end Experimental2
end Collatz3
