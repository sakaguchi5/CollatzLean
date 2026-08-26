import CollatzLean.Collatz2.RecordFerrers.Record.CarryStatistics
import CollatzLean.Collatz2.RecordFerrers.Deformation.BlockPermutation
import CollatzLean.Collatz2.RecordFerrers.Factorization.InitialAnchorFirstCrossing

/-!
# Record–Ferrers RF-A+6: arbitrary interior block permutation

adjacent interior swap law を `List.Perm` 全体へ持ち上げる。
terminal block は最後に固定し、その手前の interior blocks の任意 permutation が
full carry condition と whole minimal FirstCrossing assembly を保存することを示す。

さらに affine translation の adjacent swap law を prefix / suffix context 付きへ持ち上げる。
-/

namespace Collatz2
namespace RecordFerrers

open Word

namespace Skeleton

/-- nonempty tail の前にある先頭二 block は full carry condition のまま交換できる。 -/
theorem carryCondition_swap_first_two_of_nonempty_tail
    (start r s : ℕ)
    (tail : List ℕ)
    (hTail : tail ≠ [])
    (hCarry : carryConditionFrom start (r :: s :: tail)) :
    carryConditionFrom start (s :: r :: tail) := by
  cases tail with
  | nil =>
      exact False.elim (hTail rfl)
  | cons t ts =>
      exact carryCondition_swap_first_two_of_three start r s t ts hCarry

/--
terminal length `terminal` を最後に固定したとき、
その手前の length list の任意 permutation は full carry condition を保存する。
-/
theorem carryCondition_append_singleton_perm
    (start terminal : ℕ)
    {rs ss : List ℕ}
    (hPerm : rs.Perm ss)
    (hCarry : carryConditionFrom start (rs ++ [terminal])) :
    carryConditionFrom start (ss ++ [terminal]) := by
  induction hPerm generalizing start with
  | nil =>
      simpa using hCarry
  | @cons r rs ss hPerm ih =>
      have hTailRs : rs ++ [terminal] ≠ [] := by simp
      have hTailSs : ss ++ [terminal] ≠ [] := by simp
      have hHeadTail :
          criticalCarry start r = 1 ∧
            carryConditionFrom (start + r) (rs ++ [terminal]) := by
        cases hRs : rs ++ [terminal] with
        | nil => exact False.elim (hTailRs hRs)
        | cons s tail =>
            simpa [hRs] using hCarry
      have hTailCarry :
          carryConditionFrom (start + r) (ss ++ [terminal]) :=
        ih (start := start + r) hHeadTail.2
      cases hSs : ss ++ [terminal] with
      | nil =>
          exact False.elim (hTailSs hSs)
      | cons s tail =>
          change
            carryConditionFrom start
              (r :: (ss ++ [terminal]))
          rw [hSs]
          change
            criticalCarry start r = 1 ∧
              carryConditionFrom (start + r) (s :: tail)
          exact
            ⟨hHeadTail.1, by
              simpa [hSs] using hTailCarry⟩
  | @swap r s rs =>
      have hTail : rs ++ [terminal] ≠ [] := by simp
      simpa only [List.cons_append] using
        carryCondition_swap_first_two_of_nonempty_tail
          start s r (rs ++ [terminal]) hTail hCarry
  | @trans rs ss ts hRS hST ihRS ihST =>
      exact ihST (start := start) (ihRS (start := start) hCarry)

end Skeleton

/-- minimal-block property is preserved under list permutation. -/
theorem minimalBlocks_of_perm
    {bs cs : List Word}
    (hPerm : bs.Perm cs)
    (hMinimal : ∀ b ∈ bs, MinimalBlock b) :
    ∀ c ∈ cs, MinimalBlock c := by
  intro c hc
  apply hMinimal c
  rw [hPerm.mem_iff]
  exact hc

/--
terminal block を固定した interior block permutation は、
critical-roof anchor から組み立てた whole minimal FirstCrossing word を再び与える。
-/
theorem minimalBlock_of_permuted_interior
    (anchor terminal : Word)
    {bs cs : List Word}
    (hPerm : bs.Perm cs)
    (A : CriticalRoofPrefix anchor)
    (hMinimal : ∀ b ∈ bs, MinimalBlock b)
    (hTerminalMinimal : MinimalBlock terminal)
    (hCarry :
      Skeleton.carryConditionFrom
        (oddSteps anchor)
        ((bs ++ [terminal]).map oddSteps)) :
    MinimalBlock (anchor ++ (cs ++ [terminal]).flatten) := by
  have hLengthPerm :
      (bs.map oddSteps).Perm (cs.map oddSteps) :=
    List.Perm.map oddSteps hPerm
  have hCarry' :
      Skeleton.carryConditionFrom
        (oddSteps anchor)
        ((cs ++ [terminal]).map oddSteps) := by
    have hCarry0 :
        Skeleton.carryConditionFrom
          (oddSteps anchor)
          (bs.map oddSteps ++ [oddSteps terminal]) := by
      simpa [List.map_append] using hCarry
    have hPermuted :=
      Skeleton.carryCondition_append_singleton_perm
        (oddSteps anchor) (oddSteps terminal) hLengthPerm hCarry0
    simpa [List.map_append] using hPermuted
  have hMinimalCs : ∀ c ∈ cs, MinimalBlock c :=
    minimalBlocks_of_perm hPerm hMinimal
  have hAllMinimal :
      ∀ b ∈ cs ++ [terminal], MinimalBlock b := by
    intro b hb
    simp only [List.mem_append, List.mem_singleton] at hb
    rcases hb with hb | rfl
    · exact hMinimalCs b hb
    · exact hTerminalMinimal
  exact minimalBlock_of_blocks_carryCondition
    anchor (cs ++ [terminal]) A hAllMinimal hCarry'

/-- adjacent block swap を支配する signed exchange determinant。 -/
def blockExchangeDeterminant (u v : Word) : ℤ :=
  (affineConst u : ℤ) * coefficientGap (oddSteps v) (twoSteps v) -
    (affineConst v : ℤ) * coefficientGap (oddSteps u) (twoSteps u)

/-- local adjacent swap difference は exchange determinant そのもの。 -/
theorem affineConst_swap_two_eq_exchangeDeterminant
    (u v : Word) :
    (affineConst (v ++ u) : ℤ) - (affineConst (u ++ v) : ℤ) =
      blockExchangeDeterminant u v := by
  exact affineConst_swap_two u v

/--
任意 left / suffix context の中で adjacent block を交換したときの affine difference。
外側 context は positive factor `2^H_left * 3^p_suffix` として完全に分離する。
-/
theorem affineConst_swap_two_in_context
    (leftCtx u v suffix : Word) :
    (affineConst ((leftCtx ++ (v ++ u)) ++ suffix) : ℤ) -
        (affineConst ((leftCtx ++ (u ++ v)) ++ suffix) : ℤ) =
      ((2 : ℤ) ^ twoSteps leftCtx) *
        ((3 : ℤ) ^ oddSteps suffix) *
          blockExchangeDeterminant u v := by
  have hOuterVU :
      (affineConst ((leftCtx ++ (v ++ u)) ++ suffix) : ℤ) =
        ((3 : ℤ) ^ oddSteps suffix) *
            (affineConst (leftCtx ++ (v ++ u)) : ℤ) +
          ((2 : ℤ) ^ twoSteps (leftCtx ++ (v ++ u))) *
            (affineConst suffix : ℤ) := by
    exact_mod_cast affineConst_append (leftCtx ++ (v ++ u)) suffix
  have hOuterUV :
      (affineConst ((leftCtx ++ (u ++ v)) ++ suffix) : ℤ) =
        ((3 : ℤ) ^ oddSteps suffix) *
            (affineConst (leftCtx ++ (u ++ v)) : ℤ) +
          ((2 : ℤ) ^ twoSteps (leftCtx ++ (u ++ v))) *
            (affineConst suffix : ℤ) := by
    exact_mod_cast affineConst_append (leftCtx ++ (u ++ v)) suffix
  have hInnerVU :
      (affineConst (leftCtx ++ (v ++ u)) : ℤ) =
        ((3 : ℤ) ^ oddSteps (v ++ u)) *
            (affineConst leftCtx : ℤ) +
          ((2 : ℤ) ^ twoSteps leftCtx) *
            (affineConst (v ++ u) : ℤ) := by
    exact_mod_cast affineConst_append leftCtx (v ++ u)
  have hInnerUV :
      (affineConst (leftCtx ++ (u ++ v)) : ℤ) =
        ((3 : ℤ) ^ oddSteps (u ++ v)) *
            (affineConst leftCtx : ℤ) +
          ((2 : ℤ) ^ twoSteps leftCtx) *
            (affineConst (u ++ v) : ℤ) := by
    exact_mod_cast affineConst_append leftCtx (u ++ v)
  have hContext :
      (affineConst ((leftCtx ++ (v ++ u)) ++ suffix) : ℤ) -
          (affineConst ((leftCtx ++ (u ++ v)) ++ suffix) : ℤ) =
        ((2 : ℤ) ^ twoSteps leftCtx) *
          ((3 : ℤ) ^ oddSteps suffix) *
            ((affineConst (v ++ u) : ℤ) -
              (affineConst (u ++ v) : ℤ)) := by
    rw [hOuterVU, hOuterUV, hInnerVU, hInnerUV]
    simp only [oddSteps_append, twoSteps_append]
    have hOdd :
        oddSteps v + oddSteps u =
          oddSteps u + oddSteps v := by
      omega
    have hTwo :
        twoSteps v + twoSteps u =
          twoSteps u + twoSteps v := by
      omega
    rw [hOdd, hTwo]
    ring
  rw [hContext, affineConst_swap_two_eq_exchangeDeterminant u v]

end RecordFerrers
end Collatz2
