import CollatzLean.Collatz2.CSTMicro.CarryGeometry.BoundaryRespectingRankCellBridge

set_option linter.style.longLine false

/-!
# Sharp first-failure small strip: 3q < m

既存 B first-failure bridge は `q < m` を持つ。
ここでは odd-only FirstCrossing の exact translation identity

  3 B = sum_{k=0}^{m-1} normalizedCutTerm(k)

を使って factor 3 を回収する。

m>1 なら k=0 term は exact に `3^m`、各 `0<k<m` term は proper-prefix expanding により
strict に `3^m` 未満。したがって

  3 B < m * 3^m.

一方 first-failure upper affine equationは

  B = G R + 2^H q,

かつ `3^m < 2^H`。従って

  3q < m.

standard upper length > 2 なら first-passage condition から m>1 も内部で従う。
-/

namespace Collatz2

namespace Word

/-- proper positive cut の normalized term は `3^p` より strict に小さい。 -/
theorem FirstCrossing.normalizedCutTerm_lt_threePow
    {w : Word}
    (hF : FirstCrossing w)
    {k : ℕ}
    (hkPos : 0 < k)
    (hkLt : k < oddSteps w) :
    normalizedCutTerm w k < 3 ^ oddSteps w := by
  have hkLtLen : k < w.length := by
    simpa [oddSteps] using hkLt
  have hExpRaw :=
    (expanding_iff_twoPow_lt_threePow).1
      (hF.properExpanding hkPos hkLtLen)
  have hkLeLen : k ≤ w.length := Nat.le_of_lt hkLtLen
  have hTakeLen : (w.take k).length = k :=
    List.length_take_of_le hkLeLen
  have hExp :
      2 ^ prefixTwoDepth w k < 3 ^ k := by
    simpa [prefixTwoDepth, oddSteps, hTakeLen] using hExpRaw
  have hMul :
      2 ^ prefixTwoDepth w k * 3 ^ (oddSteps w - k) <
        3 ^ k * 3 ^ (oddSteps w - k) :=
    Nat.mul_lt_mul_of_pos_right hExp (by positivity)
  have hsum : k + (oddSteps w - k) = oddSteps w := by
    omega
  unfold normalizedCutTerm
  calc
    2 ^ prefixTwoDepth w k * 3 ^ (oddSteps w - k)
        < 3 ^ k * 3 ^ (oddSteps w - k) := hMul
    _ = 3 ^ oddSteps w := by
      rw [← pow_add, hsum]

/--
`p>1` の FirstCrossing では、normalized cut term の strict budget を
直接総和することで

  3B < p*3^p

を得る。
-/
theorem FirstCrossing.three_mul_affineConst_lt_oddSteps_mul_threePow_of_normalizedCutTerms
    {w : Word}
    (hF : FirstCrossing w)
    (hp : 1 < oddSteps w) :
    3 * affineConst w < oddSteps w * 3 ^ oddSteps w := by
  let p := oddSteps w
  have hpPos : 0 < p := by
    dsimp [p]
    omega
  have hpPredPos : 0 < p - 1 := by
    dsimp [p]
    omega
  have hpEq : p = (p - 1) + 1 := by
    omega
  have hSumEq := sum_normalizedCutTerm_eq_three_mul_affineConst w
  have hTailLe :
      Finset.sum (Finset.range (p - 1))
          (fun j => normalizedCutTerm w (j + 1)) ≤
        (p - 1) * (3 ^ p - 1) := by
    calc
      Finset.sum (Finset.range (p - 1))
          (fun j => normalizedCutTerm w (j + 1))
          ≤
        Finset.sum (Finset.range (p - 1))
          (fun _ => 3 ^ p - 1) := by
            apply Finset.sum_le_sum
            intro j hj
            have hjLt : j < p - 1 := Finset.mem_range.mp hj
            have hkPos : 0 < j + 1 := by
              omega
            have hkLt : j + 1 < p := by
              omega
            have hlt :
                normalizedCutTerm w (j + 1) < 3 ^ p := by
              simpa [p] using
                hF.normalizedCutTerm_lt_threePow
                  hkPos
                  (by simpa [p] using hkLt)
            omega
      _ = (p - 1) * (3 ^ p - 1) := by
        simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
  have hTailLt :
      Finset.sum (Finset.range (p - 1))
          (fun j => normalizedCutTerm w (j + 1)) <
        (p - 1) * 3 ^ p := by
    have hPowPos : 0 < 3 ^ p := by
      positivity
    have hSubLt : 3 ^ p - 1 < 3 ^ p := by
      omega
    have hMulLt :
        (p - 1) * (3 ^ p - 1) <
          (p - 1) * 3 ^ p :=
      (Nat.mul_lt_mul_left hpPredPos).2 hSubLt
    exact lt_of_le_of_lt hTailLe hMulLt
  have hZero :
      normalizedCutTerm w 0 = 3 ^ p := by
    simp [normalizedCutTerm, prefixTwoDepth, p]
  have hFinal :
      3 ^ p +
          Finset.sum (Finset.range (p - 1))
            (fun j => normalizedCutTerm w (j + 1)) <
        p * 3 ^ p := by
    calc
      3 ^ p +
          Finset.sum (Finset.range (p - 1))
            (fun j => normalizedCutTerm w (j + 1))
          <
        3 ^ p + (p - 1) * 3 ^ p :=
          Nat.add_lt_add_left hTailLt _
      _ = ((p - 1) + 1) * 3 ^ p := by
        rw [Nat.add_mul]
        simp [Nat.add_comm]
      _ = p * 3 ^ p := by
        rw [← hpEq]
  rw [← hSumEq]
  rw [show oddSteps w = (p - 1) + 1 by
    simpa [p] using hpEq]
  rw [Finset.sum_range_succ']
  rw [hZero]
  calc
    Finset.sum (Finset.range (p - 1))
          (fun j => normalizedCutTerm w (j + 1)) +
        3 ^ p
        =
      3 ^ p +
        Finset.sum (Finset.range (p - 1))
          (fun j => normalizedCutTerm w (j + 1)) := by
            exact Nat.add_comm _ _
    _ < p * 3 ^ p := hFinal
    _ = ((p - 1) + 1) * 3 ^ ((p - 1) + 1) := by
      rw [← hpEq]

end Word

namespace CSTMicro

namespace FirstFailureEdge

/-- standard upper length >2 なら first-passage odd total は少なくとも2。 -/
theorem one_lt_edge_oddTotal_of_two_lt_upperWord_length
    (F : FirstFailureEdge)
    (hLen : 2 < F.step.edge.upperWord.length) :
    1 < F.step.edge.oddTotal := by
  have hmPos := F.edge_oddTotal_pos
  by_contra hnot
  have hmOne : F.step.edge.oddTotal = 1 := by omega
  have hExp := F.edge_upper_firstPassage.2.1 2 (by omega) hLen
  unfold CoefficientExpandingAt at hExp
  have hCountLe :
      prefixOddCount F.step.edge.upperWord 2 ≤ F.step.edge.oddTotal := by
    calc
      prefixOddCount F.step.edge.upperWord 2
          ≤ oddCount F.step.edge.upperWord :=
        prefixOddCount_le_oddCount _ _
      _ = F.step.edge.oddTotal := F.step.edge.upperWord_oddCount
  rw [hmOne] at hCountLe
  have hPowLe :
      3 ^ prefixOddCount F.step.edge.upperWord 2 ≤ 3 ^ (1 : ℕ) :=
    Nat.pow_le_pow_right (by omega : 0 < (3 : ℕ)) hCountLe
  norm_num at hExp hPowLe
  omega

/--
nontrivial first-failure upper の sharp normalized strip。

  3*q < m.
-/
theorem three_mul_upperNormalizedDefectNat_lt_oddTotal
    (F : FirstFailureEdge)
    (hLen : 2 < F.step.edge.upperWord.length) :
    3 * F.upperNormalizedDefectNat < F.step.edge.oddTotal := by
  let w := F.upperExponentWord
  let m := F.step.edge.oddTotal
  let H := F.step.edge.length
  let q := F.upperNormalizedDefectNat
  have hm : 1 < m := by
    simpa [m] using F.one_lt_edge_oddTotal_of_two_lt_upperWord_length hLen
  have hF : Collatz2.Word.FirstCrossing w := by
    simpa [w] using F.upperExponentWord_firstCrossing
  have hBSharp :
      3 * Collatz2.Word.affineConst w < m * 3 ^ m := by
    have h := hF.three_mul_affineConst_lt_oddSteps_mul_threePow_of_normalizedCutTerms
      (by simpa [w, m] using hm)
    simpa [w, m] using h
  have hAffine :=
    F.upperExponentWord_affineConst_eq_gap_mul_R_add_twoPow_mul_upperQ
  have hMqLeB :
      2 ^ Collatz2.Word.twoSteps w * q ≤ Collatz2.Word.affineConst w := by
    have hEq :
        Collatz2.Word.affineConst w =
          Collatz2.Word.terminalGap w * F.step.edge.upperR +
            2 ^ Collatz2.Word.twoSteps w * q := by
      simpa [w, q] using hAffine
    omega
  have hThreeMq :
      3 * (2 ^ Collatz2.Word.twoSteps w * q) < m * 3 ^ m :=
    lt_of_le_of_lt (Nat.mul_le_mul_left 3 hMqLeB) hBSharp
  have hPow : 3 ^ m < 2 ^ Collatz2.Word.twoSteps w := by
    have h :=
      (Collatz2.Word.contracting_iff_threePow_lt_twoPow).1
        hF.terminalContracting
    simpa [w, m] using h
  have hMMul :
      m * 3 ^ m < m * 2 ^ Collatz2.Word.twoSteps w :=
    (Nat.mul_lt_mul_left (by omega : 0 < m)).2 hPow
  have hFinal :
      2 ^ Collatz2.Word.twoSteps w * (3 * q) <
        2 ^ Collatz2.Word.twoSteps w * m := by
    calc
      2 ^ Collatz2.Word.twoSteps w * (3 * q)
          = 3 * (2 ^ Collatz2.Word.twoSteps w * q) := by ring
      _ < m * 3 ^ m := hThreeMq
      _ < m * 2 ^ Collatz2.Word.twoSteps w := hMMul
      _ = 2 ^ Collatz2.Word.twoSteps w * m := by ring
  have hTwoPos : 0 < 2 ^ Collatz2.Word.twoSteps w := by positivity
  exact (Nat.mul_lt_mul_left hTwoPos).mp hFinal

/-- odd-only oddSteps で書いた同じ sharp strip。 -/
theorem three_mul_upperNormalizedDefectNat_lt_oddSteps
    (F : FirstFailureEdge)
    (hLen : 2 < F.step.edge.upperWord.length) :
    3 * F.upperNormalizedDefectNat < Collatz2.Word.oddSteps F.upperExponentWord := by
  rw [F.upperExponentWord_oddSteps]
  exact F.three_mul_upperNormalizedDefectNat_lt_oddTotal hLen

end FirstFailureEdge

namespace ExternalArithmetic
namespace MinimalActualABObstructionPacket

/-- minimal actual nontrivial B の natural q も sharp に `3q < m`。 -/
theorem three_mul_actualQ_lt_oddCount
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L) :
    3 * M.actual.q < oddCount M.word := by
  let F := M.actual.firstFailureEdge
  have hUpperLen : 2 < F.step.edge.upperWord.length := by
    calc
      2 < M.word.length := by simpa [M.word_length_eq] using hL
      _ = F.step.edge.upperWord.length := by
        have hEq := M.failureStep_upperWord_eq_word
        change F.step.edge.upperWord = M.word at hEq
        rw [hEq]
  have hSharp := F.three_mul_upperNormalizedDefectNat_lt_oddTotal hUpperLen
  have hQ : M.actual.q = F.upperNormalizedDefectNat := by
    simpa [F, ActualABObstructionPacket.firstFailureEdge] using M.actual.q_eq_canonical
  have hOdd : oddCount M.word = F.step.edge.oddTotal := by
    have hEq := M.failureStep_upperWord_eq_word
    change F.step.edge.upperWord = M.word at hEq
    rw [← hEq]
    exact F.step.edge.upperWord_oddCount
  rw [hQ, hOdd]
  exact hSharp

end MinimalActualABObstructionPacket
end ExternalArithmetic

end CSTMicro
end Collatz2
