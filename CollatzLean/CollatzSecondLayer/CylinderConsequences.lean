import CollatzLean.CollatzSecondLayer.CylinderUpgradeProof

/-!
# polynomial-small C3 cylinderの終点評価

first-crossingの収縮とaffine定数上界から、cylinder終点を開始値と語長で
直接抑える。Bridge 2の開始値多項式上界を終点へも伝播させる。
-/

namespace CollatzSecondLayer

open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

/--
first-crossing語では、終端で純乗法係数が収縮側に入る。
-/
lemma FirstCrossingCylinder.threePow_length_le_twoPow
    {O : OddOrbit}
    (C : FirstCrossingCylinder O) :
    3 ^ C.word.length ≤ 2 ^ twoSteps C.word := by
  have hlt : C.word.Contracting := by
    change
      (O.segmentWord
        (C.limit.minima.index C.sequenceIndex)
        C.length).Contracting
    exact C.firstCrossing.terminalContracting
  exact Nat.le_of_lt (by
    simpa [ExpWord.Contracting, oddSteps] using hlt)


/--
first-crossing語のアフィン定数は
`word.length * 2^twoSteps(word)`以下である。
-/
lemma FirstCrossingCylinder.affineConst_le_length_mul_twoPow
    {O : OddOrbit}
    (C : FirstCrossingCylinder O) :
    affineConst C.word ≤
      C.word.length * 2 ^ twoSteps C.word := by
  have hthree :
      affineConst C.word ≤
        C.word.length * 3 ^ C.word.length := by
    simpa [FirstCrossingCylinder.word] using
      affineConst_le_length_mul_threePow C.firstCrossing
  exact hthree.trans
    (Nat.mul_le_mul_left
      C.word.length
      C.threePow_length_le_twoPow)

/--
first-crossing cylinderの終点評価を、
正の係数`2^twoSteps(word)`を掛けた形で示す。
-/
lemma FirstCrossingCylinder.scaled_finish_le_start_add_length
    {O : OddOrbit}
    (C : FirstCrossingCylinder O) :
    2 ^ twoSteps C.word * C.finish ≤
      2 ^ twoSteps C.word * (C.start + C.length) := by
  let H := twoSteps C.word
  let p := C.word.length
  have hrun := C.run.realizes
  have hlen :
      C.word.length = C.length := by
    simp [FirstCrossingCylinder.word]
  have hcontract :
      3 ^ p ≤ 2 ^ H := by
    simpa [H, p] using
      C.threePow_length_le_twoPow
  have hB :
      affineConst C.word ≤ p * 2 ^ H := by
    simpa [H, p] using
      C.affineConst_le_length_mul_twoPow
  calc
    2 ^ H * C.finish
        = 3 ^ p * C.start + affineConst C.word := by
            simpa [Realizes, H, p, oddSteps] using hrun
    _ ≤ 2 ^ H * C.start + p * 2 ^ H := by
          exact Nat.add_le_add
            (Nat.mul_le_mul_right C.start hcontract)
            hB
    _ = 2 ^ H * (C.start + C.length) := by
          rw [show p = C.length by
            simpa [p] using hlen]
          ring


/-- first-crossing cylinderの終点は`start+length`以下。 -/
theorem FirstCrossingCylinder.finish_le_start_add_length
    {O : OddOrbit}
    (C : FirstCrossingCylinder O) :
    C.finish ≤ C.start + C.length := by
  exact Nat.le_of_mul_le_mul_left
    C.scaled_finish_le_start_add_length
    (Nat.pow_pos (by omega : 0 < (2 : ℕ)))

/-- canonical C3列の終点も語長に対して一様に多項式小。 -/
theorem C3CylinderSequence.finishes_polynomialSmall
    {O : OddOrbit}
    (S : C3CylinderSequence O) :
    ∃ K A : ℕ,
      ∀ j : ℕ,
        (S.cylinder j).toFirstCrossingCylinder.finish ≤
          K *
            ((S.cylinder j).toFirstCrossingCylinder.length + 1) ^ A := by
  rcases S.polynomialSmall with ⟨K, A, hstart⟩
  refine ⟨K + 1, A + 1, ?_⟩
  intro j
  let C := (S.cylinder j).toFirstCrossingCylinder
  let b := C.length + 1
  have hbpos : 0 < b := by
    dsimp [b]
    omega
  have hpowA : b ^ A ≤ b ^ (A + 1) := by
    exact Nat.pow_le_pow_right hbpos (Nat.le_succ A)
  have hpowOne : b ≤ b ^ (A + 1) := by
    have hone : 1 ≤ A + 1 := by omega
    simpa using Nat.pow_le_pow_right hbpos hone
  have hfinish : C.finish ≤ C.start + C.length :=
    C.finish_le_start_add_length
  have hstartC : C.start ≤ K * b ^ A := by
    simpa [C, b] using hstart j
  calc
    C.finish
        ≤ C.start + C.length := hfinish
    _ ≤ K * b ^ A + C.length :=
      Nat.add_le_add_right hstartC _
    _ ≤ K * b ^ (A + 1) + b ^ (A + 1) := by
      exact Nat.add_le_add
        (Nat.mul_le_mul_left K hpowA)
        (le_trans (by dsimp [b]; omega) hpowOne)
    _ = (K + 1) * b ^ (A + 1) := by ring

end CollatzSecondLayer
