import CollatzLean.Collatz.Word.Basic
import CollatzLean.Collatz.TwoAdic.Factorization

/-!
# affine constant の先頭指数 decoder

valid 非空 tail を持つ `e :: w` では

  `affineConst (e :: w) - 3 ^ oddSteps w = 2^e * affineConst w`

かつ `affineConst w` は奇数。
従って左辺の exact 2進深さは先頭指数 `e` そのものである。
-/

namespace Collatz
namespace Word

/-- valid 非空語の affine constant は奇数。 -/
theorem Valid.affineConst_odd_of_nonempty
    {w : Collatz.Word}
    (hvalid : Valid w)
    (hne : w ≠ []) :
    Odd (affineConst w) := by
  cases w with
  | nil => contradiction
  | cons e w =>
      have he : 0 < e := hvalid e (by simp)
      obtain ⟨r, hr⟩ : ∃ r : ℕ, e = r + 1 :=
        ⟨e - 1, by omega⟩
      have hthree : Odd (3 ^ oddSteps w) :=
        (show Odd (3 : ℕ) by decide).pow
      rcases hthree with ⟨a, ha⟩
      refine ⟨a + 2 ^ r * affineConst w, ?_⟩
      rw [affineConst_cons, hr, pow_succ, ha]
      ring

/-- cons affine constant から head term を引いた差。 -/
theorem affineConst_cons_sub_head
    (e : ℕ) (w : Collatz.Word) :
    affineConst (e :: w) - 3 ^ oddSteps w =
      2 ^ e * affineConst w := by
  simp [affineConst_cons]

/--
valid 非空 tail を持つ cons 語では、affine head difference の exact 2進指数は head exponent。
-/
theorem Valid.affineHeadDifference_exactFactor
    {e : ℕ} {w : Collatz.Word}
    (hvalid : Valid (e :: w))
    (hwne : w ≠ []) :
    Collatz.TwoAdic.ExactFactor
      (affineConst (e :: w) - 3 ^ oddSteps w)
      e
      (affineConst w) := by
  have htailValid : Valid w := by
    intro a ha
    exact hvalid a (by simp [ha])
  constructor
  · exact affineConst_cons_sub_head e w
  · exact htailValid.affineConst_odd_of_nonempty hwne

/--
同じ affine head difference の二つの valid cons 語では、tail が非空なら先頭指数は一意。
これは affine decoder の一段版。
-/
theorem valid_cons_headExponent_unique
    {e f : ℕ} {u v : Collatz.Word}
    (huValid : Valid (e :: u))
    (hvValid : Valid (f :: v))
    (huNe : u ≠ [])
    (hvNe : v ≠ [])
    (hLength : oddSteps u = oddSteps v)
    (hAffine : affineConst (e :: u) = affineConst (f :: v)) :
    e = f := by
  have hdiff :
      affineConst (e :: u) - 3 ^ oddSteps u =
        affineConst (f :: v) - 3 ^ oddSteps v := by
    rw [hAffine, hLength]
  have hE := huValid.affineHeadDifference_exactFactor huNe
  have hF := hvValid.affineHeadDifference_exactFactor hvNe
  rw [hdiff] at hE
  exact Collatz.TwoAdic.exponent_unique hE hF


/--
valid 有限語は `(oddSteps, twoSteps, affineConst)` で一意に決まる。
各段で `affineHeadDifference_exactFactor` が先頭指数を強制するため、
同じ三つ組を持つ二つの valid word は一致する。
-/
theorem valid_word_unique_of_oddSteps_twoSteps_affineConst
    {u v : Collatz.Word}
    (huValid : Valid u)
    (hvValid : Valid v)
    (hLength : oddSteps u = oddSteps v)
    (hExponent : twoSteps u = twoSteps v)
    (hAffine : affineConst u = affineConst v) :
    u = v := by
  induction u generalizing v with
  | nil =>
      cases v with
      | nil => rfl
      | cons f v =>
          simp [oddSteps] at hLength
  | cons e u ih =>
      cases v with
      | nil =>
          simp [oddSteps] at hLength
      | cons f v =>
          have hTailLength : oddSteps u = oddSteps v := by
            simpa using hLength
          have huTailValid : Valid u := by
            intro a ha
            exact huValid a (by simp [ha])
          have hvTailValid : Valid v := by
            intro a ha
            exact hvValid a (by simp [ha])
          cases u with
          | nil =>
              cases v with
              | nil =>
                  have hef : e = f := by
                    simp only [twoSteps_cons, twoSteps_nil] at hExponent
                    omega
                  subst f
                  rfl
              | cons b v =>
                  simp [oddSteps] at hTailLength
          | cons a u =>
              cases v with
              | nil =>
                  simp [oddSteps] at hTailLength
              | cons b v =>
                  have huNe : (a :: u) ≠ [] := by simp
                  have hvNe : (b :: v) ≠ [] := by simp
                  have hef : e = f :=
                    valid_cons_headExponent_unique
                      huValid hvValid huNe hvNe hTailLength hAffine
                  subst f
                  have hTailExponent :
                      twoSteps (a :: u) = twoSteps (b :: v) := by
                    have h :
                        e + twoSteps (a :: u) =
                          e + twoSteps (b :: v) := by
                      simpa only [twoSteps_cons] using hExponent
                    exact Nat.add_left_cancel h
                  have hTailAffine :
                      affineConst (a :: u) = affineConst (b :: v) := by
                    simp only [affineConst_cons] at hAffine
                    rw [hTailLength] at hAffine
                    have hmul :
                        2 ^ e * affineConst (a :: u) =
                          2 ^ e * affineConst (b :: v) :=
                      Nat.add_left_cancel hAffine
                    exact Nat.mul_left_cancel
                      (Nat.pow_pos (by omega : 0 < (2 : ℕ))) hmul
                  have htail :=
                    ih huTailValid hvTailValid
                      hTailLength hTailExponent hTailAffine
                  rw [htail]

end Word
end Collatz
