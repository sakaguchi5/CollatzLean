import CollatzLean.Collatz.FiniteOrbit.Runs

/-!
# finite wordからactual odd runへの復元

有限指数語のaffine実現式にvalid性と奇数終点を加えると、
各一段がactual odd-only stepである`Runs`へ復元できる。
また連結語のactual runはprefix/suffixへ分割できる。
-/

namespace Collatz
namespace Word
namespace Runs

/-- actual runの終点が奇数なら開始値も奇数。 -/
theorem start_odd
    {w : Collatz.Word} {x y : ℕ}
    (h : Runs w x y) (hy : Odd y) : Odd x := by
  cases h with
  | nil x =>
      simpa using hy
  | @cons e w x z y he hstep hz htail =>
      obtain ⟨k, hxEven | hxOdd⟩ := x.even_or_odd'
      · obtain ⟨s, hs⟩ : ∃ s : ℕ, e = s + 1 :=
          ⟨e - 1, by omega⟩
        have hbad : 2 * (2 ^ s * z) = 6 * k + 1 := by
          calc
            2 * (2 ^ s * z) = 2 ^ e * z := by
              rw [hs, pow_succ]
              ring
            _ = 3 * x + 1 := hstep
            _ = 6 * k + 1 := by
              rw [hxEven]
              ring
        omega
      · exact ⟨k, hxOdd⟩

/-- 連結語のactual runをprefixとsuffixへ分割する。 -/
theorem split_append
    {u v : Collatz.Word} {x z : ℕ}
    (h : Runs (u ++ v) x z) :
    ∃ y : ℕ, Runs u x y ∧ Runs v y z := by
  induction u generalizing x with
  | nil =>
      refine ⟨x, Runs.nil x, ?_⟩
      simpa using h
  | cons e u ih =>
      change Runs (e :: (u ++ v)) x z at h
      cases h with
      | cons he hstep hodd htail =>
          obtain ⟨y, hprefix, hsuffix⟩ := ih htail
          exact ⟨y, Runs.cons he hstep hodd hprefix, hsuffix⟩

end Runs

/--
validな有限語のaffine実現で終点が奇数なら、
各指定指数が実際の完全2進指数となるactual odd runへ復元できる。
-/
theorem Valid.runs_of_realizes
    {w : Collatz.Word} {x y : ℕ}
    (hvalid : w.Valid)
    (hreal : w.Realizes x y)
    (hy : Odd y) :
    Runs w x y := by
  induction w generalizing x y with
  | nil =>
      have hxy : y = x := by
        simpa [Realizes, oddSteps, twoSteps, affineConst] using hreal
      subst y
      exact Runs.nil x
  | cons e w ih =>
      have he : 0 < e := hvalid e (by simp)
      have htailValid : Valid w := by
        intro a ha
        exact hvalid a (by simp [ha])
      have hnormalized :
          2 ^ e * (2 ^ twoSteps w * y) =
            3 ^ oddSteps w * (3 * x + 1) +
              2 ^ e * affineConst w := by
        unfold Realizes at hreal
        simp only [twoSteps_cons, oddSteps_cons, affineConst_cons] at hreal
        calc
          2 ^ e * (2 ^ twoSteps w * y)
              = 2 ^ (e + twoSteps w) * y := by
                  rw [pow_add]
                  ring
          _ = 3 ^ (oddSteps w + 1) * x +
                (3 ^ oddSteps w + 2 ^ e * affineConst w) := hreal
          _ = 3 ^ oddSteps w * (3 * x + 1) +
                2 ^ e * affineConst w := by
                  rw [pow_succ]
                  ring
      have hpowPos : 0 < 2 ^ e := Nat.pow_pos (by omega)
      have hscaledAffine :
          2 ^ e * affineConst w ≤
            2 ^ e * (2 ^ twoSteps w * y) := by
        rw [hnormalized]
        omega
      have haffine : affineConst w ≤ 2 ^ twoSteps w * y := by
        by_contra hnot
        have hlt : 2 ^ twoSteps w * y < affineConst w :=
          Nat.lt_of_not_ge hnot
        have hmul := (Nat.mul_lt_mul_left hpowPos).2 hlt
        omega
      let q := 2 ^ twoSteps w * y - affineConst w
      have hq : q + affineConst w = 2 ^ twoSteps w * y := by
        dsimp [q]
        exact Nat.sub_add_cancel haffine
      have hproduct :
          3 ^ oddSteps w * (3 * x + 1) = 2 ^ e * q := by
        have hsum :
            3 ^ oddSteps w * (3 * x + 1) +
                2 ^ e * affineConst w =
              2 ^ e * q + 2 ^ e * affineConst w := by
          calc
            3 ^ oddSteps w * (3 * x + 1) +
                2 ^ e * affineConst w
                = 2 ^ e * (2 ^ twoSteps w * y) := hnormalized.symm
            _ = 2 ^ e * (q + affineConst w) := by rw [hq]
            _ = 2 ^ e * q + 2 ^ e * affineConst w := by ring
        exact Nat.add_right_cancel hsum
      have hdvdProduct :
          2 ^ e ∣ 3 ^ oddSteps w * (3 * x + 1) :=
        ⟨q, hproduct⟩
      have hcoprime : Nat.Coprime (2 ^ e) (3 ^ oddSteps w) := by
        exact Nat.Coprime.pow e (oddSteps w) (by decide : Nat.Coprime 2 3)
      have hdvd : 2 ^ e ∣ 3 * x + 1 :=
        hcoprime.dvd_of_dvd_mul_left hdvdProduct
      obtain ⟨z, hz⟩ := hdvd
      have htailRealizes : Realizes w z y := by
        unfold Realizes
        have hscaled :
            2 ^ e * (2 ^ twoSteps w * y) =
              2 ^ e * (3 ^ oddSteps w * z + affineConst w) := by
          calc
            2 ^ e * (2 ^ twoSteps w * y)
                = 3 ^ oddSteps w * (3 * x + 1) +
                    2 ^ e * affineConst w := hnormalized
            _ = 3 ^ oddSteps w * (2 ^ e * z) +
                    2 ^ e * affineConst w := by rw [hz]
            _ = 2 ^ e * (3 ^ oddSteps w * z + affineConst w) := by ring
        exact Nat.mul_left_cancel hpowPos hscaled
      have htailRuns : Runs w z y :=
        ih htailValid htailRealizes hy
      have hzOdd : Odd z := htailRuns.start_odd hy
      exact Runs.cons he hz.symm hzOdd htailRuns

end Word
end Collatz
