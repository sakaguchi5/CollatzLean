import CollatzLean.Collatz.Canonical.PrependOneCoreZeroObstruction

/-!
# quotient zero obstruction の near-resonance 必要条件

smallest-first paradoxical obstruction では、canonical start `S` より
全 odd boundary が下がらない。

各 odd step

`2^e * y = 3*x + 1`

に `S <= x` を掛け合わせることで、run 全体について

`2^J * S^p < (3*S + 1)^p`

を得る。

これは `j = 0` failure の逃げ道が、`2^J` と `3^p` の
near-resonance に押し込まれることを純自然数不等式として記録する。
-/

namespace Collatz
namespace Word

/--
actual run の全 prefix boundary が `S` 以上なら、step 不等式を掛け合わせて
`2^H * S^p * finish <= (3*S+1)^p * start` を得る。
-/
private theorem Runs.product_bound_of_boundary_floor
    {w : Collatz.Word} {x z S : ℕ}
    (hrun : Runs w x z)
    (hfloor :
      ∀ (u v : Collatz.Word) (y : ℕ),
        w = u ++ v →
        Runs u x y →
        S ≤ y) :
    2 ^ w.twoSteps * S ^ w.oddSteps * z ≤
      (3 * S + 1) ^ w.oddSteps * x := by
  induction hrun generalizing S with
  | nil x =>
      simp [Word.twoSteps, Word.oddSteps]
  | @cons e w x y z he hstep hy htail ih =>
      have hxFloor : S ≤ x := by
        apply hfloor [] (e :: w) x
        · simp
        · exact Runs.nil x
      have hstepBound :
          2 ^ e * S * y ≤ (3 * S + 1) * x := by
        calc
          2 ^ e * S * y = S * (2 ^ e * y) := by ring
          _ = S * (3 * x + 1) := by rw [hstep]
          _ ≤ (3 * S + 1) * x := by
            nlinarith
      have htailFloor :
          ∀ (u v : Collatz.Word) (q : ℕ),
            w = u ++ v →
            Runs u y q →
            S ≤ q := by
        intro u v q huv hrunu
        have hhead : Runs ([e] : Collatz.Word) x y :=
          Runs.cons he hstep hy (Runs.nil y)
        have hpref :
            Runs (([e] : Collatz.Word) ++ u) x q :=
          hhead.append hrunu
        apply hfloor (([e] : Collatz.Word) ++ u) v q
        · simp [huv]
        · exact hpref
      have htailBound := ih htailFloor
      simp only [Word.twoSteps_cons, Word.oddSteps_cons]
      calc
        2 ^ (e + w.twoSteps) * S ^ (w.oddSteps + 1) * z
            = (2 ^ e * S) *
                (2 ^ w.twoSteps * S ^ w.oddSteps * z) := by
                  rw [pow_add, pow_succ]
                  ring
        _ ≤ (2 ^ e * S) *
              ((3 * S + 1) ^ w.oddSteps * y) := by
                exact Nat.mul_le_mul_left _ htailBound
        _ = (3 * S + 1) ^ w.oddSteps *
              (2 ^ e * S * y) := by ring
        _ ≤ (3 * S + 1) ^ w.oddSteps *
              ((3 * S + 1) * x) := by
                exact Nat.mul_le_mul_left _ hstepBound
        _ = (3 * S + 1) ^ (w.oddSteps + 1) * x := by
              rw [pow_succ]
              ring

/--
smallest-first paradoxical exact obstruction は near-resonance 整数不等式

`2^J * S^p < (3*S + 1)^p`

を必ず満たす。
-/
theorem SmallestFirstParadoxicalExactObstruction.nearResonance
    {w : Collatz.Word}
    (O : SmallestFirstParadoxicalExactObstruction w) :
    2 ^ w.twoSteps * w.canonicalStart ^ w.oddSteps <
      (3 * w.canonicalStart + 1) ^ w.oddSteps := by
  let S := w.canonicalStart
  let T := w.canonicalEnd
  have hrun : Runs w S T := by
    simpa [S, T] using O.valid.canonicalRuns
  have hStartOdd : Odd S := by
    dsimp [S]
    exact O.valid.canonicalRuns.start_odd (canonicalEnd_odd w)
  have hSpos : 0 < S := by
    rcases hStartOdd with ⟨a, ha⟩
    omega
  have hfloor :
      ∀ (u v : Collatz.Word) (y : ℕ),
        w = u ++ v →
        Runs u S y →
        S ≤ y := by
    intro u v y hdecomp hprefix
    by_cases hu : u = []
    · subst u
      cases hprefix
      exact le_rfl
    · by_cases hv : v = []
      · subst v
        have huw : u = w := by
          simpa using hdecomp.symm
        have hprefixReal : w.Realizes S y := by
          rw [← huw]
          exact hprefix.realizes
        have hcanonicalReal : w.Realizes S T := by
          simpa [S, T] using canonicalEnd_realizes w
        have hyLeT : y ≤ T :=
          hprefixReal.finish_mono hcanonicalReal le_rfl
        have hTLeY : T ≤ y :=
          hcanonicalReal.finish_mono hprefixReal le_rfl
        have hyT : y = T := by omega
        rw [hyT]
        exact O.positiveReturn.le
      · have huPos : 0 < u.length :=
          List.length_pos_of_ne_nil hu
        have hvPos : 0 < v.length :=
          List.length_pos_of_ne_nil hv
        have huLt : u.length < w.length := by
          rw [hdecomp, List.length_append]
          omega
        have htake : w.take u.length = u := by
          rw [hdecomp]
          simp
        have hrunTake : Runs (w.take u.length) S y := by
          rw [htake]
          exact hprefix
        exact
          (O.properBoundaryAboveStart
            u.length y huPos huLt hrunTake).le
  have hproduct :
      2 ^ w.twoSteps * S ^ w.oddSteps * T ≤
        (3 * S + 1) ^ w.oddSteps * S :=
    Runs.product_bound_of_boundary_floor hrun hfloor
  have hApos :
      0 < 2 ^ w.twoSteps * S ^ w.oddSteps := by
    exact Nat.mul_pos
      (Nat.pow_pos (by omega))
      (Nat.pow_pos hSpos)
  have hST : S < T := by
    simpa [S, T] using O.positiveReturn
  have hstrictScaled :
      (2 ^ w.twoSteps * S ^ w.oddSteps) * S <
        (3 * S + 1) ^ w.oddSteps * S := by
    have hleft :
        (2 ^ w.twoSteps * S ^ w.oddSteps) * S <
          (2 ^ w.twoSteps * S ^ w.oddSteps) * T :=
      (Nat.mul_lt_mul_left hApos).2 hST
    exact lt_of_lt_of_le hleft hproduct
  have hnear :
      2 ^ w.twoSteps * S ^ w.oddSteps <
        (3 * S + 1) ^ w.oddSteps :=
    (Nat.mul_lt_mul_right hSpos).1 hstrictScaled
  simpa [S] using hnear

/-- prepend-one quotient zero failure packet から near-resonance 条件を直接得る。 -/
theorem PrependOneZeroFailureObstruction.nearResonance
    {v : Collatz.Word} {boundary : ℕ}
    (O : PrependOneZeroFailureObstruction v boundary) :
    2 ^ twoSteps (1 :: v)*
        canonicalStart (1 :: v) ^ oddSteps (1 :: v)<
      (3 * canonicalStart (1 :: v) + 1) ^ oddSteps (1 :: v):=
  O.paradoxical.nearResonance

end Word
end Collatz
