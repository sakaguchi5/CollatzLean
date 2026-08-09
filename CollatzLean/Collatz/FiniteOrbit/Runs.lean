import CollatzLean.Collatz.Word.Affine

/-!
# odd-only有限実行

`Runs`本体をcanonical residueから分離する。
-/

namespace Collatz
namespace Word

/-- 正の指数語を順に実行するodd-only有限軌道。 -/
inductive Runs : Collatz.Word → ℕ → ℕ → Prop
  | nil (x : ℕ) : Runs [] x x
  | cons {e : ℕ} {w : Collatz.Word} {x y z : ℕ}
      (positive : 0 < e)
      (step : 2 ^ e * y = 3 * x + 1)
      (oddNext : Odd y)
      (tail : Runs w y z) : Runs (e :: w) x z

namespace Runs

/-- actual runのwordはvalid。 -/
theorem valid {w : Collatz.Word} {x z : ℕ} (h : Runs w x z) : w.Valid := by
  induction h with
  | nil x => simp [Valid]
  | @cons e w x y z he _ _ _ ih =>
      intro a ha
      simp only [List.mem_cons] at ha
      rcases ha with rfl | ha
      · exact he
      · exact ih a ha

/-- actual runはアフィン実現式を満たす。 -/
theorem realizes {w : Collatz.Word} {x z : ℕ} (h : Runs w x z) :
    w.Realizes x z := by
  induction h with
  | nil x => exact realizes_nil x
  | @cons e w x y z _ hstep _ _ ih =>
      have hs : Realizes ([e] : Collatz.Word) x y :=
        (realizes_singleton_iff e x y).2 hstep
      exact hs.append ih

/-- 実行語が空であるか、終点が奇数。 -/
theorem nil_or_end_odd {w : Collatz.Word} {x z : ℕ}
    (h : Runs w x z) : w = [] ∨ Odd z := by
  induction h with
  | nil x => exact Or.inl rfl
  | @cons e w x y z _ _ hy htail ih =>
      right
      rcases ih with hw | hz
      · subst w
        cases htail
        simpa using hy
      · exact hz

/-- 非空actual runの終点は奇数。 -/
theorem end_odd_of_ne_nil {w : Collatz.Word} {x z : ℕ}
    (h : Runs w x z) (hne : w ≠ []) : Odd z := by
  rcases h.nil_or_end_odd with hw | hz
  · exact False.elim (hne hw)
  · exact hz

/-- cons形の非空actual runの終点は奇数。 -/
theorem end_odd {e : ℕ} {w : Collatz.Word} {x z : ℕ}
    (h : Runs (e :: w) x z) : Odd z :=
  h.end_odd_of_ne_nil (by simp)

/-- actual finite runのreplay。 -/
theorem replay {w : Collatz.Word} {X Z k : ℕ} (h : Runs w X Z) :
    Runs w
      (X + 2 ^ (w.twoSteps + 1) * k)
      (Z + 2 * 3 ^ w.oddSteps * k) := by
  induction h generalizing k with
  | nil x =>
      simpa [twoSteps, oddSteps] using Runs.nil (x + 2 * k)
  | @cons e w x y z he hstep hy htail ih =>
      have hstep' :
          2 ^ e *
              (y + 2 ^ (w.twoSteps + 1) * (3 * k)) =
            3 *
                (x + 2 ^ (e + w.twoSteps + 1) * k) +
              1 := by
        rw [mul_add, hstep]
        simp [pow_add]
        ring
      have hy' :
          Odd (y + 2 ^ (w.twoSteps + 1) * (3 * k)) := by
        apply hy.add_even
        refine ⟨2 ^ w.twoSteps * (3 * k), ?_⟩
        simp [pow_succ]
        ring
      have htail' :
          Runs w
            (y + 2 ^ (w.twoSteps + 1) * (3 * k))
            (z + 2 * 3 ^ w.oddSteps * (3 * k)) :=
        ih (k := 3 * k)
      have hrun :
          Runs (e :: w)
            (x + 2 ^ (e + w.twoSteps + 1) * k)
            (z + 2 * 3 ^ w.oddSteps * (3 * k)) :=
        Runs.cons he hstep' hy' htail'
      simpa [twoSteps, oddSteps, pow_succ, mul_assoc] using hrun

end Runs
end Word
end Collatz
