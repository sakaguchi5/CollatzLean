import CollatzLean.CollatzFirstLayer.CanonicalResidue

/-!
# odd-only有限実行

`Realizes`は終点間のアフィン等式だけを表す。
このファイルでは、各段階で正の指数を使い、次の値が奇数になるという実際の有限実行を定義する。
-/

namespace CollatzFirstLayer
namespace ExpWord

/-- 正の指数語を順に実行するodd-only有限軌道。 -/
inductive Runs : ExpWord → ℕ → ℕ → Prop
  | nil (x : ℕ) : Runs [] x x
  | cons {e : ℕ} {w : ExpWord} {x y z : ℕ}
      (positive : 0 < e)
      (step : 2 ^ e * y = 3 * x + 1)
      (oddNext : Odd y)
      (tail : Runs w y z) : Runs (e :: w) x z

namespace Runs

/-- 実際の有限実行が使う指数語は正である。 -/
theorem valid {w : ExpWord} {x z : ℕ} (h : Runs w x z) : Valid w := by
  induction h with
  | nil x => simp [Valid]
  | @cons e w x y z he hstep hy htail ih =>
      intro a ha
      simp only [List.mem_cons] at ha
      rcases ha with rfl | ha
      · exact he
      · exact ih a ha

/-- 実際の有限実行はアフィン実現式を満たす。 -/
theorem realizes {w : ExpWord} {x z : ℕ} (h : Runs w x z) :
    Realizes w x z := by
  induction h with
  | nil x => exact realizes_nil x
  | @cons e w x y z he hstep hy htail ih =>
      have hsingle : Realizes [e] x y :=
        (realizes_singleton_iff e x y).2 hstep
      simpa using realizes_append hsingle ih

/-- 実行語が空であるか、終点が奇数である。 -/
lemma nil_or_end_odd {w : ExpWord} {x z : ℕ}
    (h : Runs w x z) : w = [] ∨ Odd z := by
  induction h with
  | nil x => exact Or.inl rfl
  | @cons e w x y z he hstep hy htail ih =>
      right
      rcases ih with hw | hz
      · subst w
        cases htail
        simpa using hy
      · exact hz

/-- 非空実行の終点は奇数である。 -/
theorem end_odd_of_ne_nil {w : ExpWord} {x z : ℕ}
    (h : Runs w x z) (hne : w ≠ []) : Odd z := by
  rcases nil_or_end_odd h with hw | hz
  · exact False.elim (hne hw)
  · exact hz

/-- cons形で書いた非空実行の終点奇数性。 -/
lemma end_odd {e : ℕ} {w : ExpWord} {x z : ℕ}
    (h : Runs (e :: w) x z) : Odd z :=
  end_odd_of_ne_nil h (by simp)

/--
実際の有限実行に対するreplay定理。
全中間段階の正指数、指定指数、奇数性を保存する。
-/
theorem replay {w : ExpWord} {X Z k : ℕ} (h : Runs w X Z) :
    Runs w
      (X + 2 ^ (twoSteps w + 1) * k)
      (Z + 2 * 3 ^ oddSteps w * k) := by
  induction h generalizing k with
  | nil x =>
      simpa [twoSteps, oddSteps] using Runs.nil (x + 2 * k)
  | @cons e w x y z he hstep hy htail ih =>
      let y' := y + 2 ^ (twoSteps w + 1) * (3 * k)
      have hstep' :
          2 ^ e * y' =
            3 * (x + 2 ^ (twoSteps (e :: w) + 1) * k) + 1 := by
        unfold y'
        simp only [twoSteps_cons]
        calc
          2 ^ e * (y + 2 ^ (twoSteps w + 1) * (3 * k))
              = 2 ^ e * y +
                3 * (2 ^ e * 2 ^ (twoSteps w + 1) * k) := by ring
          _ = (3 * x + 1) +
                3 * (2 ^ e * 2 ^ (twoSteps w + 1) * k) := by rw [hstep]
          _ = 3 * (x + 2 ^ ((e + twoSteps w) + 1) * k) + 1 := by
                rw [show 2 ^ ((e + twoSteps w) + 1) =
                    2 ^ e * 2 ^ (twoSteps w + 1) by
                  rw [show (e + twoSteps w) + 1 = e + (twoSteps w + 1) by omega]
                  rw [pow_add]]
                ring
      have hy' : Odd y' := by
        rcases hy with ⟨a, rfl⟩
        refine ⟨a + 2 ^ twoSteps w * (3 * k), ?_⟩
        unfold y'
        rw [pow_succ]
        ring
      have htail' := ih (k := 3 * k)
      have hrun :
          Runs (e :: w)
            (x + 2 ^ (twoSteps (e :: w) + 1) * k)
            (z + 2 * 3 ^ oddSteps w * (3 * k)) :=
        Runs.cons he hstep' hy' htail'
      convert hrun using 1
      all_goals
        simp [oddSteps_cons, pow_succ]
        ring

/-- 非空実行の開始値はcanonical剰余類に属する。 -/
theorem start_canonical {e : ℕ} {w : ExpWord} {x z : ℕ}
    (h : Runs (e :: w) x z) :
    ((x : ℕ) : ZMod (residueModulus (e :: w))) =
      canonicalClass (e :: w) := by
  exact natural_start_has_canonical_class h.realizes h.end_odd

/-- 非空実行の開始値はcanonical開始値と同じ剰余を持つ。 -/
theorem start_mod_eq_canonicalStart {e : ℕ} {w : ExpWord} {x z : ℕ}
    (h : Runs (e :: w) x z) :
    x % residueModulus (e :: w) = canonicalStart (e :: w) := by
  exact natural_start_mod_eq_canonicalStart h.realizes h.end_odd

end Runs
end ExpWord
end CollatzFirstLayer
