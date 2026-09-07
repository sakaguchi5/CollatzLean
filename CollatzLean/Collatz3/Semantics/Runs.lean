import CollatzLean.Collatz3.Semantics.OddStep

/-!
# Collatz3: finite actual odd-only run

途中状態を packet field に埋め込まず、word に沿った inductive relation として持つ。
endpoint affine equation はここでは定義せず、Bridge 層で導出する。
-/

namespace Collatz3

/-- word の各指数を exact に実行する finite odd-only Collatz run。 -/
inductive Runs : Word → ℕ → ℕ → Prop where
  | nil (x : ℕ) : Runs [] x x
  | cons {e : ℕ} {w : Word} {x y z : ℕ}
      (head : OddStep e x y)
      (tail : Runs w y z) :
      Runs (e :: w) x z

namespace Runs

/-- actual run の exponent word は valid。 -/
theorem valid
    {w : Word} {x y : ℕ}
    (h : Runs w x y) :
    Word.Valid w := by
  induction h with
  | nil x =>
      simp [Word.Valid]
  | @cons e w x y z hstep htail ih =>
      intro a ha
      simp only [List.mem_cons] at ha
      rcases ha with rfl | ha
      · exact hstep.exponent_pos
      · exact ih a ha

/-- run は word append で連結できる。 -/
theorem append
    {u v : Word} {x y z : ℕ}
    (hu : Runs u x y)
    (hv : Runs v y z) :
    Runs (u ++ v) x z := by
  induction hu generalizing z with
  | nil x =>
      simpa using hv
  | @cons e u x y m hstep htail ih =>
      simp only [List.cons_append]
      exact Runs.cons hstep (ih hv)

/-- 非空 run の始点は奇数。 -/
theorem start_odd_of_nonempty
    {w : Word} {x y : ℕ}
    (h : Runs w x y)
    (hne : w ≠ []) : Odd x := by
  cases h with
  | nil x => contradiction
  | cons hstep htail => exact hstep.start_odd

/-- 非空 run の終点は奇数。 -/
theorem end_odd_of_nonempty
    {w : Word} {x y : ℕ}
    (h : Runs w x y)
    (hne : w ≠ []) : Odd y := by
  induction h with
  | nil x => contradiction
  | @cons e w x m z hstep htail ih =>
      by_cases hw : w = []
      · subst w
        cases htail
        exact hstep.end_odd
      · exact ih hw

end Runs
end Collatz3
