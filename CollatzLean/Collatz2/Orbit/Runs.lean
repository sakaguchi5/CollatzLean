import CollatzLean.Collatz2.Core.Interval


/-!
# Collatz2: stepwise finite runs

`Word.Realizes` は affine equation だけを保持する。
`Runs` はその背後にある一歩ごとの actual trajectory を lossless に保持する。

prefix / suffix / first crossing などの局所射影はまだ導入せず、
word の連結に対応する run の連結・分解だけを基本 API とする。
-/

namespace Collatz2

/--
有限 exponent word に沿った stepwise run。
各 exponent の正値性と一歩の exact equation を保持する。
-/
inductive Runs : Word → ℕ → ℕ → Prop where
  | nil (x : ℕ) : Runs [] x x
  | cons {e : ℕ} {w : Word} {x y z : ℕ}
      (exponent_pos : 0 < e)
      (step : 2 ^ e * y = 3 * x + 1)
      (tail : Runs w y z) :
      Runs (e :: w) x z

namespace Runs

/-- stepwise run の word は valid。 -/
theorem valid
    {w : Word} {x y : ℕ}
    (h : Runs w x y) :
    Word.Valid w := by
  induction h with
  | nil x =>
      simp [Word.Valid]
  | @cons e w x y z he hstep htail ih =>
      intro a ha
      simp only [List.mem_cons] at ha
      rcases ha with rfl | ha
      · exact he
      · exact ih a ha

/-- stepwise run は affine realization を与える。 -/
theorem realizes
    {w : Word} {x y : ℕ}
    (h : Runs w x y) :
    Word.Realizes w x y := by
  induction h with
  | nil x =>
      exact Word.realizes_nil x
  | @cons e w x y z he hstep htail ih =>
      have hhead : Word.Realizes ([e] : Word) x y :=
        (Word.realizes_singleton_iff e x y).2 hstep
      simpa using hhead.append ih

/-- 二つの stepwise run を連結する。 -/
theorem append
    {u v : Word} {x y z : ℕ}
    (hu : Runs u x y)
    (hv : Runs v y z) :
    Runs (u ++ v) x z := by
  induction hu generalizing z with
  | nil x =>
      simpa using hv
  | @cons e u x y m he hstep htail ih =>
      simp only [List.cons_append]
      exact Runs.cons he hstep (ih hv)

/--
append word の run は中間 boundary を失わず左右の run に分解できる。
-/
theorem split_append
    {u v : Word} {x z : ℕ}
    (h : Runs (u ++ v) x z) :
    ∃ y : ℕ, Runs u x y ∧ Runs v y z := by
  induction u generalizing x with
  | nil =>
      exact ⟨x, Runs.nil x, by simpa using h⟩
  | cons e u ih =>
      cases h with
      | @cons _ _ _ y _ he hstep htail =>
          obtain ⟨m, hu, hv⟩ := ih htail
          exact ⟨m, Runs.cons he hstep hu, hv⟩

/--
lossless interval decomposition に対応して run も
left / body / right の三 run へ分解できる。
-/
theorem split_interval
    {w : Word} {x z : ℕ}
    (h : Runs w x z)
    (I : Interval w) :
    ∃ a b : ℕ,
      Runs I.left x a ∧
      Runs I.body a b ∧
      Runs I.right b z := by
  have h' : Runs (I.left ++ (I.body ++ I.right)) x z := by
    simpa [List.append_assoc, I.decomp] using h
  obtain ⟨a, hleft, hrest⟩ :=
    split_append
      h'
  obtain ⟨b, hbody, hright⟩ :=
    split_append
      hrest
  exact ⟨a, b, hleft, hbody, hright⟩

end Runs
end Collatz2
