import CollatzLean.Collatz2.Core.Interval

/-!
# Collatz2: stepwise finite odd-only runs

`Word.Realizes` は affine equation だけを保持する。
`Runs` はその背後にある一歩ごとの actual odd-only trajectory を lossless に保持する。

各 nonempty step では exponent の正値性・exact step equation に加え、
正規化後の次 boundary が odd であることも保持する。
これにより非空 run の endpoint odd は追加仮定なしで導出できる。

prefix / suffix / first crossing などの局所射影は導入せず、
word の連結に対応する run の連結・分解だけを基本 API とする。
-/

namespace Collatz2

/--
有限 exponent word に沿った stepwise odd-only run。
各 exponent の正値性、一歩の exact equation、正規化後 boundary の odd 性を保持する。
-/
inductive Runs : Word → ℕ → ℕ → Prop where
  | nil (x : ℕ) : Runs [] x x
  | cons {e : ℕ} {w : Word} {x y z : ℕ}
      (exponent_pos : 0 < e)
      (step : 2 ^ e * y = 3 * x + 1)
      (next_odd : Odd y)
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
  | @cons e w x y z he hstep hyOdd htail ih =>
      intro a ha
      simp only [List.mem_cons] at ha
      rcases ha with rfl | ha
      · exact he
      · exact ih a ha

/--
非空 odd-only run の開始値も odd。
これは保持データではなく、正の exponent と一歩の exact equation から従う。
-/
theorem start_odd_of_ne_nil
    {w : Word} {x y : ℕ}
    (h : Runs w x y)
    (hne : w ≠ []) :
    Odd x := by
  cases h with
  | nil x =>
      contradiction
  | @cons e w x m z he hstep hmOdd htail =>
      obtain ⟨k, hEven | hOdd⟩ := x.even_or_odd'
      · cases e with
        | zero => omega
        | succ e =>
            have hEq : 2 * (2 ^ e * m) = 6 * k + 1 := by
              calc
                2 * (2 ^ e * m)
                    = 2 ^ (e + 1) * m := by
                        rw [pow_succ]
                        ring
                _ = 3 * x + 1 := hstep
                _ = 6 * k + 1 := by rw [hEven]; ring
            omega
      · exact ⟨k, by omega⟩

/--
非空 odd-only run の endpoint は odd。
最後の一歩の `next_odd` が tail を通して terminal boundary まで伝播する。
-/
theorem end_odd_of_ne_nil
    {w : Word} {x y : ℕ}
    (h : Runs w x y)
    (hne : w ≠ []) :
    Odd y := by
  induction h with
  | nil x =>
      contradiction
  | @cons e w x m z he hstep hmOdd htail ih =>
      by_cases hw : w = []
      · subst w
        cases htail
        exact hmOdd
      · exact ih hw

/-- stepwise run は affine realization を与える。 -/
theorem realizes
    {w : Word} {x y : ℕ}
    (h : Runs w x y) :
    Word.Realizes w x y := by
  induction h with
  | nil x =>
      exact Word.realizes_nil x
  | @cons e w x y z he hstep hyOdd htail ih =>
      have hhead : Word.Realizes ([e] : Word) x y :=
        (Word.realizes_singleton_iff e x y).2 hstep
      simpa using hhead.append ih

/-- 二つの stepwise odd-only run を連結する。 -/
theorem append
    {u v : Word} {x y z : ℕ}
    (hu : Runs u x y)
    (hv : Runs v y z) :
    Runs (u ++ v) x z := by
  induction hu generalizing z with
  | nil x =>
      simpa using hv
  | @cons e u x y m he hstep hyOdd htail ih =>
      simp only [List.cons_append]
      exact Runs.cons he hstep hyOdd (ih hv)

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
      | @cons _ _ _ y _ he hstep hyOdd htail =>
          obtain ⟨m, hu, hv⟩ := ih htail
          exact ⟨m, Runs.cons he hstep hyOdd hu, hv⟩

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
    split_append h'
  obtain ⟨b, hbody, hright⟩ :=
    split_append hrest
  exact ⟨a, b, hleft, hbody, hright⟩

end Runs
end Collatz2
