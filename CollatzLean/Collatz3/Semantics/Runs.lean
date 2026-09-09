import CollatzLean.Collatz3.Semantics.OddStep


/-!
# Collatz3: finite actual odd-only run

途中状態を packet field に埋め込まず、word に沿った inductive relation として持つ。
endpoint affine equation はここでは定義せず、Bridge 層で導出する。

同じ始点からの finite run は odd-only step の決定性により prefix comparable である。
この有限決定性を、`FirstHitsOne` や primitive return の一意性の共通核として使う。
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

/-- 非空 word の run から、最初の一段の中間値を取り出す。 -/
theorem exists_intermediate_of_cons
    {e : ℕ} {w : Word} {x z : ℕ}
    (h : Runs (e :: w) x z) :
    ∃ y : ℕ, OddStep e x y ∧ Runs w y z := by
  cases h with
  | cons hstep htail =>
      exact ⟨_, hstep, htail⟩

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

/--
同じ始点から出る二つの finite actual run は、word としても prefix comparable。
短い方の終点から長い方の終点までの actual suffix run も同時に得る。
-/
theorem prefixComparable_of_common_start
    {u v : Word}
    {x y z : ℕ}
    (hu : Runs u x y)
    (hv : Runs v x z) :
    (∃ t : Word,
      v = u ++ t ∧
        Runs t y z) ∨
      (∃ t : Word,
        u = v ++ t ∧
          Runs t z y) := by
  induction hu generalizing v z with
  | nil x =>
      exact Or.inl ⟨v, by simp, hv⟩
  | @cons e u x m y hstep htail ih =>
      cases hv with
      | nil x =>
          exact Or.inr
            ⟨e :: u, by simp, Runs.cons hstep htail⟩
      | @cons f v x n z hstep' htail' =>
          have hDet := OddStep.deterministic hstep hstep'
          rcases hDet with ⟨hef, hmn⟩
          subst f
          subst n
          rcases ih (v := v) (z := z) htail' with hLeft | hRight
          · rcases hLeft with ⟨t, hEq, hRun⟩
            refine Or.inl ⟨t, ?_, hRun⟩
            simp [hEq]
          · rcases hRight with ⟨t, hEq, hRun⟩
            refine Or.inr ⟨t, ?_, hRun⟩
            simp [hEq]

/--
始点 `x` と終点 `y` が異なる finite run には、`y` へ初めて到達する prefix が存在する。

元の run を左から一段ずつ調べ、最初の endpoint equality を有限に検査する。
無限探索・classical choice・`Nat.find` は使わない。
-/
theorem exists_firstHitPrefix
    {w : Word}
    {x y : ℕ}
    (h : Runs w x y) :
    x ≠ y →
    ∃ v t : Word,
      w = v ++ t ∧
      Runs v x y ∧
      v ≠ [] ∧
      ∀ front back : Word,
        v = front ++ back →
        back ≠ [] →
        ¬ Runs front x y := by
  induction h with
  | nil x =>
      intro hxy
      exact False.elim (hxy rfl)
  | @cons e u x m y hstep htail ih =>
      intro hxy
      by_cases hmy : m = y
      · subst y
        refine ⟨[e], u, by simp, Runs.cons hstep (Runs.nil m), by simp, ?_⟩
        intro front back hEq hBack hFront
        have hBackPos : 0 < Word.oddSteps back := by
          cases back with
          | nil => contradiction
          | cons b bs => simp
        have hSteps := congrArg Word.oddSteps hEq
        have hFrontZero : Word.oddSteps front = 0 := by
          simp [Word.oddSteps_append] at hSteps
          omega
        have hFrontNil : front = [] := by
          by_contra hFrontNe
          have hFrontPos : 0 < Word.oddSteps front := by
            cases front with
            | nil => contradiction
            | cons a as => simp
          omega
        subst front
        cases hFront
        exact hxy rfl
      · rcases ih hmy with
          ⟨v, t, huEq, hvRun, hvNonempty, hvFirst⟩
        refine
          ⟨e :: v, t, ?_, Runs.cons hstep hvRun, by simp, ?_⟩
        · simp [huEq]
        · intro front back hEq hBack hFrontRun
          cases front with
          | nil =>
              cases hFrontRun
              exact hxy rfl
          | cons f fs =>
              rcases Runs.exists_intermediate_of_cons hFrontRun with
                ⟨n, hstep', htail'⟩
              simp only [List.cons_append] at hEq
              injection hEq with hef hRest
              subst f
              have hmn : m = n :=
                (OddStep.deterministic hstep hstep').2
              subst n
              exact hvFirst fs back hRest hBack htail'

/--
同じ始点から同じ odd-step 数だけ進んだ actual run は、
指数語も終点も一意。
-/
theorem word_end_eq_of_common_start_same_oddSteps
    {u v : Word}
    {x y z : ℕ}
    (hu : Runs u x y)
    (hv : Runs v x z)
    (hSteps : Word.oddSteps u = Word.oddSteps v) :
    u = v ∧ y = z := by
  rcases prefixComparable_of_common_start hu hv with
      ⟨t, hEq, hRun⟩ | ⟨t, hEq, hRun⟩
  · have hZero : Word.oddSteps t = 0 := by
      rw [hEq, Word.oddSteps_append] at hSteps
      omega
    have ht : t = [] := by
      by_contra ht
      have hPos : 0 < Word.oddSteps t := by
        cases t with
        | nil => contradiction
        | cons a as => simp
      omega
    subst t
    simp only [List.append_nil] at hEq
    subst v
    cases hRun
    exact ⟨rfl, rfl⟩
  · have hZero : Word.oddSteps t = 0 := by
      rw [hEq, Word.oddSteps_append] at hSteps
      omega
    have ht : t = [] := by
      by_contra ht
      have hPos : 0 < Word.oddSteps t := by
        cases t with
        | nil => contradiction
        | cons a as => simp
      omega
    subst t
    simp only [List.append_nil] at hEq
    subst u
    cases hRun
    exact ⟨rfl, rfl⟩

end Runs
end Collatz3
