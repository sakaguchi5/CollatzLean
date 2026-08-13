import CollatzLean.Collatz2.Orbit.Runs

/-!
# Collatz2: recover normalized Runs from exact word realization

`Word.Realizes` は whole affine equation だけを保持するが、
word が valid で terminal endpoint が odd なら、その equation から
各 normalized step boundary を順に復元できる。

従って genuine `affineConst` を持つ exact realization は、
この条件下では stepwise `Runs` と同値な情報を持つ。
-/

namespace Collatz2
namespace Word

/--
`cons` word の exact affine realization を、
先頭 odd-only step が見える形へ並べ替える。
-/
theorem Realizes.cons_balance
    {e : ℕ} {v : Word} {x z : ℕ}
    (hreal : Realizes (e :: v) x z) :
    2 ^ e * (2 ^ twoSteps v * z) =
      3 ^ oddSteps v * (3 * x + 1) +
        2 ^ e * affineConst v := by
  have hEq := (realizes_iff (e :: v) x z).1 hreal
  simp only [
    twoSteps_cons,
    oddSteps_cons,
    affineConst_cons
  ] at hEq
  calc
    2 ^ e * (2 ^ twoSteps v * z)
        = 2 ^ (e + twoSteps v) * z := by
          rw [pow_add]
          ring
    _ =
        3 ^ (oddSteps v + 1) * x +
          (3 ^ oddSteps v + 2 ^ e * affineConst v) := hEq
    _ =
        3 ^ oddSteps v * (3 * x + 1) +
          2 ^ e * affineConst v := by
          rw [pow_succ]
          ring

/--
exact realization の先頭では、
normalization factor `2^e` が `3*x+1` を割る。
-/
theorem Realizes.head_two_pow_dvd
    {e : ℕ} {v : Word} {x z : ℕ}
    (hreal : Realizes (e :: v) x z) :
    2 ^ e ∣ 3 * x + 1 := by
  have hbalance := Realizes.cons_balance hreal
  have hdivSum :
      2 ^ e ∣
        3 ^ oddSteps v * (3 * x + 1) +
          2 ^ e * affineConst v := by
    rw [← hbalance]
    exact
      Nat.dvd_mul_right
        (2 ^ e)
        (2 ^ twoSteps v * z)
  have hdivTranslate :
      2 ^ e ∣ 2 ^ e * affineConst v :=
    Nat.dvd_mul_right (2 ^ e) (affineConst v)
  have hdivProd :
      2 ^ e ∣ 3 ^ oddSteps v * (3 * x + 1) :=
    (Nat.dvd_add_iff_left hdivTranslate).2 hdivSum
  have hcop :
      Nat.Coprime (2 ^ e) (3 ^ oddSteps v) :=
    ((by decide : Nat.Coprime 2 3).pow_left e).pow_right
      (oddSteps v)
  exact hcop.dvd_of_dvd_mul_left hdivProd

/--
`Realizes (e :: v) x z` から、
先頭 normalized odd-only step の endpoint `y` と
tail の exact realization を復元する。
-/
theorem Realizes.exists_headStep_tail
    {e : ℕ} {v : Word} {x z : ℕ}
    (hreal : Realizes (e :: v) x z) :
    ∃ y : ℕ,
      2 ^ e * y = 3 * x + 1 ∧
      Realizes v y z := by
  have hdiv :
      2 ^ e ∣ 3 * x + 1 :=
    Realizes.head_two_pow_dvd hreal
  let y : ℕ := (3 * x + 1) / 2 ^ e
  have hstep :
      2 ^ e * y = 3 * x + 1 := by
    dsimp [y]
    exact Nat.mul_div_cancel' hdiv
  have hbalance :=
    Realizes.cons_balance hreal
  have htailMul :
      2 ^ e * (2 ^ twoSteps v * z) =
        2 ^ e *
          (3 ^ oddSteps v * y + affineConst v) := by
    calc
      2 ^ e * (2 ^ twoSteps v * z)
          =
          3 ^ oddSteps v * (3 * x + 1) +
            2 ^ e * affineConst v := hbalance
      _ =
          3 ^ oddSteps v * (2 ^ e * y) +
            2 ^ e * affineConst v := by
            rw [← hstep]
      _ =
          2 ^ e *
            (3 ^ oddSteps v * y + affineConst v) := by
            ring
  have htailEq :
      2 ^ twoSteps v * z =
        3 ^ oddSteps v * y + affineConst v := by
    exact
      Nat.mul_left_cancel
        (Nat.pow_pos (by omega))
        htailMul
  have htailReal :
      Realizes v y z :=
    (realizes_iff v y z).2 htailEq
  exact ⟨y, hstep, htailReal⟩

/--
run の endpoint が odd なら start も odd。
nonempty なら既存の start-odd 性を使い、
empty なら start = endpoint。
-/
theorem Runs.start_odd_of_end_odd
    {v : Word} {x z : ℕ}
    (hrun : Runs v x z)
    (hz : Odd z) :
    Odd x := by
  by_cases hv : v = []
  · subst v
    cases hrun
    exact hz
  · exact hrun.start_odd_of_ne_nil hv

/--
valid word の exact affine realization が odd endpoint を持つなら、
一歩ごとの normalized odd-only `Runs` を復元できる。
-/
theorem Realizes.toRuns_of_valid_of_end_odd
    {w : Word} {x z : ℕ}
    (hreal : Realizes w x z)
    (hvalid : w.Valid)
    (hz : Odd z) :
    Runs w x z := by
  induction w generalizing x with
  | nil =>
      have hEq := (realizes_iff ([] : Word) x z).1 hreal
      have hxz : z = x := by
        simpa [twoSteps, oddSteps, affineConst] using hEq
      subst z
      exact Runs.nil x
  | cons e v ih =>
      have he : 0 < e :=
        hvalid e (by simp)
      have hvalidTail : Valid v := by
        intro a ha
        exact hvalid a (by simp [ha])
      obtain ⟨y, hstep, htailReal⟩ :=
        Realizes.exists_headStep_tail hreal
      have htailRun : Runs v y z :=
        ih htailReal hvalidTail
      have hyOdd : Odd y := by
        by_cases hv : v = []
        · subst v
          cases htailRun
          exact hz
        · exact htailRun.start_odd_of_ne_nil hv
      exact Runs.cons he hstep hyOdd htailRun

end Word
end Collatz2
