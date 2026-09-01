import CollatzLean.Collatz2.Geometry.CriticalFerrersThreeAdicSmallMultiplier

/-!
# Collatz2 Geometry: 3進分離 A/B の actual word 版

抽象高さ列に対して証明した補題 A/B を、実際の exponent word

  h(k) = prefixTwoDepth w k

へ接続する。

重要なのは `prefixTwoDepth` が ℕ 全体では strict monotone ではないこと。
`k >= w.length` では `take k = w` となり一定になるため、ここでは

  i < j <= oddSteps w

という有限区間だけで strict 増加を証明する。
-/

namespace Collatz2
namespace Word

/-- valid word の prefix-two-depth は word 内部では strict に増加する。 -/
theorem prefixTwoDepth_lt_of_valid
    {w : Word}
    (hV : Valid w)
    {i j : ℕ}
    (hij : i < j)
    (hjLe : j ≤ oddSteps w) :
    prefixTwoDepth w i < prefixTwoDepth w j := by
  induction w generalizing i j with
  | nil =>
      simp [oddSteps] at hjLe
      omega
  | cons e w ih =>
      have hePos : 0 < e := hV e (by simp)
      have hVTail : Valid w := by
        intro x hx
        exact hV x (by simp [hx])
      cases i with
      | zero =>
          have hjPos : 0 < j := by omega
          have hjLeLen : j ≤ (e :: w).length := by
            simpa [oddSteps] using hjLe
          have hTakeLen : ((e :: w).take j).length = j :=
            List.length_take_of_le hjLeLen
          have hTakeNe : (e :: w).take j ≠ [] := by
            apply List.ne_nil_of_length_pos
            rw [hTakeLen]
            exact hjPos
          have hTakeValid : Valid ((e :: w).take j) := by
            have hWhole :
                Valid ((e :: w).take j ++ (e :: w).drop j) := by
              simpa using hV
            exact hWhole.prefix
          have hPos :=
            twoSteps_pos_of_valid_nonempty hTakeValid hTakeNe
          simpa [prefixTwoDepth] using hPos
      | succ i =>
          cases j with
          | zero => omega
          | succ j =>
              have hij' : i < j := by omega
              have hjLe' : j ≤ oddSteps w := by
                simpa [oddSteps] using hjLe
              have hlt := ih hVTail hij' hjLe'
              simpa [prefixTwoDepth, List.take_succ_cons, twoSteps_cons] using
                Nat.add_lt_add_left hlt e

/-- valid word では cut index 自身が prefix-two-depth 以下。 -/
theorem index_le_prefixTwoDepth_of_valid
    {w : Word}
    (hV : Valid w)
    {k : ℕ}
    (hkLe : k ≤ oddSteps w) :
    k ≤ prefixTwoDepth w k := by
  induction w generalizing k with
  | nil =>
      simp [oddSteps] at hkLe
      subst k
      simp [prefixTwoDepth]
  | cons e w ih =>
      have hePos : 0 < e := hV e (by simp)
      have hVTail : Valid w := by
        intro x hx
        exact hV x (by simp [hx])
      cases k with
      | zero => simp [prefixTwoDepth]
      | succ k =>
          have hkLe' : k ≤ oddSteps w := by
            simpa [oddSteps] using hkLe
          have hIH := ih hVTail hkLe'
          simp only [prefixTwoDepth, List.take_succ_cons, twoSteps_cons]
          have hDepth : k ≤ twoSteps (List.take k w) := by
            simpa [prefixTwoDepth] using hIH
          omega

@[simp] theorem criticalHeight_one : criticalHeight 1 = 1 := by decide

/--
長さ 2 以上の valid FirstCrossing word では最初の exponent は 1。
したがって最初の二つの Ferrers 高さは `h₀ = 0, h₁ = 1` で固定される。
-/
theorem prefixTwoDepth_one_eq_one_of_valid_firstCrossing
    {w : Word}
    (hV : Valid w)
    (hF : FirstCrossing w)
    (hLen : 2 ≤ oddSteps w) :
    prefixTwoDepth w 1 = 1 := by
  have hLe : prefixTwoDepth w 1 ≤ criticalHeight 1 :=
    hF.prefixTwoDepth_le_criticalHeight (by omega) (by omega)
  have hLeOne : prefixTwoDepth w 1 ≤ 1 := by
    simpa using hLe
  have hPos : 0 < prefixTwoDepth w 1 :=
    prefixTwoDepth_lt_of_valid hV (i := 0) (j := 1) (by omega) (by omega)
  omega

/--
二つの actual profiles が最初に `j` で異なるなら、`j >= 2`。
`0` は定義から共通、`1` は valid FirstCrossing なら共通して 1 だからである。
-/
theorem two_le_firstProfileDifference
    {u v : Word}
    (hVu : Valid u)
    (hVv : Valid v)
    (hFu : FirstCrossing u)
    (hFv : FirstCrossing v)
    (hp : oddSteps u = oddSteps v)
    {j : ℕ}
    (hjLt : j < oddSteps u)
    (hBefore :
      ∀ i : ℕ, i < j →
        prefixTwoDepth u i = prefixTwoDepth v i)
    (hNe : prefixTwoDepth u j ≠ prefixTwoDepth v j) :
    2 ≤ j := by
  have hjNeZero : j ≠ 0 := by
    intro hj0
    subst j
    simp [prefixTwoDepth] at hNe
  have hjNeOne : j ≠ 1 := by
    intro hj1
    subst j
    have hLenU : 2 ≤ oddSteps u := by omega
    have hLenV : 2 ≤ oddSteps v := by omega
    have hu1 := prefixTwoDepth_one_eq_one_of_valid_firstCrossing hVu hFu hLenU
    have hv1 := prefixTwoDepth_one_eq_one_of_valid_firstCrossing hVv hFv hLenV
    exact hNe (hu1.trans hv1.symm)
  omega

/--
actual word 版の補題A。

最初の相違列 `j` の低い高さ

  a = min (prefixTwoDepth u j) (prefixTwoDepth v j)

が、`affineConst u - affineConst v` の exact 2進深さになる。
-/
theorem firstDifference_twoPow_exact_of_valid_words
    {u v : Word}
    (hVu : Valid u)
    (hVv : Valid v)
    (hp : oddSteps u = oddSteps v)
    {j : ℕ}
    (hjLt : j < oddSteps u)
    (hBefore :
      ∀ i : ℕ, i < j →
        prefixTwoDepth u i = prefixTwoDepth v i)
    (hNe : prefixTwoDepth u j ≠ prefixTwoDepth v j) :
    ExactTwoPowZ
      (min (prefixTwoDepth u j) (prefixTwoDepth v j))
      ((affineConst u : ℤ) - (affineConst v : ℤ)) := by
  let a := min (prefixTwoDepth u j) (prefixTwoDepth v j)
  have hjLtV : j < oddSteps v := by simpa [← hp] using hjLt
  have hAfter :
      ∀ i : ℕ, j < i → i < oddSteps u →
        a < prefixTwoDepth u i ∧ a < prefixTwoDepth v i := by
    intro i hji hiLt
    have hiLeU : i ≤ oddSteps u := Nat.le_of_lt hiLt
    have hiLtV : i < oddSteps v := by simpa [← hp] using hiLt
    have hiLeV : i ≤ oddSteps v := Nat.le_of_lt hiLtV
    have huInc := prefixTwoDepth_lt_of_valid hVu hji hiLeU
    have hvInc := prefixTwoDepth_lt_of_valid hVv hji hiLeV
    dsimp [a]
    constructor <;> omega
  have hA := firstDifference_twoPow_exact
      (r := oddSteps u)
      (j := j)
      (a := a)
      (h := fun k => prefixTwoDepth u k)
      (h' := fun k => prefixTwoDepth v k)
      hjLt hBefore hNe rfl hAfter
  have hCodeU :
      criticalFerrersCode (oddSteps u)
          (fun k => prefixTwoDepth u k) =
        affineConst u := by
    simpa using
      (criticalFerrersCode_prefixTwoDepth_eq_affineConst u)
  have hCodeV :
      criticalFerrersCode (oddSteps u)
          (fun k => prefixTwoDepth v k) =
        affineConst v := by
    rw [hp]
    simpa using
      (criticalFerrersCode_prefixTwoDepth_eq_affineConst v)
  unfold criticalFerrersCodeDiffZ at hA
  rw [hCodeU, hCodeV] at hA
  exact hA

/--
actual word 版の補題B。

`affineConst` 差が `q * 3^r` なら、最初の相違列の低い高さが
multiplier `q` の exact 2進深さになる。
-/
theorem collisionMultiplier_twoPow_exact_of_valid_words
    {u v : Word}
    (hVu : Valid u)
    (hVv : Valid v)
    (hp : oddSteps u = oddSteps v)
    {j : ℕ}
    (hjLt : j < oddSteps u)
    (hBefore :
      ∀ i : ℕ, i < j →
        prefixTwoDepth u i = prefixTwoDepth v i)
    (hNe : prefixTwoDepth u j ≠ prefixTwoDepth v j)
    {q : ℤ}
    (hCollision :
      (affineConst u : ℤ) - (affineConst v : ℤ) =
        q * (3 : ℤ) ^ oddSteps u) :
    ExactTwoPowZ
      (min (prefixTwoDepth u j) (prefixTwoDepth v j)) q := by
  have hA :=
    firstDifference_twoPow_exact_of_valid_words
      hVu hVv hp hjLt hBefore hNe
  have hCodeU :
      criticalFerrersCode (oddSteps u)
          (fun k => prefixTwoDepth u k) =
        affineConst u := by
    simpa using
      (criticalFerrersCode_prefixTwoDepth_eq_affineConst u)
  have hCodeV :
      criticalFerrersCode (oddSteps u)
          (fun k => prefixTwoDepth v k) =
        affineConst v := by
    rw [hp]
    simpa using
      (criticalFerrersCode_prefixTwoDepth_eq_affineConst v)
  have hCodeDiffEq :
      criticalFerrersCodeDiffZ
          (oddSteps u)
          (fun k => prefixTwoDepth u k)
          (fun k => prefixTwoDepth v k) =
        (affineConst u : ℤ) - (affineConst v : ℤ) := by
    unfold criticalFerrersCodeDiffZ
    rw [hCodeU, hCodeV]
  have hACode :
      ExactTwoPowZ
        (min (prefixTwoDepth u j) (prefixTwoDepth v j))
        (criticalFerrersCodeDiffZ
          (oddSteps u)
          (fun k => prefixTwoDepth u k)
          (fun k => prefixTwoDepth v k)) := by
    rw [hCodeDiffEq]
    exact hA
  have hCollisionCode :
      criticalFerrersCodeDiffZ
          (oddSteps u)
          (fun k => prefixTwoDepth u k)
          (fun k => prefixTwoDepth v k) =
        q * (3 : ℤ) ^ oddSteps u := by
    unfold criticalFerrersCodeDiffZ
    rw [hCodeU, hCodeV]
    exact hCollision
  have hB :=
    collisionMultiplier_twoPow_exact
      (r := oddSteps u)
      (h := fun k => prefixTwoDepth u k)
      (h' := fun k => prefixTwoDepth v k)
      hACode
      hCollisionCode
  exact hB


/--
actual FirstCrossing での最初の相違列の幾何 bound。

  j <= a < criticalHeight j.
-/
theorem firstDifference_index_bounds_of_valid_firstCrossing
    {u v : Word}
    (hVu : Valid u)
    (hVv : Valid v)
    (hFu : FirstCrossing u)
    (hFv : FirstCrossing v)
    (hp : oddSteps u = oddSteps v)
    {j : ℕ}
    (hjLt : j < oddSteps u)
    (hNe : prefixTwoDepth u j ≠ prefixTwoDepth v j) :
    let a := min (prefixTwoDepth u j) (prefixTwoDepth v j)
    j ≤ a ∧ a < criticalHeight j := by
  intro a
  have hjLtV : j < oddSteps v := by simpa [← hp] using hjLt
  have hju : j ≤ prefixTwoDepth u j :=
    index_le_prefixTwoDepth_of_valid hVu (Nat.le_of_lt hjLt)
  have hjv : j ≤ prefixTwoDepth v j :=
    index_le_prefixTwoDepth_of_valid hVv (Nat.le_of_lt hjLtV)
  have hRoofU : prefixTwoDepth u j ≤ criticalHeight j := by
    by_cases hj0 : j = 0
    · subst j
      simp [prefixTwoDepth]
    · exact hFu.prefixTwoDepth_le_criticalHeight
        (Nat.pos_of_ne_zero hj0) hjLt
  have hRoofV : prefixTwoDepth v j ≤ criticalHeight j := by
    by_cases hj0 : j = 0
    · subst j
      simp [prefixTwoDepth]
    · exact hFv.prefixTwoDepth_le_criticalHeight
        (Nat.pos_of_ne_zero hj0) hjLtV
  constructor
  · dsimp [a]
    exact (Nat.le_min).2 ⟨hju, hjv⟩
  · dsimp [a]
    rcases lt_or_gt_of_ne hNe with hlt | hgt
    · rw [Nat.min_eq_left (Nat.le_of_lt hlt)]
      omega
    · rw [Nat.min_eq_right (Nat.le_of_lt hgt)]
      omega

end Word
end Collatz2
