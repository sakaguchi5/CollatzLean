import CollatzLean.CollatzFirstLayer.FirstCarry
import CollatzLean.CollatzFirstLayer.Orbit

/-!
# first-carry三分岐と同期prefix

従来の`d ≤ e`を前提とした二分岐を拡張し、`e < d`では上下二軌道が
同じ指数を使って一段進み、差の2進深さが`d-e`へ減ることを示す。
さらに、累積2除算数が初期差深さより小さい任意の有限prefixについて、
同じ語をreplayしながら差深さが正確に減る同期定理を与える。
-/

namespace CollatzFirstLayer

/-- `e < d`のとき、上下二値は同じ指数`e`を使って一段同期する。 -/
structure SynchronizedCarry
    (x y d e a u : ℕ) : Type where
  depth_lt : e < d
  upperNext : ℕ
  upperFactor : ExactTwoFactor (3 * y + 1) e upperNext
  nextDifference :
    upperNext = a + 2 ^ (d - e) * (3 * u)
  nextDifferenceOdd : Odd (3 * u)

/-- first-carryの完全な三分岐。 -/
inductive FirstCarryOutcome
    (x y d e a u : ℕ) : Type
  | synchronized (h : SynchronizedCarry x y d e a u)
  | captured
      (depth_lt : d < e)
      (oddPart : ℕ)
      (exactFactor : ExactTwoFactor (3 * y + 1) d oddPart)
  | deferred
      (depth_eq : d = e)
      (quotient : ℕ)
      (extraFactor : 3 * y + 1 = 2 ^ (d + 1) * quotient)

/-- `e < d`ならupper側も指数`e`で正確に止まる。 -/
def synchronized_carry_of_depth_lt
    {x y d e a u : ℕ}
    (hed : e < d)
    (hxy : y = x + 2 ^ d * u)
    (hu : Odd u)
    (hx : 3 * x + 1 = 2 ^ e * a)
    (ha : Odd a) :
    SynchronizedCarry x y d e a u := by
  let r := d - e
  have hr : 0 < r := by
    dsimp [r]
    omega
  have hd : d = e + r := by
    dsimp [r]
    omega
  let b := a + 2 ^ r * (3 * u)
  have hodd3u : Odd (3 * u) := by
    exact (show Odd (3 : ℕ) by decide).mul hu
  have heven : Even (2 ^ r * (3 * u)) := by
    obtain ⟨s, hs⟩ : ∃ s : ℕ, r = s + 1 := by
      exact ⟨r - 1, by omega⟩
    rw [hs]
    exact even_two_pow_succ_mul_nat s (3 * u)
  have hbOdd : Odd b := by
    rcases ha with ⟨ka, hka⟩
    rcases heven with ⟨ke, hke⟩
    refine ⟨ka + ke, ?_⟩
    unfold b
    rw [hka, hke]
    ring
  refine ⟨hed, b, ?_, rfl, hodd3u⟩
  refine ⟨?_, hbOdd⟩
  unfold b
  calc
    3 * y + 1
        = (3 * x + 1) + 3 * 2 ^ d * u := by
            rw [hxy]
            ring
    _ = 2 ^ e * a + 3 * 2 ^ d * u := by rw [hx]
    _ = 2 ^ e * (a + 2 ^ r * (3 * u)) := by
          rw [hd, pow_add]
          ring

/-- first-carryを`e<d`,`d<e`,`d=e`の三枝へ完全分類する。 -/
theorem first_carry_trichotomy_nonempty
    {x y d e a u : ℕ}
    (hxy : y = x + 2 ^ d * u)
    (hu : Odd u)
    (hx : 3 * x + 1 = 2 ^ e * a)
    (ha : Odd a) :
    Nonempty (FirstCarryOutcome x y d e a u) := by
  rcases lt_trichotomy e d with hed | heq | hde
  · exact ⟨FirstCarryOutcome.synchronized
      (synchronized_carry_of_depth_lt hed hxy hu hx ha)⟩
  · subst e
    rcases first_carry_equal hxy hu hx ha with ⟨q, hq⟩
    exact ⟨FirstCarryOutcome.deferred rfl q hq⟩
  · have he : e = d + (e - d) := by omega
    have hx' : 3 * x + 1 = 2 ^ (d + (e - d)) * a := by
      rw [← he]
      exact hx
    rcases first_carry_strict
        (r := e - d) (by omega) hxy hu hx' ha with ⟨b, hb⟩
    exact ⟨FirstCarryOutcome.captured hde b hb⟩

/-- first-carry三分岐を古典選択で一つ取り出す。 -/
noncomputable def first_carry_trichotomy
    {x y d e a u : ℕ}
    (hxy : y = x + 2 ^ d * u)
    (hu : Odd u)
    (hx : 3 * x + 1 = 2 ^ e * a)
    (ha : Odd a) :
    FirstCarryOutcome x y d e a u :=
  Classical.choice
    (first_carry_trichotomy_nonempty hxy hu hx ha)

namespace ExpWord.Runs

/--
初期差深さ`D`が語の総2除算数より大きい間は、
同じ語をreplayできる。
-/
theorem runs_replay_of_gap_depth_gt_twoSteps
    {w : ExpWord} {X Z D u : ℕ}
    (h : Runs w X Z)
    (hdepth : twoSteps w < D) :
    Runs w
      (X + 2 ^ D * u)
      (Z + 2 ^ (D - twoSteps w) * 3 ^ oddSteps w * u) := by
  let r := D - twoSteps w
  have hr : 0 < r := by
    dsimp [r]
    omega
  have hD : D = twoSteps w + r := by
    dsimp [r]
    omega
  obtain ⟨s, hs⟩ : ∃ s : ℕ, r = s + 1 := by
    exact ⟨r - 1, by omega⟩
  have hrun := h.replay (k := 2 ^ s * u)
  convert hrun using 1
  · congr 1
    rw [hD, hs, pow_add, pow_succ, pow_succ]
    ring
  · congr 1
    rw [show D - twoSteps w = r by rfl, hs, pow_succ]
    ring

/-- 初期差深さが語の総2除算数を超える場合、残りの差深さは正である。 -/
lemma replay_endpoint_depth_pos
    {w : ExpWord} {D : ℕ}
    (hdepth : twoSteps w < D) :
    0 < D - twoSteps w := by
  omega

/--
同期replay型の終点差は、`u`が奇数なら完全2進分解を持つ。
その奇数部分は正確に`3^oddSteps(w) * u`である。
-/
theorem replay_endpoint_exact_difference
    {w : ExpWord} {Z D u : ℕ}
    (hu : Odd u) :
    ExactTwoFactor
      ((Z + 2 ^ (D - twoSteps w) * 3 ^ oddSteps w * u) - Z)
      (D - twoSteps w)
      (3 ^ oddSteps w * u) := by
  refine ⟨by simp [Nat.mul_assoc], ?_⟩
  exact
    (show Odd (3 ^ oddSteps w) by
      exact (show Odd (3 : ℕ) by decide).pow).mul hu

/--
初期差深さ`D`が語の総2除算数より大きい間は、同じ語をreplayできる。
終点差深さは正確に`D-twoSteps(w)`へ減り、奇数部分は`3^p u`となる。
-/
theorem replay_of_gap_depth_gt_twoSteps
    {w : ExpWord} {X Z D u : ℕ}
    (h : Runs w X Z)
    (hdepth : twoSteps w < D)
    (hu : Odd u) :
    Runs w
      (X + 2 ^ D * u)
      (Z + 2 ^ (D - twoSteps w) * 3 ^ oddSteps w * u)
    ∧
    0 < D - twoSteps w
    ∧
    ExactTwoFactor
      ((Z + 2 ^ (D - twoSteps w) * 3 ^ oddSteps w * u) - Z)
      (D - twoSteps w)
      (3 ^ oddSteps w * u) := by
  constructor
  · exact runs_replay_of_gap_depth_gt_twoSteps h hdepth
  constructor
  · exact replay_endpoint_depth_pos hdepth
  · exact replay_endpoint_exact_difference
      (w := w) (Z := Z) (D := D) hu

end ExpWord.Runs

end CollatzFirstLayer
