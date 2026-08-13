import CollatzLean.Collatz2.Core.DisplacementForm
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Positivity

/-!
# Collatz2: genuine word の translation path

任意の affine transfer では `B` は自由だが、genuine Collatz word では
`B = Word.affineConst w` に固定される。

append law

  `B(u ++ v) = 3^|v| B(u) + 2^H(u) B(v)`

を translation cocycle として読む。

このファイルではさらに、`B` の内部にある prefix-two-depth / suffix-odd-depth の
translation path を明示し、valid word 上では `(oddSteps, twoSteps, affineConst)` が
word 自身を lossless に符号化することを示す。

また二つの translation の差について、

* common prefix は `2^twoSteps(prefix)` を因子として与える
* common suffix は `3^oddSteps(suffix)` を因子として与える

という左右の divisibility shadow を切り出す。
-/

namespace Collatz2
namespace Word

/-- word 連結に対する exact translation cocycle の意味的な別名。 -/
theorem translationCocycle_append (u v : Word) :
    affineConst (u ++ v) =
      3 ^ oddSteps v * affineConst u +
        2 ^ twoSteps u * affineConst v :=
  affineConst_append u v

/--
genuine word の translation は、二つの diagonal coefficient の積より strict に小さい。
-/
theorem affineConst_lt_twoPow_mul_threePow (w : Word) :
    affineConst w <
      2 ^ twoSteps w * 3 ^ oddSteps w := by
  induction w with
  | nil =>
      simp [affineConst, twoSteps, oddSteps]
  | cons e w ih =>
      let X := 2 ^ e
      let Y := 2 ^ twoSteps w
      let Z := 3 ^ oddSteps w
      have hXpos : 0 < X := by
        dsimp [X]
        positivity
      have hYpos : 0 < Y := by
        dsimp [Y]
        positivity
      have hZpos : 0 < Z := by
        dsimp [Z]
        positivity
      have hscaled : X * affineConst w < X * (Y * Z) := by
        exact Nat.mul_lt_mul_of_pos_left (by simpa [Y, Z] using ih) hXpos
      have hXYpos : 0 < X * Y := Nat.mul_pos hXpos hYpos
      have hXYone : 1 ≤ X * Y := by omega
      have hZle : Z ≤ (X * Y) * Z := by
        have h := Nat.mul_le_mul_right Z hXYone
        simpa using h
      have hQpos : 0 < (X * Y) * Z := Nat.mul_pos hXYpos hZpos
      have hstep :
          Z + X * affineConst w < 3 * ((X * Y) * Z) := by
        have h1 :
            Z + X * affineConst w < Z + (X * Y) * Z := by
          have hs : X * affineConst w < (X * Y) * Z := by
            simpa [mul_assoc] using hscaled
          exact Nat.add_lt_add_left hs Z
        omega
      simp only [affineConst_cons, twoSteps_cons, oddSteps_cons]
      rw [pow_add, pow_succ]
      change Z + X * affineConst w < (X * Y) * (Z * 3)
      calc
        Z + X * affineConst w < 3 * ((X * Y) * Z) := hstep
        _ = (X * Y) * (Z * 3) := by ring

/-- genuine translation の size bound を transfer level に持ち上げた版。 -/
theorem ofWord_translate_lt_diagonal_product (w : Word) :
    (AffineTransfer.ofWord w).translate <
      (AffineTransfer.ofWord w).twoCoeff *
        (AffineTransfer.ofWord w).oddCoeff := by
  simpa [AffineTransfer.ofWord] using
    affineConst_lt_twoPow_mul_threePow w

/-- word の displacement form の constant term も同じ bound を満たす。 -/
theorem displacementForm_constant_lt_diagonal_product (w : Word) :
    (AffineTransfer.ofWord w).displacementForm.constant <
      ((AffineTransfer.ofWord w).twoCoeff *
        (AffineTransfer.ofWord w).oddCoeff : ℕ) := by
  change (Word.affineConst w : ℤ) <
    (((2 ^ twoSteps w) * (3 ^ oddSteps w) : ℕ) : ℤ)
  exact_mod_cast affineConst_lt_twoPow_mul_threePow w

/-! ## Translation path の展開 -/

/-- translation path の全項を同じ自然数係数で scale する。 -/
def scaleTranslationTerms (a : ℕ) : List ℕ → List ℕ
  | [] => []
  | t :: ts => a * t :: scaleTranslationTerms a ts

/-- 一様な scaling では path term の個数は変わらない。 -/
theorem length_scaleTranslationTerms
    (a : ℕ)
    (ts : List ℕ) :
    (scaleTranslationTerms a ts).length = ts.length := by
  induction ts with
  | nil =>
      rfl
  | cons t ts ih =>
      simp [scaleTranslationTerms, ih]

/-- 一様に scale した translation path の和も同じ係数だけ scale される。 -/
theorem sum_scaleTranslationTerms
    (a : ℕ)
    (ts : List ℕ) :
    (scaleTranslationTerms a ts).sum = a * ts.sum := by
  induction ts with
  | nil =>
      simp [scaleTranslationTerms]
  | cons t ts ih =>
      simp [scaleTranslationTerms, ih, Nat.mul_add]

/--
総和が `affineConst` になる path term。

`w = [e₁,e₂,...,eₚ]` では

  `3^(p-1),
   2^e₁ * 3^(p-2),
   2^(e₁+e₂) * 3^(p-3), ...`

と展開され、別個の総和 object を導入する必要はない。
-/
def translationPathTerms : Word → List ℕ
  | [] => []
  | e :: w =>
      3 ^ oddSteps w ::
        scaleTranslationTerms (2 ^ e) (translationPathTerms w)

/-- translation path は odd step ごとに1項を持つ。 -/
theorem translationPathTerms_length
    (w : Word) :
    (translationPathTerms w).length = oddSteps w := by
  induction w with
  | nil =>
      rfl
  | cons e w ih =>
      simp [translationPathTerms, length_scaleTranslationTerms, oddSteps, ih]

/-- exact path expansion：全 translation path term の和は `B`。 -/
theorem translationPathTerms_sum_eq_affineConst
    (w : Word) :
    (translationPathTerms w).sum = affineConst w := by
  induction w with
  | nil =>
      rfl
  | cons e w ih =>
      simp [translationPathTerms, sum_scaleTranslationTerms,
        affineConst_cons, ih]

/-! ## 奇性と lossless word coding -/

/-- 3 の任意の冪は odd。 -/
private theorem threePow_odd (n : ℕ) : Odd (3 ^ n) :=
  (show Odd (3 : ℕ) by decide).pow

/-- 2 の正冪は明示的な因子 `2` を一つ持つ。 -/
private theorem twoPow_eq_two_mul_of_pos
    {e : ℕ}
    (he : 0 < e) :
    ∃ q : ℕ, 2 ^ e = 2 * q := by
  obtain ⟨d, hd⟩ : ∃ d : ℕ, e = d + 1 :=
    ⟨e - 1, by omega⟩
  refine ⟨2 ^ d, ?_⟩
  rw [hd, pow_succ]
  ring

/-- valid nonempty word の affine translation は odd。 -/
theorem affineConst_odd_of_valid_nonempty
    {w : Word}
    (hvalid : Valid w)
    (hne : w ≠ []) :
    Odd (affineConst w) := by
  cases w with
  | nil =>
      contradiction
  | cons e w =>
      have he : 0 < e := hvalid e (by simp)
      rcases threePow_odd (oddSteps w) with ⟨a, ha⟩
      obtain ⟨q, hq⟩ := twoPow_eq_two_mul_of_pos he
      refine ⟨a + q * affineConst w, ?_⟩
      rw [affineConst_cons, ha, hq]
      ring

/-- odd な自然数は 2 で割り切れない。 -/
private theorem not_two_dvd_of_odd
    {a : ℕ}
    (ha : Odd a) :
    ¬ 2 ∣ a := by
  intro h2
  rcases ha with ⟨k, hk⟩
  rcases h2 with ⟨m, hm⟩
  omega

/--
2 の冪と odd 数の積どうしが等しければ、その 2 の指数は等しい。
これは translation の injectivity を支える基本的な decoder step である。
-/
private theorem twoPow_mul_odd_exponent_unique
    {e f a b : ℕ}
    (ha : Odd a)
    (hb : Odd b)
    (hEq : 2 ^ e * a = 2 ^ f * b) :
    e = f := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hef | hfe
  · obtain ⟨d, hd⟩ : ∃ d : ℕ, f = e + 1 + d :=
      ⟨f - (e + 1), by omega⟩
    have hcancel :
        2 ^ e * a = 2 ^ e * (2 ^ (1 + d) * b) := by
      calc
        2 ^ e * a = 2 ^ f * b := hEq
        _ = 2 ^ (e + 1 + d) * b := by rw [hd]
        _ = 2 ^ (e + (1 + d)) * b := by
          have hexp : e + 1 + d = e + (1 + d) := by omega
          rw [hexp]
        _ = 2 ^ e * (2 ^ (1 + d) * b) := by
          rw [pow_add]
          ring
    have haEq : a = 2 ^ (1 + d) * b :=
      Nat.mul_left_cancel (Nat.pow_pos (by omega : 0 < (2 : ℕ))) hcancel
    have hdiv : 2 ∣ a := by
      refine ⟨2 ^ d * b, ?_⟩
      rw [haEq, show 1 + d = d + 1 by omega, pow_succ]
      ring
    exact (not_two_dvd_of_odd ha) hdiv
  · obtain ⟨d, hd⟩ : ∃ d : ℕ, e = f + 1 + d :=
      ⟨e - (f + 1), by omega⟩
    have hcancel :
        2 ^ f * b = 2 ^ f * (2 ^ (1 + d) * a) := by
      calc
        2 ^ f * b = 2 ^ e * a := hEq.symm
        _ = 2 ^ (f + 1 + d) * a := by rw [hd]
        _ = 2 ^ (f + (1 + d)) * a := by
          have hexp : f + 1 + d = f + (1 + d) := by omega
          rw [hexp]
        _ = 2 ^ f * (2 ^ (1 + d) * a) := by
          rw [pow_add]
          ring
    have hbEq : b = 2 ^ (1 + d) * a :=
      Nat.mul_left_cancel (Nat.pow_pos (by omega : 0 < (2 : ℕ))) hcancel
    have hdiv : 2 ∣ b := by
      refine ⟨2 ^ d * a, ?_⟩
      rw [hbEq, show 1 + d = d + 1 by omega, pow_succ]
      ring
    exact (not_two_dvd_of_odd hb) hdiv

/--
valid word は lossless triple
`(oddSteps, twoSteps, affineConst)` によって一意に決まる。

最初の exponent は

  `B(e :: tail) - 3^(length tail) = 2^e * B(tail)`

から復号できる。nonempty valid tail の `B` は odd なので `e` が決まり、最後に total
`twoSteps` から残りの exponent が固定される。
-/
theorem valid_word_unique_of_oddSteps_twoSteps_affineConst
    {u v : Word}
    (hu : Valid u)
    (hv : Valid v)
    (hp : oddSteps u = oddSteps v)
    (hH : twoSteps u = twoSteps v)
    (hB : affineConst u = affineConst v) :
    u = v := by
  induction u generalizing v with
  | nil =>
      cases v with
      | nil => rfl
      | cons f v =>
          simp [oddSteps] at hp
  | cons e u ih =>
      cases v with
      | nil =>
          simp [oddSteps] at hp
      | cons f v =>
          have hpTail : oddSteps u = oddSteps v := by
            simp only [oddSteps_cons] at hp
            omega
          have huTail : Valid u := by
            intro a ha
            exact hu a (by simp [ha])
          have hvTail : Valid v := by
            intro a ha
            exact hv a (by simp [ha])
          by_cases huNil : u = []
          · subst u
            cases v with
            | nil =>
                simp only [twoSteps_cons, twoSteps_nil] at hH
                have hef : e = f := by omega
                subst f
                rfl
            | cons g v =>
                simp [oddSteps] at hpTail
          · have hvNe : v ≠ [] := by
              intro hvNil
              subst v
              simp only [oddSteps, List.length_nil, List.length_eq_zero_iff] at hpTail
              exact huNil hpTail
            have huOdd : Odd (affineConst u) :=
              affineConst_odd_of_valid_nonempty huTail huNil
            have hvOdd : Odd (affineConst v) :=
              affineConst_odd_of_valid_nonempty hvTail hvNe
            have hscaled :
                2 ^ e * affineConst u = 2 ^ f * affineConst v := by
              have hB' := hB
              simp only [affineConst_cons] at hB'
              rw [hpTail] at hB'
              exact Nat.add_left_cancel hB'
            have hef : e = f :=
              twoPow_mul_odd_exponent_unique huOdd hvOdd hscaled
            subst f
            have hBtail : affineConst u = affineConst v :=
              Nat.mul_left_cancel
                (Nat.pow_pos (by omega : 0 < (2 : ℕ))) hscaled
            have hHtail : twoSteps u = twoSteps v := by
              simp only [twoSteps_cons] at hH
              omega
            have huv : u = v :=
              ih huTail hvTail hpTail hHtail hBtail
            subst v
            rfl

/-! ## Translation 差の tomography -/

/--
translation 差の exact common-prefix factorization。
suffix の odd-step 数が等しいと、prefix の `3^p * B(prefix)` 寄与が相殺される。
-/
theorem affineConst_sub_commonPrefix_eq
    (r u v : Word)
    (hodd : oddSteps u = oddSteps v) :
    (affineConst (r ++ u) : ℤ) -
        (affineConst (r ++ v) : ℤ) =
      ((2 : ℤ) ^ twoSteps r) *
        ((affineConst u : ℤ) - (affineConst v : ℤ)) := by
  have huZ :
      (affineConst (r ++ u) : ℤ) =
        ((3 : ℤ) ^ oddSteps u) * (affineConst r : ℤ) +
          ((2 : ℤ) ^ twoSteps r) * (affineConst u : ℤ) := by
    exact_mod_cast affineConst_append r u
  have hvZ :
      (affineConst (r ++ v) : ℤ) =
        ((3 : ℤ) ^ oddSteps v) * (affineConst r : ℤ) +
          ((2 : ℤ) ^ twoSteps r) * (affineConst v : ℤ) := by
    exact_mod_cast affineConst_append r v
  rw [huZ, hvZ, hodd]
  ring

/-- common prefix は差に対して `2^twoSteps` の全因子を与える。 -/
theorem twoPow_prefix_dvd_affineConst_sub
    (r u v : Word)
    (hodd : oddSteps u = oddSteps v) :
    ((2 ^ twoSteps r : ℕ) : ℤ) ∣
      (affineConst (r ++ u) : ℤ) -
        (affineConst (r ++ v) : ℤ) := by
  refine ⟨(affineConst u : ℤ) - (affineConst v : ℤ), ?_⟩
  simpa using affineConst_sub_commonPrefix_eq r u v hodd

/--
二つの residual word が valid かつ nonempty なら、それらの odd translation の差には
common-prefix depth に加えてさらに因子 `2` が一つ現れる。
-/
theorem twoPow_succ_prefix_dvd_affineConst_sub
    (r u v : Word)
    (hu : Valid u)
    (hv : Valid v)
    (hune : u ≠ [])
    (hvne : v ≠ [])
    (hodd : oddSteps u = oddSteps v) :
    ((2 ^ (twoSteps r + 1) : ℕ) : ℤ) ∣
      (affineConst (r ++ u) : ℤ) -
        (affineConst (r ++ v) : ℤ) := by
  rcases affineConst_odd_of_valid_nonempty hu hune with ⟨a, ha⟩
  rcases affineConst_odd_of_valid_nonempty hv hvne with ⟨b, hb⟩
  refine ⟨(a : ℤ) - (b : ℤ), ?_⟩
  rw [affineConst_sub_commonPrefix_eq r u v hodd, ha, hb]
  push_cast
  rw [pow_succ]
  ring

/--
two-depth が2以上の common prefix の後に nonempty valid residual が続くなら、
translation 差は 8 で割り切れる。
-/
theorem eight_dvd_affineConst_sub_of_commonPrefix_twoSteps_ge_two
    (r u v : Word)
    (hu : Valid u)
    (hv : Valid v)
    (hune : u ≠ [])
    (hvne : v ≠ [])
    (hodd : oddSteps u = oddSteps v)
    (hdepth : 2 ≤ twoSteps r) :
    (8 : ℤ) ∣
      (affineConst (r ++ u) : ℤ) -
        (affineConst (r ++ v) : ℤ) := by
  obtain ⟨d, hd⟩ : ∃ d : ℕ, twoSteps r + 1 = d + 3 :=
    ⟨twoSteps r - 2, by omega⟩
  rcases twoPow_succ_prefix_dvd_affineConst_sub
      r u v hu hv hune hvne hodd with ⟨q, hq⟩
  refine ⟨(((2 ^ d : ℕ) : ℤ) * q), ?_⟩
  rw [hq, hd, pow_add]
  norm_num
  ring

/--
translation 差の exact common-suffix factorization。
prefix の two-step 数が等しいと、suffix の `2^H * B(suffix)` 寄与が相殺される。
-/
theorem affineConst_sub_commonSuffix_eq
    (u v s : Word)
    (htwo : twoSteps u = twoSteps v) :
    (affineConst (u ++ s) : ℤ) -
        (affineConst (v ++ s) : ℤ) =
      ((3 : ℤ) ^ oddSteps s) *
        ((affineConst u : ℤ) - (affineConst v : ℤ)) := by
  have huZ :
      (affineConst (u ++ s) : ℤ) =
        ((3 : ℤ) ^ oddSteps s) * (affineConst u : ℤ) +
          ((2 : ℤ) ^ twoSteps u) * (affineConst s : ℤ) := by
    exact_mod_cast affineConst_append u s
  have hvZ :
      (affineConst (v ++ s) : ℤ) =
        ((3 : ℤ) ^ oddSteps s) * (affineConst v : ℤ) +
          ((2 : ℤ) ^ twoSteps v) * (affineConst s : ℤ) := by
    exact_mod_cast affineConst_append v s
  rw [huZ, hvZ, htwo]
  ring

/-- common suffix は差に対して `3^oddSteps` の全因子を与える。 -/
theorem threePow_suffix_dvd_affineConst_sub
    (u v s : Word)
    (htwo : twoSteps u = twoSteps v) :
    ((3 ^ oddSteps s : ℕ) : ℤ) ∣
      (affineConst (u ++ s) : ℤ) -
        (affineConst (v ++ s) : ℤ) := by
  refine ⟨(affineConst u : ℤ) - (affineConst v : ℤ), ?_⟩
  simpa using affineConst_sub_commonSuffix_eq u v s htwo

/--
先頭の等しい `3^p` 項が相殺された後、十分に深い head exponent は residual translation 差に
共通因子 `2^m` を与える。
-/
theorem twoPow_head_dvd_affineConst_sub
    {a b m : ℕ}
    (u v : Word)
    (hodd : oddSteps u = oddSteps v)
    (hma : m ≤ a)
    (hmb : m ≤ b) :
    ((2 ^ m : ℕ) : ℤ) ∣
      (affineConst (a :: u) : ℤ) -
        (affineConst (b :: v) : ℤ) := by
  obtain ⟨da, hda⟩ : ∃ da : ℕ, a = m + da :=
    ⟨a - m, by omega⟩
  obtain ⟨db, hdb⟩ : ∃ db : ℕ, b = m + db :=
    ⟨b - m, by omega⟩
  refine ⟨((2 : ℤ) ^ da) * (affineConst u : ℤ) -
      ((2 : ℤ) ^ db) * (affineConst v : ℤ), ?_⟩
  simp only [affineConst_cons]
  push_cast
  rw [hodd, hda, hdb, pow_add, pow_add]
  ring

/--
final exponent 自体は `B` に現れない。mod 3 では terminal exponent より前の prefix だけが残る。
-/
theorem affineConst_append_singleton_mod_three
    (u : Word)
    (e : ℕ) :
    ((affineConst (u ++ [e]) : ℕ) : ZMod 3) =
      (2 : ZMod 3) ^ twoSteps u := by
  have h := affineConst_append u ([e] : Word)
  have hcast :=
    congrArg (fun n : ℕ => (n : ZMod 3)) h
  calc
    ((affineConst (u ++ [e]) : ℕ) : ZMod 3)
        =
        (3 : ZMod 3) *
            ((affineConst u : ℕ) : ZMod 3) +
          (2 : ZMod 3) ^ twoSteps u := by
      simpa [oddSteps, twoSteps, affineConst] using hcast
    _ = (2 : ZMod 3) ^ twoSteps u := by
      have h3 : (3 : ZMod 3) = 0 := by
        decide
      rw [h3]
      simp

end Word
end Collatz2
