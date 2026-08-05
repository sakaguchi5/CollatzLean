import CollatzLean.CollatzSecondLayer2.LongPlateauRefinement
import Mathlib.Tactic.Linarith

/-!
# no-critical contracting normalizationの定量評価

正の指数語のaffine定数にgeometric上界を与え、orderedかつcontractingな
q-windowの正差を`(3/2)^q`未満に抑える。

さらにsynchronized区間では差深さが消費総指数だけ減ることを用いて、
no-critical normalization中のsynchronized plateau長をwindow長未満に抑える。
この評価からterminal時刻とterminal endpointのscaled polynomial上界を得る。
-/

namespace CollatzSecondLayer2

open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

namespace ExpWord

/--
正の指数語では、affine定数を総scaleへ戻した量は`3^p`以下。

`2^p * B_w ≤ 3^p * 2^H`。
-/
theorem twoPow_oddSteps_mul_affineConst_le
    {w : ExpWord}
    (hvalid : Valid w) :
    2 ^ oddSteps w * affineConst w ≤
      3 ^ oddSteps w * 2 ^ twoSteps w := by
  induction w with
  | nil =>
      simp
  | cons e w ih =>
      have he : 0 < e := hvalid e (by simp)
      have hw : Valid w := by
        intro a ha
        exact hvalid a (by simp [ha])
      have hih := ih hw
      have hlen : oddSteps w ≤ twoSteps w :=
        oddSteps_le_twoSteps hw
      have hpow :
          2 ^ (oddSteps w + 1) ≤
            2 ^ (e + twoSteps w) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      have hhead :
          2 ^ (oddSteps w + 1) * 3 ^ oddSteps w ≤
            3 ^ oddSteps w * 2 ^ (e + twoSteps w) := by
        simpa [Nat.mul_comm] using
          Nat.mul_le_mul_left (3 ^ oddSteps w) hpow
      have htail :
          2 ^ (oddSteps w + 1) *
              (2 ^ e * affineConst w) ≤
            (2 * 3 ^ oddSteps w) *
              2 ^ (e + twoSteps w) := by
        calc
          2 ^ (oddSteps w + 1) *
                (2 ^ e * affineConst w)
              = 2 ^ (e + 1) *
                  (2 ^ oddSteps w * affineConst w) := by
                    rw [pow_add, pow_add]
                    ring
          _ ≤ 2 ^ (e + 1) *
                (3 ^ oddSteps w * 2 ^ twoSteps w) :=
              Nat.mul_le_mul_left _ hih
          _ = (2 * 3 ^ oddSteps w) *
                2 ^ (e + twoSteps w) := by
              rw [pow_add, pow_add]
              ring
      simp only [oddSteps_cons, affineConst_cons, twoSteps_cons]
      rw [pow_succ, pow_succ]
      calc
        (2 ^ oddSteps w * 2) *
              (3 ^ oddSteps w + 2 ^ e * affineConst w)
            =
          2 ^ (oddSteps w + 1) * 3 ^ oddSteps w +
            2 ^ (oddSteps w + 1) *
              (2 ^ e * affineConst w) := by
                rw [pow_succ]
                ring
        _ ≤
          3 ^ oddSteps w * 2 ^ (e + twoSteps w) +
            (2 * 3 ^ oddSteps w) *
              2 ^ (e + twoSteps w) :=
              Nat.add_le_add hhead htail
        _ = (3 ^ oddSteps w * 3) *
              2 ^ (e + twoSteps w) := by ring

end ExpWord

namespace OddOrbit.WindowDifferenceData

/-- 同じactual ordered windowを表す差分データの2進深さは一意。 -/
theorem depth_unique
    {O : OddOrbit} {i q : ℕ}
    (D E : O.WindowDifferenceData i q) :
    D.depth = E.depth := by
  let delta := O.value (i + q) - O.value i
  have hD : ExactTwoFactor delta D.depth D.oddPart := by
    refine ⟨?_, D.oddPart_odd⟩
    dsimp [delta]
    rw [D.difference]
    omega
  have hE : ExactTwoFactor delta E.depth E.oddPart := by
    refine ⟨?_, E.oddPart_odd⟩
    dsimp [delta]
    rw [E.difference]
    omega
  exact exactTwoFactor_exponent_unique hD hE

/--
`C < A`で正の`x`を持ち、

`A*x + A*delta = C*x + B`

なら、contracting差`(A-C)*x`の分だけ余裕があるため
`A*delta < B`。
-/
theorem mul_delta_lt_of_contracting_balance
    {A C x delta B : ℕ}
    (hCA : C < A)
    (hxPos : 0 < x)
    (hbalance :
      A * x + A * delta =
        C * x + B) :
    A * delta < B := by
  have hAeq :
      A = C + (A - C) :=
    (Nat.add_sub_of_le hCA.le).symm
  have hAx :
      A * x = C * x + (A - C) * x := by
    have h := congrArg (fun n : ℕ => n * x) hAeq
    rw [Nat.add_mul] at h
    exact h
  rw [hAx] at hbalance
  have hgapPos :
      0 < (A - C) * x :=
    Nat.mul_pos
      (Nat.sub_pos_of_lt hCA)
      hxPos
  omega


/--
`A*delta < B`とscaled affine budget

`m*B ≤ C*A`

から、正の因子`A`を消去して`m*delta < C`を得る。
-/
theorem scaled_gap_lt_of_affine_budget
    {m A delta B C : ℕ}
    (hmPos : 0 < m)
    (hApos : 0 < A)
    (hdelta : A * delta < B)
    (hbudget : m * B ≤ C * A) :
    m * delta < C := by
  have hscaled :
      m * (A * delta) < m * B :=
    (Nat.mul_lt_mul_left hmPos).2 hdelta
  have hwithA :
      (m * delta) * A < C * A := by
    calc
      (m * delta) * A
          = m * (A * delta) := by
              ring
      _ < m * B :=
        hscaled
      _ ≤ C * A :=
        hbudget
  exact
    (Nat.mul_lt_mul_right hApos).1 hwithA

/--
validなq-windowのaffine定数はscaledに

`2^q * affineConst ≤ 3^q * 2^H`

を満たす。
-/
theorem twoPow_length_mul_segmentAffineConst_le
    {O : OddOrbit} {i q : ℕ} :
    2 ^ q * affineConst (O.segmentWord i q) ≤
      3 ^ q * 2 ^ O.windowTwoSteps i q := by
  let w : ExpWord :=
    O.segmentWord i q
  have hwValid : Valid w := by
    simpa [w] using
      (O.runs_segment i q).valid
  have h :=
    ExpWord.twoPow_oddSteps_mul_affineConst_le
      hwValid
  simpa [
    w,
    OddOrbit.windowTwoSteps,
    oddSteps
  ] using h


/--
orderedかつcontractingなq-windowでは、
scaledな正差がaffine定数より厳密に小さい。

`2^H * (upper-lower) < affineConst`。
-/
theorem windowTwoPow_mul_gap_lt_segmentAffineConst
    {O : OddOrbit} {i q : ℕ}
    (D : O.WindowDifferenceData i q)
    (hcontract :
      3 ^ q < 2 ^ O.windowTwoSteps i q) :
    2 ^ O.windowTwoSteps i q *
        (2 ^ D.depth * D.oddPart) <
      affineConst (O.segmentWord i q) := by
  let w : ExpWord :=
    O.segmentWord i q
  let H : ℕ :=
    O.windowTwoSteps i q
  let A : ℕ :=
    2 ^ H
  let C : ℕ :=
    3 ^ q
  let B : ℕ :=
    affineConst w
  let delta : ℕ :=
    2 ^ D.depth * D.oddPart
  have hrun :
      A * O.value (i + q) =
        C * O.value i + B := by
    simpa [
      w,
      H,
      A,
      C,
      B,
      ExpWord.Realizes,
      OddOrbit.windowTwoSteps,
      oddSteps
    ] using
      O.realizes_segment i q
  have hbalance :
      A * O.value i + A * delta =
        C * O.value i + B := by
    simpa [
      delta,
      D.difference,
      Nat.mul_add
    ] using hrun
  have hCA : C < A := by
    simpa [C, A, H] using hcontract
  have hdelta :
      A * delta < B :=
    mul_delta_lt_of_contracting_balance
      hCA
      (O.value_pos i)
      hbalance
  simpa [A, B, delta, H, w] using hdelta

/--
orderedかつcontractingなq-windowの正差はscaledに`3^q`未満。

`2^q * (upper-lower) < 3^q`。
-/
theorem twoPow_length_mul_gap_lt_threePow
    {O : OddOrbit} {i q : ℕ}
    (D : O.WindowDifferenceData i q)
    (hcontract :
      3 ^ q < 2 ^ O.windowTwoSteps i q) :
    2 ^ q * (2 ^ D.depth * D.oddPart) <
      3 ^ q := by
  refine
    scaled_gap_lt_of_affine_budget
      (m := 2 ^ q)
      (A := 2 ^ O.windowTwoSteps i q)
      (delta := 2 ^ D.depth * D.oddPart)
      (B := affineConst (O.segmentWord i q))
      (C := 3 ^ q)
      ?_ ?_ ?_ ?_
  · positivity
  · positivity
  · exact
      windowTwoPow_mul_gap_lt_segmentAffineConst
        D hcontract
  · exact
      twoPow_length_mul_segmentAffineConst_le
        (O := O)
        (i := i)
        (q := q)


end OddOrbit.WindowDifferenceData

namespace OddOrbit.SynchronizedWindowAt

/-- synchronized一段後の差深さはlower指数だけexactに減る。 -/
theorem nextDepth_add_exponent_eq
    {O : OddOrbit} {i q : ℕ}
    (S : O.SynchronizedWindowAt i q)
    (Dnext : O.WindowDifferenceData (i + 1) q) :
    Dnext.depth + O.exponent i = S.depth := by
  let E : O.WindowDifferenceData (i + 1) q :=
    { depth := S.depth - O.exponent i
      oddPart := 3 * S.oddPart
      difference := by
        have h := S.upperNext_eq
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
      oddPart_odd :=
        (show Odd (3 : ℕ) by decide).mul S.oddPart_odd }
  have hdepth : Dnext.depth = E.depth :=
    Dnext.depth_unique E
  have hle : O.exponent i ≤ S.depth :=
    Nat.le_of_lt S.synchronized
  dsimp [E] at hdepth
  omega

end OddOrbit.SynchronizedWindowAt

namespace OddOrbit

theorem two_le_twoPow_exponent
    (O : OddOrbit)
    (i : ℕ) :
    2 ≤ 2 ^ O.exponent i := by
  have heNe :
      O.exponent i ≠ 0 :=
    Nat.ne_of_gt (O.exponent_pos i)
  obtain ⟨r, hr⟩ :=
    Nat.exists_eq_succ_of_ne_zero heNe
  rw [hr, pow_succ]
  have hpow :
      0 < 2 ^ r :=
    Nat.pow_pos (by omega)
  omega


/--
odd-only軌道の一段成長は、`+1`した量について
`3/2`以下に抑えられる。

`2 * (x_{i+1} + 1) ≤ 3 * (x_i + 1)`。
-/
theorem two_mul_nextValue_add_one_le_three_mul
    (O : OddOrbit)
    (i : ℕ) :
    2 * (O.value (i + 1) + 1) ≤
      3 * (O.value i + 1) := by
  have he :
      2 ≤ 2 ^ O.exponent i :=
    two_le_twoPow_exponent O i
  have hs := O.step i
  calc
    2 * (O.value (i + 1) + 1)
        =
      2 * O.value (i + 1) + 2 := by
        ring
    _ ≤
      2 ^ O.exponent i * O.value (i + 1) + 2 := by
        exact
          Nat.add_le_add_right
            (Nat.mul_le_mul_right
              (O.value (i + 1))
              he)
            2
    _ =
      3 * O.value i + 3 := by
        rw [hs]
    _ =
      3 * (O.value i + 1) := by
        ring


/--
一段評価とtailのn段評価から、n+1段評価を得る。
-/
theorem twoPow_succ_mul_value_add_one_le_threePow_succ
    (O : OddOrbit)
    (i n : ℕ)
    (htail :
      2 ^ n * (O.value (i + 1 + n) + 1) ≤
        3 ^ n * (O.value (i + 1) + 1)) :
    2 ^ (n + 1) * (O.value (i + (n + 1)) + 1) ≤
      3 ^ (n + 1) * (O.value i + 1) := by
  have hstep :
      2 * (O.value (i + 1) + 1) ≤
        3 * (O.value i + 1) :=
    two_mul_nextValue_add_one_le_three_mul O i
  have hindex :
      i + (n + 1) = i + 1 + n := by
    simp only [Nat.add_comm, Nat.add_left_comm]
  calc
    2 ^ (n + 1) * (O.value (i + (n + 1)) + 1)
        =
      2 *
        (2 ^ n * (O.value (i + 1 + n) + 1)) := by
          rw [hindex, pow_succ]
          ring
    _ ≤
      2 *
        (3 ^ n * (O.value (i + 1) + 1)) :=
          Nat.mul_le_mul_left 2 htail
    _ =
      3 ^ n *
        (2 * (O.value (i + 1) + 1)) := by
          ring
    _ ≤
      3 ^ n *
        (3 * (O.value i + 1)) :=
          Nat.mul_le_mul_left (3 ^ n) hstep
    _ =
      3 ^ (n + 1) * (O.value i + 1) := by
          rw [pow_succ]
          ring


/-- odd-only軌道のn段成長を`(3/2)^n`でscaledに抑える。 -/
theorem twoPow_mul_value_add_one_le_threePow
    (O : OddOrbit)
    (i : ℕ) :
    ∀ n : ℕ,
      2 ^ n * (O.value (i + n) + 1) ≤
        3 ^ n * (O.value i + 1) := by
  intro n
  induction n generalizing i with
  | zero =>
      simp
  | succ n ih =>
      exact
        twoPow_succ_mul_value_add_one_le_threePow_succ
          O i n
          (ih (i := i + 1))

/-- r≤qなら位置rの値をq-scaleへ持ち上げて抑えられる。 -/
theorem twoPow_full_mul_value_le_threePow_full
    (O : OddOrbit) (i : ℕ)
    {r q : ℕ}
    (hrq : r ≤ q) :
    2 ^ q * O.value (i + r) ≤
      3 ^ q * (O.value i + 1) := by
  have hbase :=
    O.twoPow_mul_value_add_one_le_threePow i r
  have h23 :
      2 ^ (q - r) ≤ 3 ^ (q - r) :=
    twoPow_le_threePow (q - r)
  have hpowTwo :
      2 ^ q = 2 ^ (q - r) * 2 ^ r := by
    rw [← pow_add, Nat.sub_add_cancel hrq]
  have hpowThree :
      3 ^ q = 3 ^ (q - r) * 3 ^ r := by
    rw [← pow_add, Nat.sub_add_cancel hrq]
  calc
    2 ^ q * O.value (i + r)
        ≤ 2 ^ q * (O.value (i + r) + 1) :=
      Nat.mul_le_mul_left _ (Nat.le_succ _)
    _ =
        2 ^ (q - r) *
          (2 ^ r * (O.value (i + r) + 1)) := by
      rw [hpowTwo]
      ring
    _ ≤
        2 ^ (q - r) *
          (3 ^ r * (O.value i + 1)) :=
      Nat.mul_le_mul_left _ hbase
    _ ≤
        3 ^ (q - r) *
          (3 ^ r * (O.value i + 1)) :=
      Nat.mul_le_mul_right
        (3 ^ r * (O.value i + 1))
        h23
    _ =
        3 ^ q * (O.value i + 1) := by
      rw [hpowThree]
      ring

end OddOrbit

namespace OddOrbit

/--
window総指数を先頭指数と残りのwindow総指数へ分解する。
-/
theorem windowTwoSteps_succ_eq
    (O : OddOrbit)
    (i L : ℕ) :
    O.windowTwoSteps i (L + 1) =
      O.exponent i +
        O.windowTwoSteps (i + 1) L := by
  simp [
    OddOrbit.windowTwoSteps,
    OddOrbit.segmentWord_succ,
    twoSteps
  ]


/--
長さ`L+1`のsynchronized区間から、
先頭を除いた長さ`L`のsynchronized区間を得る。
-/
def synchronizedInterval_tail
    (O : OddOrbit)
    {start q a L : ℕ}
    (hsync :
      ∀ t : ℕ, t < L + 1 →
        O.SynchronizedWindowAt
          (start + a + t) q) :
    ∀ t : ℕ, t < L →
      O.SynchronizedWindowAt
        (start + (a + 1) + t) q := by
  intro t ht
  have h :=
    hsync (t + 1) (by omega)
  simpa [
    Nat.add_assoc,
    Nat.add_comm,
    Nat.add_left_comm
  ] using h

end OddOrbit

namespace OddOrbit.FiniteCaptureNormalizationData

/--
一つのsynchronized shiftでは、
消費指数と次時刻の差深さの和が現在差深さに等しい。
-/
theorem synchronizedStep_depth_balance
    {O : OddOrbit} {start q : ℕ}
    {D₀ : O.WindowDifferenceData start q}
    (F : O.FiniteCaptureNormalizationData D₀)
    (a : ℕ)
    (ha : a ≤ F.terminalTime)
    (haNext : a + 1 ≤ F.terminalTime)
    (S :
      O.SynchronizedWindowAt
        (start + a) q) :
    O.exponent (start + a) +
        (F.difference (a + 1) haNext).depth =
      (F.difference a ha).depth := by
  let Dstart :=
    F.difference a ha
  let Dnext :=
    F.difference (a + 1) haNext
  have hSdepth :
      S.depth = Dstart.depth := by
    exact
      S.toWindowDifferenceData.depth_unique
        Dstart
  have hnext :
      Dnext.depth +
          O.exponent (start + a) =
        S.depth := by
    simpa [
      Dnext,
      Nat.add_assoc
    ] using
      S.nextDepth_add_exponent_eq Dnext
  calc
    O.exponent (start + a) + Dnext.depth
        =
      Dnext.depth + O.exponent (start + a) := by
        rw [Nat.add_comm]
    _ = S.depth :=
      hnext
    _ = Dstart.depth :=
      hSdepth

/--
同じ時刻を表す二つの添字では、
`difference`に渡す上界証明が異なっていてもdepthは一致する。
-/
theorem difference_depth_eq_of_index_eq
    {O : OddOrbit} {start q : ℕ}
    {D₀ : O.WindowDifferenceData start q}
    (F : O.FiniteCaptureNormalizationData D₀)
    {a b : ℕ}
    (ha : a ≤ F.terminalTime)
    (hb : b ≤ F.terminalTime)
    (hab : a = b) :
    (F.difference a ha).depth =
      (F.difference b hb).depth := by
  subst b
  rfl

/--
tailのdepth収支と先頭一段のdepth収支を合成する。
-/
theorem prepend_depth_balance
    {head tail endDepth nextDepth startDepth : ℕ}
    (htail :
      tail + endDepth = nextDepth)
    (hstep :
      head + nextDepth = startDepth) :
    (head + tail) + endDepth = startDepth := by
  calc
    (head + tail) + endDepth
        = head + (tail + endDepth) := by
            rw [Nat.add_assoc]
    _ = head + nextDepth := by
          rw [htail]
    _ = startDepth :=
          hstep

/--
先頭のsynchronized一段と、残り`L`段のdepth収支から、
長さ`L+1`のdepth収支を構成する。
-/
theorem synchronizedInterval_depth_balance_succ_of_tail
    {O : OddOrbit} {start q : ℕ}
    {D₀ : O.WindowDifferenceData start q}
    (F : O.FiniteCaptureNormalizationData D₀)
    (a L : ℕ)
    (hinside :
      a + (L + 1) ≤ F.terminalTime)
    (ha :
      a ≤ F.terminalTime)
    (haNext :
      a + 1 ≤ F.terminalTime)
    (htailInside :
      a + 1 + L ≤ F.terminalTime)
    (S :
      O.SynchronizedWindowAt
        (start + a) q)
    (htail :
      O.windowTwoSteps
            (start + (a + 1)) L +
          (F.difference
            (a + 1 + L)
            htailInside).depth =
        (F.difference
          (a + 1)
          haNext).depth) :
    O.windowTwoSteps (start + a) (L + 1) +
        (F.difference
          (a + (L + 1))
          hinside).depth =
      (F.difference a ha).depth := by
  have hstep :
      O.exponent (start + a) +
          (F.difference
            (a + 1)
            haNext).depth =
        (F.difference a ha).depth :=
    F.synchronizedStep_depth_balance
      a ha haNext S
  have hcombined :
      (O.exponent (start + a) +
          O.windowTwoSteps
            (start + (a + 1)) L) +
        (F.difference
          (a + 1 + L)
          htailInside).depth =
      (F.difference a ha).depth := by
    exact
      prepend_depth_balance
        htail
        hstep
  have hstartIndex :
      start + a + 1 =
        start + (a + 1) := by
    simp [Nat.add_assoc]
  have hendIndex :
      a + (L + 1) =
        a + 1 + L := by
    omega
  have hendDepth :
      (F.difference
          (a + (L + 1))
          hinside).depth =
        (F.difference
          (a + 1 + L)
          htailInside).depth := by
    exact
      F.difference_depth_eq_of_index_eq
        hinside
        htailInside
        hendIndex
  rw [
    O.windowTwoSteps_succ_eq
      (start + a)
      L
  ]
  rw [hstartIndex, hendDepth]
  exact hcombined

/--
synchronized区間では、消費総指数と終端差深さの和が
開始差深さに等しい。
-/
theorem synchronizedInterval_depth_balance
    {O : OddOrbit} {start q : ℕ}
    {D₀ : O.WindowDifferenceData start q}
    (F : O.FiniteCaptureNormalizationData D₀)
    (a L : ℕ)
    (hinside :
      a + L ≤ F.terminalTime)
    (hsync :
      ∀ t : ℕ, t < L →
        O.SynchronizedWindowAt
          (start + a + t) q) :
    O.windowTwoSteps (start + a) L +
        (F.difference
          (a + L)
          hinside).depth =
      (F.difference a
        (le_trans
          (Nat.le_add_right a L)
          hinside)).depth := by
  induction L generalizing a with
  | zero =>
      simp [OddOrbit.windowTwoSteps]
  | succ L ih =>
      have ha :
          a ≤ F.terminalTime := by
        exact
          le_trans
            (Nat.le_add_right a (L + 1))
            hinside
      have haNext :
          a + 1 ≤ F.terminalTime := by
        omega
      have htailInside :
          a + 1 + L ≤ F.terminalTime := by
        omega
      have htailSync :
          ∀ t : ℕ, t < L →
            O.SynchronizedWindowAt
              (start + (a + 1) + t) q :=
        O.synchronizedInterval_tail
          (start := start)
          (q := q)
          (a := a)
          (L := L)
          hsync
      have htail :
          O.windowTwoSteps
                (start + (a + 1)) L +
              (F.difference
                (a + 1 + L)
                htailInside).depth =
            (F.difference
              (a + 1)
              haNext).depth := by
        simpa only [Nat.add_assoc] using
          ih
            (a := a + 1)
            htailInside
            htailSync
      exact
        F.synchronizedInterval_depth_balance_succ_of_tail
          a
          L
          hinside
          ha
          haNext
          htailInside
          (hsync 0 (Nat.zero_lt_succ L))
          htail

/-- contracting synchronized plateauの長さはwindow長未満。 -/
theorem synchronizedPlateau_length_lt_windowLength
    {O : OddOrbit} {start q : ℕ}
    {D₀ : O.WindowDifferenceData start q}
    (F : O.FiniteCaptureNormalizationData D₀)
    (P : SynchronizedPlateauInFirstDeferred F)
    (hcontract :
      3 ^ q <
        2 ^ O.windowTwoSteps (start + P.offset) q) :
    P.length < q := by
  have hoff : P.offset ≤ F.terminalTime := by
    exact le_trans (Nat.le_add_right P.offset P.length) P.inside
  let Dstart := F.difference P.offset hoff
  have hbalance :=
    F.synchronizedInterval_depth_balance
      P.offset P.length P.inside P.synchronized
  have hvalid : Valid (O.segmentWord (start + P.offset) P.length) :=
    (O.runs_segment (start + P.offset) P.length).valid
  have hlenSteps :
      P.length ≤ O.windowTwoSteps (start + P.offset) P.length := by
    simpa [OddOrbit.windowTwoSteps, oddSteps] using
      oddSteps_le_twoSteps hvalid
  have hstepsDepth :
      O.windowTwoSteps (start + P.offset) P.length ≤ Dstart.depth := by
    dsimp [Dstart]
    omega
  have hlenDepth : P.length ≤ Dstart.depth :=
    le_trans hlenSteps hstepsDepth
  have hoddPos : 0 < Dstart.oddPart := by
    rcases Dstart.oddPart_odd with ⟨u, hu⟩
    omega
  have hpowDepth : 2 ^ Dstart.depth ≤ 2 ^ Dstart.depth * Dstart.oddPart := by
    calc
      2 ^ Dstart.depth = 2 ^ Dstart.depth * 1 := by simp
      _ ≤ 2 ^ Dstart.depth * Dstart.oddPart :=
        Nat.mul_le_mul_left _ (by omega : 1 ≤ Dstart.oddPart)
  have hgap :=
    Dstart.twoPow_length_mul_gap_lt_threePow hcontract
  have hpow :
      2 ^ (q + P.length) < 3 ^ q := by
    calc
      2 ^ (q + P.length)
          ≤ 2 ^ (q + Dstart.depth) :=
            Nat.pow_le_pow_right (by omega) (by omega)
      _ = 2 ^ q * 2 ^ Dstart.depth := by rw [pow_add]
      _ ≤ 2 ^ q * (2 ^ Dstart.depth * Dstart.oddPart) :=
            Nat.mul_le_mul_left _ hpowDepth
      _ < 3 ^ q := hgap
  by_contra hnot
  have hqL : q ≤ P.length := Nat.le_of_not_gt hnot
  have hfourLe : 4 ^ q ≤ 2 ^ (q + P.length) := by
    calc
      4 ^ q = 2 ^ (q + q) := by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
        congr 1
        omega
      _ ≤ 2 ^ (q + P.length) :=
        Nat.pow_le_pow_right (by omega) (by omega)
  have hthreeLeFour : 3 ^ q ≤ 4 ^ q := by
    exact pow_le_pow_left' (by omega) q
  omega

end OddOrbit.FiniteCaptureNormalizationData

namespace FirstDeferredNormalizationTowerData

/-- no-critical項ではwindow長以上のsynchronized plateauは存在しない。 -/
theorem no_plateau_ge_windowLength_of_noCritical
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    {D : StandardNormalizationGeneratedObstructionTowerData hGap O}
    (T : FirstDeferredNormalizationTowerData D)
    (j : ℕ)
    (hNoCritical : NoCriticalCaptureInFirstDeferred (T.data j)) :
    ¬ ∃ P : SynchronizedPlateauInFirstDeferred (T.data j),
      T.windowLength j ≤ P.length := by
  rintro ⟨P, hlength⟩
  have hoffset_le_terminal :
      P.offset ≤ (T.data j).terminalTime := by
    exact le_trans
      (Nat.le_add_right P.offset P.length)
      P.inside
  have hcontract :=
    (T.data j).contracting_at_of_noCritical
      (by
        simpa [
          FirstDeferredNormalizationTowerData.start,
          FirstDeferredNormalizationTowerData.windowLength,
          StandardNormalizationGeneratedObstructionTowerData.start,
          StandardNormalizationGeneratedObstructionTowerData.windowLength,
          PolynomialPreparedFullWindowFamily.start
        ] using
          D.initial_threePow_lt_twoPow (T.select j))
      hNoCritical
      P.offset
      hoffset_le_terminal
  have hlt :
      P.length < T.windowLength j :=
    (T.data j).synchronizedPlateau_length_lt_windowLength
      P
      (by
        simpa [
          FirstDeferredNormalizationTowerData.start
        ] using hcontract)
  exact (Nat.not_lt_of_ge hlength) hlt

/-- no-critical項のterminal時刻は`(captureCount+1)*q`未満。 -/
theorem terminalTime_lt_captureSucc_mul_windowLength
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    {D : StandardNormalizationGeneratedObstructionTowerData hGap O}
    (T : FirstDeferredNormalizationTowerData D)
    (j : ℕ)
    (hNoCritical :
      NoCriticalCaptureInFirstDeferred (T.data j)) :
    T.terminalTime j <
      ((T.data j).captureCount + 1) *
        T.windowLength j := by
  let q := T.windowLength j
  have hq : 0 < q := by
    simpa [q] using T.windowLength_pos j
  by_contra hnot
  have hqPredSucc :
      (q - 1) + 1 = q :=
    Nat.sub_add_cancel hq
  have htimeBase :
      ((T.data j).captureCount + 1) * q ≤
        T.terminalTime j :=
    Nat.le_of_not_gt hnot
  have htime :
      ((T.data j).captureCount + 1) *
          ((q - 1) + 1) ≤
        (T.data j).terminalTime := by
    rw [hqPredSucc]
    simpa [
      q,
      FirstDeferredNormalizationTowerData.terminalTime
    ] using htimeBase
  obtain ⟨P, hP⟩ :=
    (T.data j).exists_synchronizedPlateau_of_mul_le_terminalTime
      (q - 1)
      htime
  apply
    T.no_plateau_ge_windowLength_of_noCritical
      j hNoCritical
  refine ⟨P, ?_⟩
  have hlength :
      (q - 1) + 1 ≤ P.length :=
    Nat.succ_le_of_lt hP
  rw [hqPredSucc] at hlength
  simpa [q] using hlength

/-- 任意の自然数は自身を指数とする2冪以下。 -/
lemma nat_le_twoPow_self (n : ℕ) :
    n ≤ 2 ^ n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [pow_succ]
      have hpos : 0 < 2 ^ n :=
        Nat.pow_pos (by omega)
      omega

/-- no-critical項のterminal時刻は`q*(q+1)`未満。 -/
theorem terminalTime_lt_windowLength_mul_succ
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    {D : StandardNormalizationGeneratedObstructionTowerData hGap O}
    (T : FirstDeferredNormalizationTowerData D)
    (j : ℕ)
    (hNoCritical : NoCriticalCaptureInFirstDeferred (T.data j)) :
    T.terminalTime j <
      T.windowLength j * (T.windowLength j + 1) := by
  let C := (T.data j).captureCount
  let q := T.windowLength j
  have hcount : 2 ^ C < q + 1 := by
    simpa [C, q] using
      T.twoPow_captureCount_lt_windowLength_succ j hNoCritical
  have hCle : C + 1 ≤ q + 1 := by
    have hCpow : C ≤ 2 ^ C :=
      nat_le_twoPow_self C
    have hClt : C < q + 1 :=
      lt_of_le_of_lt hCpow hcount
    exact Nat.succ_le_of_lt hClt
  have htime :=
    T.terminalTime_lt_captureSucc_mul_windowLength j hNoCritical
  calc
    T.terminalTime j < (C + 1) * q := by simpa [C, q] using htime
    _ ≤ (q + 1) * q := Nat.mul_le_mul_right q hCle
    _ = q * (q + 1) := by ring

/--
first-deferred towerの各項は開始時点でcontracting。
-/
theorem initial_contracting
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    {D : StandardNormalizationGeneratedObstructionTowerData hGap O}
    (T : FirstDeferredNormalizationTowerData D)
    (j : ℕ) :
    3 ^ T.windowLength j <
      2 ^ O.windowTwoSteps
        (T.start j)
        (T.windowLength j) := by
  simpa [
    FirstDeferredNormalizationTowerData.start,
    FirstDeferredNormalizationTowerData.windowLength,
    StandardNormalizationGeneratedObstructionTowerData.start,
    StandardNormalizationGeneratedObstructionTowerData.windowLength,
    PolynomialPreparedFullWindowFamily.start
  ] using
    D.initial_threePow_lt_twoPow (T.select j)

/--
no-criticalなtower項では、terminal以前の任意の時刻で
q-windowはcontractingのまま。
-/
theorem contracting_at_of_noCritical
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    {D : StandardNormalizationGeneratedObstructionTowerData hGap O}
    (T : FirstDeferredNormalizationTowerData D)
    (j t : ℕ)
    (hNoCritical :
      NoCriticalCaptureInFirstDeferred (T.data j))
    (ht :
      t ≤ T.terminalTime j) :
    3 ^ T.windowLength j <
      2 ^ O.windowTwoSteps
        (T.start j + t)
        (T.windowLength j) := by
  let F := T.data j
  have htF :
      t ≤ F.terminalTime := by
    simpa [
      F,
      FirstDeferredNormalizationTowerData.terminalTime
    ] using ht
  have h :=
    F.contracting_at_of_noCritical
      (T.initial_contracting j)
      hNoCritical
      t
      htF
  simpa [
    F,
    FirstDeferredNormalizationTowerData.start,
    FirstDeferredNormalizationTowerData.windowLength,
    StandardNormalizationGeneratedObstructionTowerData.start,
    StandardNormalizationGeneratedObstructionTowerData.windowLength,
    PolynomialPreparedFullWindowFamily.start,
    Nat.add_assoc
  ] using h

/--
no-criticalなtower項では、terminal以前の時刻`t`から
qだけ進めたscaled値は`3^q`以下しか増えない。
-/
theorem scaled_value_add_windowLength_le
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    {D : StandardNormalizationGeneratedObstructionTowerData hGap O}
    (T : FirstDeferredNormalizationTowerData D)
    (j t : ℕ)
    (hNoCritical :
      NoCriticalCaptureInFirstDeferred (T.data j))
    (ht :
      t ≤ T.terminalTime j) :
    2 ^ T.windowLength j *
        O.value
          (T.start j + t + T.windowLength j) ≤
      2 ^ T.windowLength j *
          O.value (T.start j + t) +
        3 ^ T.windowLength j := by
  let q := T.windowLength j
  let F := T.data j
  have htF :
      t ≤ F.terminalTime := by
    simpa [
      F,
      FirstDeferredNormalizationTowerData.terminalTime
    ] using ht
  let Dt :=
    F.difference t htF
  have hcontract :
      3 ^ q <
        2 ^ O.windowTwoSteps
          (T.start j + t)
          q := by
    simpa [q] using
      T.contracting_at_of_noCritical
        j t hNoCritical ht
  have hgap :
      2 ^ q *
          (2 ^ Dt.depth * Dt.oddPart) <
        3 ^ q := by
    apply Dt.twoPow_length_mul_gap_lt_threePow
    simpa [
      Dt,
      F,
      q,
      FirstDeferredNormalizationTowerData.start,
      FirstDeferredNormalizationTowerData.windowLength,
      StandardNormalizationGeneratedObstructionTowerData.start,
      StandardNormalizationGeneratedObstructionTowerData.windowLength,
      PolynomialPreparedFullWindowFamily.start,
      Nat.add_assoc
    ] using hcontract
  have hdifference :
      O.value (T.start j + t + q) =
        O.value (T.start j + t) +
          2 ^ Dt.depth * Dt.oddPart := by
    simpa [
      Dt,
      F,
      q,
      FirstDeferredNormalizationTowerData.start,
      FirstDeferredNormalizationTowerData.windowLength,
      StandardNormalizationGeneratedObstructionTowerData.start,
      StandardNormalizationGeneratedObstructionTowerData.windowLength,
      PolynomialPreparedFullWindowFamily.start,
      Nat.add_assoc
    ] using Dt.difference
  calc
    2 ^ q * O.value (T.start j + t + q)
        =
      2 ^ q *
        (O.value (T.start j + t) +
          2 ^ Dt.depth * Dt.oddPart) := by
            rw [hdifference]
    _ =
      2 ^ q * O.value (T.start j + t) +
        2 ^ q * (2 ^ Dt.depth * Dt.oddPart) := by
          ring
    _ ≤
      2 ^ q * O.value (T.start j + t) +
        3 ^ q := by
          exact
            Nat.add_le_add_left
              (Nat.le_of_lt hgap)
              _

/--
n回までのscaled値上界と次の一段上界から、
n+1回までのscaled値上界を得る。
-/
theorem scaled_value_mul_step
    {A B x₀ xₙ xₙ₁ n : ℕ}
    (hprev :
      A * xₙ ≤ A * x₀ + n * B)
    (hstep :
      A * xₙ₁ ≤ A * xₙ + B) :
    A * xₙ₁ ≤ A * x₀ + (n + 1) * B := by
  calc
    A * xₙ₁
        ≤ A * xₙ + B :=
      hstep
    _ ≤
      (A * x₀ + n * B) + B :=
        Nat.add_le_add_right hprev B
    _ =
      A * x₀ + (n + 1) * B := by
        ring

/--
contracting q-windowをq刻みで進めたときのscaled値上界。
-/
theorem scaled_value_add_mul_windowLength_le
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    {D : StandardNormalizationGeneratedObstructionTowerData hGap O}
    (T : FirstDeferredNormalizationTowerData D)
    (j r n : ℕ)
    (hNoCritical :
      NoCriticalCaptureInFirstDeferred (T.data j))
    (hsteps :
      ∀ m : ℕ, m < n →
        r + m * T.windowLength j ≤
          T.terminalTime j) :
    2 ^ T.windowLength j *
        O.value
          (T.start j +
            r +
            n * T.windowLength j) ≤
      2 ^ T.windowLength j *
          O.value (T.start j + r) +
        n * 3 ^ T.windowLength j := by
  let q := T.windowLength j
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hprev :
          2 ^ q *
              O.value
                (T.start j + r + n * q) ≤
            2 ^ q *
                O.value (T.start j + r) +
              n * 3 ^ q := by
        apply ih
        intro m hm
        exact hsteps m (Nat.lt_trans hm (Nat.lt_succ_self n))
      have hnInside :
          r + n * q ≤ T.terminalTime j := by
        exact hsteps n (Nat.lt_succ_self n)
      have hstep :
          2 ^ q *
              O.value
                (T.start j + r +
                  (n + 1) * q) ≤
            2 ^ q *
                O.value
                  (T.start j + r + n * q) +
              3 ^ q := by
        have h :=
          T.scaled_value_add_windowLength_le
            j
            (r + n * q)
            hNoCritical
            hnInside
        simpa [
          q,
          Nat.succ_mul,
          Nat.add_assoc,
          Nat.add_comm,
          Nat.add_left_comm
        ] using h
      exact
        scaled_value_mul_step
          (A := 2 ^ q)
          (B := 3 ^ q)
          (x₀ := O.value (T.start j + r))
          (xₙ :=
            O.value
              (T.start j + r + n * q))
          (xₙ₁ :=
            O.value
              (T.start j + r + (n + 1) * q))
          (n := n)
          hprev
          hstep

/-- no-critical項のterminal endpointはscaled固定多項式以下。 -/
theorem terminalEndpoint_scaled_le_of_noCritical
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    {D : StandardNormalizationGeneratedObstructionTowerData hGap O}
    (T : FirstDeferredNormalizationTowerData D)
    (j : ℕ)
    (hNoCritical : NoCriticalCaptureInFirstDeferred (T.data j)) :
    2 ^ T.windowLength j * T.terminalEndpoint j ≤
      (((polynomialPreparedFullWindowFamily hGap D.crossing).K + 1) *
        (T.windowLength j + 1) ^
          ((polynomialPreparedFullWindowFamily hGap D.crossing).A + 1)) *
        3 ^ T.windowLength j := by
  let q := T.windowLength j
  let t := T.terminalTime j
  let k := t / q
  let r := t % q
  let P := polynomialPreparedFullWindowFamily hGap D.crossing
  have hq : 0 < q := T.windowLength_pos j
  have hrq : r < q := by
    exact Nat.mod_lt _ hq
  have hdecomp : r + k * q = t := by
    simpa [r, k, Nat.mul_comm] using (Nat.mod_add_div t q)
  have htime := T.terminalTime_lt_windowLength_mul_succ j hNoCritical
  have hk : k + 1 ≤ q + 1 := by
    by_contra hnot
    have hqk : q + 1 ≤ k := by omega
    have hmul : q * k ≤ t := by
      simpa [k, Nat.mul_comm] using Nat.div_mul_le_self t q
    have : q * (q + 1) ≤ t :=
      le_trans (Nat.mul_le_mul_left q hqk) hmul
    exact Nat.not_le_of_gt htime this
  have hsteps :
      ∀ m : ℕ, m < k + 1 → r + m * q ≤ t := by
    intro m hm
    have hmk : m ≤ k := by omega
    calc
      r + m * q ≤ r + k * q :=
        Nat.add_le_add_left (Nat.mul_le_mul_right q hmk) r
      _ = t := hdecomp
  have hjump :=
    T.scaled_value_add_mul_windowLength_le
      j r (k + 1) hNoCritical
      (by simpa [q, t] using hsteps)
  have hendpointIndex :
      T.start j + r + (k + 1) * q =
        T.start j + t + q := by
    rw [← hdecomp]
    ring
  rw [hendpointIndex] at hjump
  have hresidue :
      2 ^ q * O.value (T.start j + r) ≤
        3 ^ q * (O.value (T.start j) + 1) := by
    simpa [q] using
      O.twoPow_full_mul_value_le_threePow_full
        (T.start j) hrq.le
  have hinitialLt :
      O.value (T.start j) < O.value (T.start j + q) := by
    let D0 := (T.data j).difference 0 (by simp)
    simpa [
      D0,
      q,
      FirstDeferredNormalizationTowerData.start,
      FirstDeferredNormalizationTowerData.windowLength,
      StandardNormalizationGeneratedObstructionTowerData.start,
      StandardNormalizationGeneratedObstructionTowerData.windowLength,
      PolynomialPreparedFullWindowFamily.start,
      Nat.add_assoc
    ] using D0.value_lt
  have hinitial :
      O.value (T.start j) + 1 ≤ P.K * (q + 1) ^ P.A := by
    have hendpoint := P.endpointBound (T.crossingIndex j)
    have hupper : O.value (T.start j + q) ≤ P.K * (q + 1) ^ P.A := by
      simpa [P, q,
        FirstDeferredNormalizationTowerData.start,
        FirstDeferredNormalizationTowerData.windowLength,
        FirstDeferredNormalizationTowerData.crossingIndex,
        StandardNormalizationGeneratedObstructionTowerData.start,
        StandardNormalizationGeneratedObstructionTowerData.windowLength,
        PolynomialPreparedFullWindowFamily.start,
        Nat.add_assoc] using hendpoint
    exact le_trans (Nat.succ_le_of_lt hinitialLt) hupper
  have hcoefficient :
      P.K * (q + 1) ^ P.A + (q + 1) ≤
        (P.K + 1) * (q + 1) ^ (P.A + 1) := by
    have hbase : 1 ≤ q + 1 := by omega
    have hpowMono :
        (q + 1) ^ P.A ≤ (q + 1) ^ (P.A + 1) :=
      Nat.pow_le_pow_right hbase (by omega)
    have hbasePow :
        q + 1 ≤ (q + 1) ^ (P.A + 1) := by
      rw [pow_succ]
      have hpowPos : 1 ≤ (q + 1) ^ P.A :=
        Nat.one_le_iff_ne_zero.mpr
          (Nat.ne_of_gt (Nat.pow_pos (by omega)))
      nlinarith
    calc
      P.K * (q + 1) ^ P.A + (q + 1)
          ≤ P.K * (q + 1) ^ (P.A + 1) +
              (q + 1) ^ (P.A + 1) :=
            Nat.add_le_add
              (Nat.mul_le_mul_left P.K hpowMono)
              hbasePow
      _ = (P.K + 1) * (q + 1) ^ (P.A + 1) := by ring
  have hscaled :
      2 ^ q * T.terminalEndpoint j ≤
        (P.K * (q + 1) ^ P.A + (q + 1)) * 3 ^ q := by
    calc
      2 ^ q * T.terminalEndpoint j
          = 2 ^ q * O.value (T.start j + t + q) := by
              rfl
      _ ≤ 2 ^ q * O.value (T.start j + r) +
            (k + 1) * 3 ^ q := by
              simpa [q, t] using hjump
      _ ≤ 3 ^ q * (O.value (T.start j) + 1) +
            (k + 1) * 3 ^ q :=
              Nat.add_le_add hresidue le_rfl
      _ ≤ 3 ^ q * (P.K * (q + 1) ^ P.A) +
            (q + 1) * 3 ^ q :=
              Nat.add_le_add
                (Nat.mul_le_mul_left (3 ^ q) hinitial)
                (Nat.mul_le_mul_right (3 ^ q) hk)
      _ = (P.K * (q + 1) ^ P.A + (q + 1)) * 3 ^ q := by ring
  calc
    2 ^ q * T.terminalEndpoint j
        ≤ (P.K * (q + 1) ^ P.A + (q + 1)) * 3 ^ q := hscaled
    _ ≤ ((P.K + 1) * (q + 1) ^ (P.A + 1)) * 3 ^ q :=
      Nat.mul_le_mul_right _ hcoefficient

end FirstDeferredNormalizationTowerData

end CollatzSecondLayer2
