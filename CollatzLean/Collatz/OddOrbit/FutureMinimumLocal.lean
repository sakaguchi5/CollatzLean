import CollatzLean.Collatz.OddOrbit.HighExponent
import CollatzLean.Collatz.OddOrbit.FutureMinimumArithmetic
import CollatzLean.Collatz.Word.Geometry

/-!
# future minimum の局所 barrier / exponent cone / first high

future minimum からの actual dynamics に対して、
* barrier を割る一段は high exponent である
* offset t の exponent は t+1 以下
* value+1 depth は最初の high offset + 1 と一致
* first-high prefix は coefficient-expanding
を有限局所 API としてまとめる。
-/

namespace Collatz
namespace OddOrbit

/-- 一段が barrier `X` 以上に残るための exact inequality。 -/
theorem step_stays_above_barrier_iff
    {X delta e y : ℕ}
    (he : 2 ≤ e)
    (hstep : 2 ^ e * y = 3 * (X + delta) + 1) :
    X ≤ y ↔
      (2 ^ e - 3) * X ≤ 3 * delta + 1 := by
  have hpow : 3 ≤ 2 ^ e := by
    have hfour : 4 ≤ 2 ^ e := by
      simpa using Nat.pow_le_pow_right
        (by omega : 0 < (2 : ℕ)) he
    omega
  have hdecomp :
      2 ^ e = 3 + (2 ^ e - 3) := by
    omega
  constructor
  · intro hXy
    have hmul : 2 ^ e * X ≤ 2 ^ e * y :=
      Nat.mul_le_mul_left (2 ^ e) hXy
    rw [hstep, hdecomp] at hmul
    ring_nf at hmul
    omega
  · intro hbarrier
    have hmul : 2 ^ e * X ≤ 2 ^ e * y := by
      rw [hstep, hdecomp]
      ring_nf
      omega
    exact Nat.le_of_mul_le_mul_left hmul (Nat.pow_pos (by omega))

/-- barrier を初めて下へ割る一段の exponent は少なくとも2。 -/
theorem exponent_two_le_of_step_descends_below
    {X x e y : ℕ}
    (hx : X ≤ x)
    (hy : y < X)
    (hstep : 2 ^ e * y = 3 * x + 1) :
    2 ≤ e := by
  by_contra hnot
  have hcases : e = 0 ∨ e = 1 := by omega
  rcases hcases with rfl | rfl
  · norm_num at hstep
    omega
  · norm_num at hstep
    omega

/-- any odd-only orbit grows by at most a factor 2 per odd step。 -/
theorem value_add_le_twoPow_mul
    (O : OddOrbit) (n : ℕ) :
    ∀ t : ℕ,
      O.value (n + t) ≤ 2 ^ t * O.value n := by
  intro t
  induction t with
  | zero => simp
  | succ t ih =>
      have hePos := O.exponent_pos (n + t)
      obtain ⟨r, hr⟩ : ∃ r : ℕ, O.exponent (n + t) = r + 1 :=
        ⟨O.exponent (n + t) - 1, by omega⟩
      have hpow : 2 ≤ 2 ^ O.exponent (n + t) := by
        rw [hr, pow_succ]
        have hp : 0 < 2 ^ r := Nat.pow_pos (by omega)
        omega
      have hstep := O.step (n + t)
      have hcurPos := O.value_pos (n + t)
      have htwo :
          2 * O.value (n + t + 1) ≤
            4 * O.value (n + t) := by
        calc
          2 * O.value (n + t + 1)
              ≤ 2 ^ O.exponent (n + t) *
                  O.value (n + t + 1) :=
            Nat.mul_le_mul_right _ hpow
          _ = 3 * O.value (n + t) + 1 := hstep
          _ ≤ 4 * O.value (n + t) := by omega
      have hnext :
          O.value (n + t + 1) ≤ 2 * O.value (n + t) := by
        omega
      have hbound :
          O.value (n + t + 1) ≤
            2 * (2 ^ t * O.value n) :=
        le_trans hnext (Nat.mul_le_mul_left 2 ih)
      have hindex : n + (t + 1) = n + t + 1 := by omega
      rw [hindex]
      calc
        O.value (n + t + 1)
            ≤ 2 * (2 ^ t * O.value n) := hbound
        _ = 2 ^ (t + 1) * O.value n := by
          rw [pow_succ]
          ring

/-- unbounded future minimum is at least3。 -/
theorem FutureMinimumAt.three_le_value
    {O : OddOrbit} {n : ℕ}
    (hmin : O.FutureMinimumAt n) (hU : O.Unbounded) :
    3 ≤ O.value n := by
  have hpos := O.value_pos n
  have hodd := O.value_odd n
  have hneOne : O.value n ≠ 1 := by
    intro hOne
    have he := hmin.exponent_eq_one hU
    have hs := O.step n
    rw [he, hOne] at hs
    norm_num at hs
    rcases O.value_odd (n + 1) with ⟨k, hk⟩
    omega
  rcases hodd with ⟨k, hk⟩
  omega

/-- future minimum exponent cone: offset t の actual exponent は t+1 以下。 -/
theorem FutureMinimumAt.exponent_le_offset_add_one
    {O : OddOrbit} {n : ℕ}
    (hmin : O.FutureMinimumAt n) (hU : O.Unbounded) :
    ∀ t : ℕ, O.exponent (n + t) ≤ t + 1 := by
  intro t
  by_cases ht : t = 0
  · subst t
    simpa using (hmin.exponent_eq_one hU).le
  · have hsource3 := hmin.three_le_value hU
    have hcur := O.value_add_le_twoPow_mul n t
    have hsourceNext :
        O.value n ≤ O.value (n + t + 1) := by
      exact hmin _ (by omega)
    have hstep := O.step (n + t)
    have hscaledSource :
        2 ^ O.exponent (n + t) * O.value n ≤
          3 * (2 ^ t * O.value n) + 1 := by
      calc
        2 ^ O.exponent (n + t) * O.value n
            ≤ 2 ^ O.exponent (n + t) *
                O.value (n + t + 1) :=
          Nat.mul_le_mul_left _ hsourceNext
        _ = 3 * O.value (n + t) + 1 := hstep
        _ ≤ 3 * (2 ^ t * O.value n) + 1 :=
          Nat.add_le_add_right (Nat.mul_le_mul_left 3 hcur) 1
    by_contra hnot
    have heLarge : t + 2 ≤ O.exponent (n + t) := by omega
    have hpow :
        2 ^ (t + 2) ≤ 2 ^ O.exponent (n + t) :=
      Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) heLarge
    have hlower :
        2 ^ (t + 2) * O.value n ≤
          2 ^ O.exponent (n + t) * O.value n :=
      Nat.mul_le_mul_right (O.value n) hpow
    have hfour :
        2 ^ (t + 2) * O.value n =
          4 * (2 ^ t * O.value n) := by
      rw [show t + 2 = t + 2 by rfl, pow_add]
      norm_num
      ring
    rw [hfour] at hlower
    have hbase : 3 ≤ 2 ^ t * O.value n := by
      have hpowPos : 0 < 2 ^ t := Nat.pow_pos (by omega)
      have hpowOne : 1 ≤ 2 ^ t := by omega
      calc
        3 = 1 * 3 := by ring
        _ ≤ 2 ^ t * O.value n := Nat.mul_le_mul hpowOne hsource3
    omega

/-- length L の exponent-1 run transports `value+1` exactly。 -/
theorem value_add_one_scaled_of_one_run
    (O : OddOrbit) :
    ∀ {start L : ℕ},
      (∀ k : ℕ, k < L → O.exponent (start + k) = 1) →
      2 ^ L * (O.value (start + L) + 1) =
        3 ^ L * (O.value start + 1) := by
  intro start L
  induction L generalizing start with
  | zero =>
      intro _
      simp
  | succ L ih =>
      intro hones
      have hfirst : O.exponent start = 1 := by
        simpa using hones 0 (by omega)
      have htail :
          ∀ k : ℕ, k < L →
            O.exponent (start + 1 + k) = 1 := by
        intro k hk
        have h := hones (k + 1) (by omega)
        have hadd : start + (k + 1) = start + 1 + k := by
            omega
        rw [hadd] at h
        exact h
      have hstep :
          2 * (O.value (start + 1) + 1) =
            3 * (O.value start + 1) := by
        have hs := O.step start
        rw [hfirst] at hs
        norm_num at hs
        omega
      have hIH := ih (start := start + 1) htail
      have hindex : start + (L + 1) = start + 1 + L := by omega
      rw [hindex]
      calc
        2 ^ (L + 1) * (O.value (start + 1 + L) + 1)
            = 2 *
                (2 ^ L * (O.value (start + 1 + L) + 1)) := by
              rw [pow_succ]
              ring
        _ = 2 * (3 ^ L * (O.value (start + 1) + 1)) := by
              rw [hIH]
        _ = 3 ^ L * (2 * (O.value (start + 1) + 1)) := by ring
        _ = 3 ^ L * (3 * (O.value start + 1)) := by rw [hstep]
        _ = 3 ^ (L + 1) * (O.value start + 1) := by
              rw [pow_succ]
              ring

/-- future minimum 以後の最初の high exponent。 -/
structure FutureMinimumFirstHighData
    {O : OddOrbit} (n : ℕ) where
  offset : ℕ
  beforeHigh_one : ∀ k : ℕ, k < offset →
    O.exponent (n + k) = 1
  high : O.HighExponentAt (n + offset)

namespace FutureMinimumFirstHighData

/-- first high data can always be selected。 -/
noncomputable def firstHigh
    (O : OddOrbit) (n : ℕ) :
    FutureMinimumFirstHighData (O := O) n := by
  classical
  let hex := O.exists_highExponent_at_or_after n
  let m : ℕ := Classical.choose hex
  have hm : n ≤ m := by
    dsimp [m]
    exact (Classical.choose_spec hex).1
  have hhigh : O.HighExponentAt m := by
    dsimp [m]
    exact (Classical.choose_spec hex).2
  have hExists :
      ∃ L : ℕ, O.HighExponentAt (n + L) := by
    refine ⟨m - n, ?_⟩
    have hmn : n + (m - n) = m :=
      Nat.add_sub_of_le hm
    rw [hmn]
    exact hhigh
  let L : ℕ := Nat.find hExists
  have hLHigh :
      O.HighExponentAt (n + L) := by
    dsimp [L]
    exact Nat.find_spec hExists
  refine ⟨L, ?_, hLHigh⟩
  intro k hk
  have hnotHigh :
      ¬ O.HighExponentAt (n + k) := by
    intro hkHigh
    have hle : L ≤ k := by
      dsimp [L]
      exact Nat.find_min' hExists hkHigh
    omega
  have hpos :
      0 < O.exponent (n + k) :=
    O.exponent_pos (n + k)
  unfold HighExponentAt at hnotHigh
  omega

/-- source `+1` depth equals first-high offset + 1。 -/
theorem depth_eq_offset_add_one
    {O : OddOrbit} {n A u : ℕ}
    (H : FutureMinimumFirstHighData (O := O) n)
    (hA : TwoAdic.ExactFactor (O.value n + 1) A u) :
    A = H.offset + 1 := by
  obtain ⟨v, hv⟩ :=
    O.value_add_one_exactFactor_of_one_run_to_high
      (start := n) (L := H.offset)
      H.beforeHigh_one H.high
  exact TwoAdic.exponent_unique hA hv

/-- first high exponent is at most the source `+1` depth。 -/
theorem highExponent_le_depth
    {O : OddOrbit} {n A u : ℕ}
    (hmin : O.FutureMinimumAt n) (hU : O.Unbounded)
    (H : FutureMinimumFirstHighData (O := O) n)
    (hA : TwoAdic.ExactFactor (O.value n + 1) A u) :
    O.exponent (n + H.offset) ≤ A := by
  have hcone := hmin.exponent_le_offset_add_one hU H.offset
  have hdepth := H.depth_eq_offset_add_one hA
  omega

/-- first high step の reduced exact equation。 -/
theorem reducedEquation
    {O : OddOrbit} {n : ℕ}
    (H : FutureMinimumFirstHighData (O := O) n) :
    ∃ u : ℕ,
      TwoAdic.ExactFactor
        (O.value n + 1) (H.offset + 1) u ∧
      2 ^ (O.exponent (n + H.offset) - 1) *
          O.value (n + H.offset + 1) + 1 =
        3 ^ (H.offset + 1) * u := by
  obtain ⟨u, hu⟩ :=
    O.value_add_one_exactFactor_of_one_run_to_high
      (start := n) (L := H.offset)
      H.beforeHigh_one H.high
  refine ⟨u, hu, ?_⟩
  let e := O.exponent (n + H.offset)
  have heTwo : 2 ≤ e := by
    have hHigh : O.HighExponentAt (n + H.offset) :=
      H.high
    unfold HighExponentAt at hHigh
    dsimp [e]
    omega
  obtain ⟨s, hs⟩ : ∃ s : ℕ, e = s + 1 :=
    ⟨e - 1, by omega⟩
  have hones :=
    O.value_add_one_scaled_of_one_run
      (start := n) (L := H.offset) H.beforeHigh_one
  have hpowPos : 0 < 2 ^ H.offset := Nat.pow_pos (by omega)
  have hbefore :
      O.value (n + H.offset) + 1 =
        2 * 3 ^ H.offset * u := by
    have hscaled :
        2 ^ H.offset * (O.value (n + H.offset) + 1) =
          2 ^ H.offset * (2 * 3 ^ H.offset * u) := by
      calc
        2 ^ H.offset * (O.value (n + H.offset) + 1)
            = 3 ^ H.offset * (O.value n + 1) := hones
        _ = 3 ^ H.offset * (2 ^ (H.offset + 1) * u) := by
              rw [hu.1]
        _ = 2 ^ H.offset * (2 * 3 ^ H.offset * u) := by
              rw [pow_succ]
              ring
    exact Nat.mul_left_cancel hpowPos hscaled
  have hstep := O.step (n + H.offset)
  change 2 ^ e * O.value (n + H.offset + 1) =
      3 * O.value (n + H.offset) + 1 at hstep
  have htwice :
      2 * (2 ^ s * O.value (n + H.offset + 1) + 1) =
        2 * (3 ^ (H.offset + 1) * u) := by
    calc
      2 * (2 ^ s * O.value (n + H.offset + 1) + 1)
          = 2 ^ e * O.value (n + H.offset + 1) + 2 := by
            rw [hs, pow_succ]
            ring
      _ = 3 * O.value (n + H.offset) + 1 + 2 := by rw [hstep]
      _ = 3 * (O.value (n + H.offset) + 1) := by ring
      _ = 3 * (2 * 3 ^ H.offset * u) := by rw [hbefore]
      _ = 2 * (3 ^ (H.offset + 1) * u) := by
            rw [pow_succ]
            ring
  have hred :
      2 ^ s * O.value (n + H.offset + 1) + 1 =
        3 ^ (H.offset + 1) * u :=
    Nat.mul_left_cancel (by omega : 0 < (2 : ℕ)) htwice
  simpa [e, hs] using hred

private theorem twoSteps_segment_of_all_one
    (O : OddOrbit) {start L : ℕ}
    (hones : ∀ k : ℕ, k < L → O.exponent (start + k) = 1) :
    (O.segment start L).twoSteps = L := by
  induction L generalizing start with
  | zero => simp [OddOrbit.segment, Word.twoSteps]
  | succ L ih =>
      have hfirst : O.exponent start = 1 := by
        simpa using hones 0 (by omega)
      have htail :
          ∀ k : ℕ, k < L → O.exponent (start + 1 + k) = 1 := by
        intro k hk
        have h := hones (k + 1) (by omega)
        have hadd : start + (k + 1) = start + 1 + k := by
          omega
        rw [hadd] at h
        exact h
      rw [O.segment_succ]
      simp [Word.twoSteps_cons, hfirst, ih htail,Nat.add_comm]

/-- first-high prefix の total two-steps。 -/
theorem firstHighPrefix_twoSteps
    {O : OddOrbit} {n : ℕ}
    (H : FutureMinimumFirstHighData (O := O) n) :
    (O.segment n (H.offset + 1)).twoSteps =
      H.offset + O.exponent (n + H.offset) := by
  have honeSegment :
      ∀ (i L : ℕ),
        (∀ k : ℕ, k < L → O.exponent (i + k) = 1) →
        (O.segment i L).twoSteps = L := by
    intro i L hOne
    induction L generalizing i with
    | zero =>
        simp
    | succ L ih =>
        rw [O.segment_succ]
        simp only [Word.twoSteps_cons]
        have hhead :
            O.exponent i = 1 := by
          simpa using hOne 0 (by omega)
        have htail :
            ∀ k : ℕ,
              k < L →
                O.exponent (i + 1 + k) = 1 := by
          intro k hk
          have h :=
            hOne (k + 1) (by omega)
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
        rw [hhead]
        rw [ih (i := i + 1) htail]
        omega
  have hprefix :
      (O.segment n H.offset).twoSteps = H.offset := by
    apply honeSegment n H.offset
    intro k hk
    exact H.beforeHigh_one k hk
  rw [O.segment_add n H.offset 1]
  rw [Word.twoSteps_append, hprefix]
  simp

/--
future minimum の first-high prefix is necessarily coefficient-expanding。
-/
theorem prefixExpanding
    {O : OddOrbit} {n : ℕ}
    (hmin : O.FutureMinimumAt n) (hU : O.Unbounded)
    (H : FutureMinimumFirstHighData (O := O) n) :
    (O.segment n (H.offset + 1)).Expanding := by
  obtain ⟨u, hu, hred⟩ := H.reducedEquation
  let L := H.offset
  let e := O.exponent (n + L)
  let X := O.value n
  let Z := O.value (n + L + 1)
  have heTwo : 2 ≤ e := by
    have hHigh :
        O.HighExponentAt (n + H.offset) :=
      H.high
    unfold HighExponentAt at hHigh
    dsimp [e, L]
    exact hHigh
  have hZXle : X ≤ Z := by
    dsimp [X, Z, L]
    exact hmin _ (by omega)
  have hZXne : X ≠ Z := by
    dsimp [X, Z, L]
    exact O.value_ne_of_lt_of_unbounded hU (by omega)
  have hZX : X < Z := by omega
  let d := Z - X
  have hdPos : 0 < d := by dsimp [d]; omega
  have hZ : Z = X + d := by
    dsimp [d]
    rw [Nat.add_comm]
    exact (Nat.sub_add_cancel hZX.le).symm
  have hsource : X + 1 = 2 ^ (L + 1) * u := by
    simpa [X, L] using hu.1
  have hred' :
      2 ^ (e - 1) * Z + 1 = 3 ^ (L + 1) * u := by
    simpa [e, X, Z, L] using hred
  have htwoSteps := H.firstHighPrefix_twoSteps
  have hoddSteps :
      (O.segment n (H.offset + 1)).oddSteps = H.offset + 1 := by
    simp [Word.oddSteps]
  unfold Word.Expanding
  rw [htwoSteps, hoddSteps]
  change 2 ^ (L + e) < 3 ^ (L + 1)
  by_contra hnot
  have hGE : 3 ^ (L + 1) ≤ 2 ^ (L + e) := Nat.le_of_not_gt hnot
  let G := 2 ^ (L + e) - 3 ^ (L + 1)
  have hGsum :
      3 ^ (L + 1) + G = 2 ^ (L + e) := by
    dsimp [G]
    exact Nat.add_sub_of_le hGE
  have hpow :
      2 ^ (L + e) = 2 ^ (L + 1) * 2 ^ (e - 1) := by
    have hexp : L + e = (L + 1) + (e - 1) := by omega
    rw [hexp, pow_add]
  let a := 2 ^ (e - 1)
  have haPos : 0 < a := Nat.pow_pos (by omega)
  have hredA :
      a * Z + 1 = 3 ^ (L + 1) * u := by
    simpa [a] using hred'
  have hpowA :
      2 ^ (L + e) = 2 ^ (L + 1) * a := by
    simpa [a] using hpow
  have hmaster :
      a * Z + 1 + G * u = a * (X + 1) := by
    calc
      a * Z + 1 + G * u
          = 3 ^ (L + 1) * u + G * u := by
            rw [hredA]
      _ = (3 ^ (L + 1) + G) * u := by ring
      _ = 2 ^ (L + e) * u := by rw [hGsum]
      _ = (2 ^ (L + 1) * a) * u := by rw [hpowA]
      _ = a * (2 ^ (L + 1) * u) := by ring
      _ = a * (X + 1) := by rw [← hsource]
  have hcancel :
      a * X + (a * d + 1 + G * u) =
        a * X + a := by
    calc
      a * X + (a * d + 1 + G * u)
          = a * Z + 1 + G * u := by rw [hZ]; ring
      _ = a * (X + 1) := hmaster
      _ = a * X + a := by ring
  have heq : a * d + 1 + G * u = a :=
    Nat.add_left_cancel hcancel
  have had : a ≤ a * d := by
    have hdOne : 1 ≤ d := by omega
    simpa using Nat.mul_le_mul_left a hdOne
  omega

end FutureMinimumFirstHighData

end OddOrbit
end Collatz
