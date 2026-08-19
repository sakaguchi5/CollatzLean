import CollatzLean.Collatz2.CSTMicro.CarryGeometry.MaximalProfileLayerIntervals
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.CriticalPowerFareyBeatty
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.CriticalChristoffelPacket

/-!
# Critical prefix / Ostrowski bridge

Stage 7 の arbitrary shifted interval `[a,b)` を、原点始まり Christoffel block と
直接同一視してはいけない。一般には

  beattyIndex (a+i) - beattyIndex a

は原点始まりの floor word そのものとは限らないからである。

そこで critical prefix numerator

  Ψ(n) = Σ_{k<n} 2^(beattyIndex k) 3^(n-1-k)

を導入し、まず exact endpoint identity

  2^(beattyIndex a) Φ[a,b]
    = Ψ(b) - 3^(b-a) Ψ(a)

を証明する。従って Stage 7 の layer interval contribution `C_j[a,b]` は

  2^(j+1) C_j[a,b]
    = 3^(m-b) Ψ(b) - 3^(m-a) Ψ(a)

へ変換できる。左の `2^(j+1)` は 3-adic unit なので、後段の odd-prime / 3-adic
解析では情報を失わない。

次に actual power-Farey convergent `(P_r,Q_r)` では既存 theorem

  beattyIndex i = floor(i Q_r / P_r),  i < P_r

を使い、

  Ψ(P_r) = criticalChristoffelPhi P_r Q_r

を exact に得る。

最後に consecutive Farey determinant から actual numerator sequence の recurrence

  P_(r+1) = P_(r-1) + a_r P_r
  Q_(r+1) = Q_(r-1) + a_r Q_r

を内部証明し、`a_r` を canonical partial quotient として登録する。
これにより任意の prefix length に対する bounded greedy Ostrowski expansion を構成する。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

open scoped BigOperators

/-! ## critical prefix and endpoint identity -/

/-- 原点から `n` odd-columns を読む critical prefix numerator。 -/
def criticalPrefixPhiZ
    (n : ℕ) : ℤ :=
  Finset.sum (Finset.range n)
    (fun k =>
      (2 : ℤ) ^ beattyIndex k *
        (3 : ℤ) ^ (n - 1 - k))

/-- Stage 7 の `criticalIntervalPhi` の整数環版。 -/
def criticalIntervalPhiZ
    (a b : ℕ) : ℤ :=
  Finset.sum (Finset.Ico a b)
    (fun k =>
      (2 : ℤ) ^ (beattyIndex k - beattyIndex a) *
        (3 : ℤ) ^ (b - 1 - k))

/-- `Ico a b` を offset range `0,...,b-a-1` へ移す。 -/
private theorem sum_Ico_eq_sum_range_sub
    {α : Type*}
    [AddCommMonoid α]
    (f : ℕ → α)
    {a b : ℕ}
    (hab : a ≤ b) :
    Finset.sum (Finset.Ico a b) f =
      Finset.sum (Finset.range (b - a))
        (fun r => f (a + r)) := by
  classical
  symm
  refine Finset.sum_bij (fun r _ => a + r) ?_ ?_ ?_ ?_
  · intro r hr
    have hrLt : r < b - a := Finset.mem_range.mp hr
    exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
  · intro r₁ hr₁ r₂ hr₂ hEq
    omega
  · intro k hk
    have hkIco := Finset.mem_Ico.mp hk
    refine ⟨k - a, Finset.mem_range.mpr ?_, ?_⟩
    · omega
    · omega
  · intro r hr
    rfl

/-- Nat 版 interval numerator を Int 版へ cast する。 -/
theorem criticalIntervalPhi_cast_eq
    (a b : ℕ) :
    (criticalIntervalPhi a b : ℤ) =
      criticalIntervalPhiZ a b := by
  classical
  unfold criticalIntervalPhi criticalIntervalPhiZ
  push_cast
  rfl

/-- Beatty index は weak monotone。 -/
private theorem beattyIndex_mono_of_le
    {a b : ℕ}
    (hab : a ≤ b) :
    beattyIndex a ≤ beattyIndex b := by
  by_cases hEq : a = b
  · subst b
    exact le_rfl
  · exact le_of_lt (beattyIndex_strictMono (by omega))

/--
critical prefix の exact endpoint decomposition。
-/
theorem criticalPrefixPhiZ_endpoint_decomposition
    {a b : ℕ}
    (hab : a ≤ b) :
    criticalPrefixPhiZ b =
      (3 : ℤ) ^ (b - a) * criticalPrefixPhiZ a +
        (2 : ℤ) ^ beattyIndex a * criticalIntervalPhiZ a b := by
  classical
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab
  simp only [Nat.add_sub_cancel_left]
  unfold criticalPrefixPhiZ
  rw [Finset.sum_range_add]
  have hLeft :
      Finset.sum (Finset.range a)
          (fun k =>
            (2 : ℤ) ^ beattyIndex k *
              (3 : ℤ) ^ (a + c - 1 - k)) =
        (3 : ℤ) ^ c *
          Finset.sum (Finset.range a)
            (fun k =>
              (2 : ℤ) ^ beattyIndex k *
                (3 : ℤ) ^ (a - 1 - k)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hkLt : k < a := Finset.mem_range.mp hk
    have hExp :
        a + c - 1 - k = c + (a - 1 - k) := by
      omega
    rw [hExp, pow_add]
    ring
  have hRightReindex :
      criticalIntervalPhiZ a (a + c) =
        Finset.sum (Finset.range c)
          (fun r =>
            (2 : ℤ) ^ (beattyIndex (a + r) - beattyIndex a) *
              (3 : ℤ) ^ (c - 1 - r)) := by
    unfold criticalIntervalPhiZ
    rw [sum_Ico_eq_sum_range_sub
      (fun k =>
        (2 : ℤ) ^ (beattyIndex k - beattyIndex a) *
          (3 : ℤ) ^ (a + c - 1 - k)) (by omega : a ≤ a + c)]
    simp only [Nat.add_sub_cancel_left]
    apply Finset.sum_congr rfl
    intro r hr
    have hrLt : r < c := Finset.mem_range.mp hr
    have hExp :
        a + c - 1 - (a + r) = c - 1 - r := by
      omega
    rw [hExp]
  have hRight :
      Finset.sum (Finset.range c)
          (fun r =>
            (2 : ℤ) ^ beattyIndex (a + r) *
              (3 : ℤ) ^ (a + c - 1 - (a + r))) =
        (2 : ℤ) ^ beattyIndex a * criticalIntervalPhiZ a (a + c) := by
    rw [hRightReindex, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    have hrLt : r < c := Finset.mem_range.mp hr
    have hBeta : beattyIndex a ≤ beattyIndex (a + r) :=
      beattyIndex_mono_of_le (by omega)
    have hBetaExp :
        beattyIndex (a + r) =
          beattyIndex a +
            (beattyIndex (a + r) - beattyIndex a) := by
      omega
    have hThreeExp :
        a + c - 1 - (a + r) = c - 1 - r := by
      omega
    have hBetaCancel :
        beattyIndex a +
            (beattyIndex (a + r) - beattyIndex a) -
          beattyIndex a =
        beattyIndex (a + r) - beattyIndex a := by
      omega
    rw [hBetaExp, hThreeExp, pow_add, hBetaCancel]
    ring
  rw [hLeft, hRight]

/-- shifted interval を二つの origin-prefix の差へ変換する。 -/
theorem criticalIntervalPhiZ_eq_endpoint_difference
    {a b : ℕ}
    (hab : a ≤ b) :
    (2 : ℤ) ^ beattyIndex a * criticalIntervalPhiZ a b =
      criticalPrefixPhiZ b -
        (3 : ℤ) ^ (b - a) * criticalPrefixPhiZ a := by
  have h := criticalPrefixPhiZ_endpoint_decomposition hab
  linarith

/-- Stage 7 の Nat interval numerator を直接 endpoint difference へ変換する。 -/
theorem criticalIntervalPhi_endpoint_difference
    {a b : ℕ}
    (hab : a ≤ b) :
    (2 : ℤ) ^ beattyIndex a * (criticalIntervalPhi a b : ℤ) =
      criticalPrefixPhiZ b -
        (3 : ℤ) ^ (b - a) * criticalPrefixPhiZ a := by
  rw [criticalIntervalPhi_cast_eq]
  exact criticalIntervalPhiZ_eq_endpoint_difference hab

/--
Stage 7 interval contribution の endpoint-prefix form。

  2^(j+1) C_j[a,b]
    = 3^(m-b) Ψ(b) - 3^(m-a) Ψ(a).
-/
theorem profileDyadicIntervalNumerator_endpoint_prefix
    {m j a b : ℕ}
    (hab : a ≤ b)
    (hbm : b ≤ m)
    (hj : j < beattyIndex a) :
    (2 : ℤ) ^ (j + 1) *
        (profileDyadicIntervalNumerator m j a b : ℤ) =
      (3 : ℤ) ^ (m - b) * criticalPrefixPhiZ b -
        (3 : ℤ) ^ (m - a) * criticalPrefixPhiZ a := by
  have hStage7 :=
    profileDyadicIntervalNumerator_eq_scaledCriticalIntervalPhi
      (m := m) (j := j) (a := a) (b := b) hbm hj
  have hStage7Z := congrArg (fun n : ℕ => (n : ℤ)) hStage7
  push_cast at hStage7Z
  have hTwoExp :
      (j + 1) + (beattyIndex a - j - 1) = beattyIndex a := by
    omega
  have hThreeExp :
      (m - b) + (b - a) = m - a := by
    omega
  have hEndpoint := criticalIntervalPhi_endpoint_difference (a := a) (b := b) hab
  rw [hStage7Z]
  calc
    (2 : ℤ) ^ (j + 1) *
          ((2 : ℤ) ^ (beattyIndex a - j - 1) *
            (3 : ℤ) ^ (m - b) *
            (criticalIntervalPhi a b : ℤ))
        =
      ((2 : ℤ) ^ (j + 1) *
          (2 : ℤ) ^ (beattyIndex a - j - 1)) *
        ((3 : ℤ) ^ (m - b) *
          (criticalIntervalPhi a b : ℤ)) := by
            ring
    _ =
      (2 : ℤ) ^ beattyIndex a *
        ((3 : ℤ) ^ (m - b) *
          (criticalIntervalPhi a b : ℤ)) := by
            rw [← pow_add, hTwoExp]
    _ =
      (3 : ℤ) ^ (m - b) *
        ((2 : ℤ) ^ beattyIndex a *
          (criticalIntervalPhi a b : ℤ)) := by
            ring
    _ =
      (3 : ℤ) ^ (m - b) *
        (criticalPrefixPhiZ b -
          (3 : ℤ) ^ (b - a) * criticalPrefixPhiZ a) := by
            rw [hEndpoint]
    _ =
      (3 : ℤ) ^ (m - b) * criticalPrefixPhiZ b -
        ((3 : ℤ) ^ (m - b) *
          (3 : ℤ) ^ (b - a)) *
          criticalPrefixPhiZ a := by
            ring
    _ =
      (3 : ℤ) ^ (m - b) * criticalPrefixPhiZ b -
        (3 : ℤ) ^ (m - a) *
          criticalPrefixPhiZ a := by
            rw [← pow_add, hThreeExp]

/--
Admissible profile の maximal layer interval では `j < beattyIndex a` が自動的に従うので、
endpoint-prefix formula を side condition なしで使える。
-/
theorem AdmissibleSturmianProfile.maximalLayerInterval_endpoint_prefix
    {m : ℕ}
    {h : ℕ → ℕ}
    (A : AdmissibleSturmianProfile m h)
    {j : ℕ}
    {ab : ℕ × ℕ}
    (hab : ab ∈ maximalProfileLayerIntervals m h j) :
    (2 : ℤ) ^ (j + 1) *
        (profileDyadicIntervalNumerator m j ab.1 ab.2 : ℤ) =
      (3 : ℤ) ^ (m - ab.2) * criticalPrefixPhiZ ab.2 -
        (3 : ℤ) ^ (m - ab.1) * criticalPrefixPhiZ ab.1 := by
  have hMax : IsMaximalProfileLayerInterval m h j ab :=
    (mem_maximalProfileLayerIntervals_iff.mp hab).2.2
  have haLtM : ab.1 < m :=
    lt_of_lt_of_le hMax.1 hMax.2.1
  have haSupport : ab.1 ∈ profileLayerSupport m h j :=
    hMax.mem_support le_rfl hMax.1
  have hLayer : j < h ab.1 :=
    (Finset.mem_filter.mp haSupport).2
  have hDepth : h ab.1 ≤ beattyIndex ab.1 :=
    A.depth_le haLtM
  have hjBeatty : j < beattyIndex ab.1 :=
    lt_of_lt_of_le hLayer hDepth
  exact
    profileDyadicIntervalNumerator_endpoint_prefix
      (a := ab.1) (b := ab.2)
      hMax.1.le hMax.2.1 hjBeatty

/-! ## actual convergent prefix = Christoffel phi -/

/-- additive fold を finite sum へ移す local bridge。 -/
private theorem foldl_range_add_eq_sum_local
    (n : ℕ)
    (f : ℕ → ℤ) :
    (List.range n).foldl (fun acc i => acc + f i) 0 =
      Finset.sum (Finset.range n) f := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [Finset.sum_range_succ, ih]

/-- explicit Christoffel fold の local finite-sum form。 -/
private theorem criticalChristoffelPhi_eq_sum_local
    (p q : ℕ) :
    criticalChristoffelPhi p q =
      Finset.sum (Finset.range p)
        (fun i =>
          (3 : ℤ) ^ (p - 1 - i) *
            (2 : ℤ) ^ ((i * q) / p)) := by
  unfold criticalChristoffelPhi
  exact foldl_range_add_eq_sum_local p
    (fun i =>
      (3 : ℤ) ^ (p - 1 - i) *
        (2 : ℤ) ^ ((i * q) / p))

/--
actual convergent height `P_r` では critical prefix numerator は Christoffel numerator そのもの。
-/
theorem actual_criticalPrefixPhiZ_eq_christoffelPhi
    {r : ℕ}
    (hr : 9 ≤ r) :
    criticalPrefixPhiZ (criticalPowerP r) =
      criticalChristoffelPhi (criticalPowerP r) (criticalPowerQ r) := by
  rw [criticalChristoffelPhi_eq_sum_local]
  unfold criticalPrefixPhiZ
  apply Finset.sum_congr rfl
  intro i hi
  have hiLt : i < criticalPowerP r := Finset.mem_range.mp hi
  rw [actual_beattyIndex_eq_div hr hiLt]
  ring

/-- existing `criticalChristoffelPhiAt` API への specialization。 -/
theorem actual_criticalPrefixPhiZ_eq_christoffelPhiAt
    {r : ℕ}
    (hr : 9 ≤ r) :
    criticalPrefixPhiZ (criticalPowerP r) =
      criticalChristoffelPhiAt actualCriticalContinuedFractionData r := by
  simpa [criticalChristoffelPhiAt, actualCriticalContinuedFractionData] using
    actual_criticalPrefixPhiZ_eq_christoffelPhi hr

/-! ## actual Farey recurrence and canonical partial quotients -/

/-- actual even pair の determinant orientation。 -/
theorem actualCriticalFareyDeterminant_even
    {r : ℕ}
    (hr : 9 ≤ r)
    (hEven : r % 2 = 0) :
    criticalPowerP r * criticalPowerQ (r + 1) + 1 =
      criticalPowerP (r + 1) * criticalPowerQ r := by
  have hBelow := (criticalPower_orientation r).1 hEven
  have hOdd : (r + 1) % 2 = 1 := by omega
  have hAbove := (criticalPower_orientation (r + 1)).2 hOdd
  have hCross :=
    CriticalPowerFraction.cross_lt_of_below_above hBelow hAbove
  have hCross' :
      criticalPowerP r * criticalPowerQ (r + 1) <
        criticalPowerP (r + 1) * criticalPowerQ r := by
    simpa [criticalPowerP, criticalPowerQ] using hCross
  rcases criticalPower_adjacent_next hr with h | h
  · simpa [criticalPowerP, criticalPowerQ] using h
  · have hRev :
        criticalPowerP (r + 1) * criticalPowerQ r + 1 =
          criticalPowerP r * criticalPowerQ (r + 1) := by
      simpa [criticalPowerP, criticalPowerQ] using h
    omega

/-- actual odd pair の determinant orientation。 -/
theorem actualCriticalFareyDeterminant_odd
    {r : ℕ}
    (hr : 9 ≤ r)
    (hOdd : r % 2 = 1) :
    criticalPowerP (r + 1) * criticalPowerQ r + 1 =
      criticalPowerP r * criticalPowerQ (r + 1) := by
  have hEven : (r + 1) % 2 = 0 := by omega
  have hBelow := (criticalPower_orientation (r + 1)).1 hEven
  have hAbove := (criticalPower_orientation r).2 hOdd
  have hCross :=
    CriticalPowerFraction.cross_lt_of_below_above hBelow hAbove
  have hCross' :
      criticalPowerP (r + 1) * criticalPowerQ r <
        criticalPowerP r * criticalPowerQ (r + 1) := by
    simpa [criticalPowerP, criticalPowerQ] using hCross
  rcases criticalPower_adjacent_next hr with h | h
  · have hFwd :
        criticalPowerP r * criticalPowerQ (r + 1) + 1 =
          criticalPowerP (r + 1) * criticalPowerQ r := by
      simpa [criticalPowerP, criticalPowerQ] using h
    omega
  · simpa [criticalPowerP, criticalPowerQ] using h

/-- index `r` の actual continued-fraction recurrence coefficient であること。 -/
def IsActualCriticalPartialQuotient
    (r a : ℕ) : Prop :=
  0 < a ∧
  criticalPowerP (r + 1) =
    criticalPowerP (r - 1) + a * criticalPowerP r ∧
  criticalPowerQ (r + 1) =
    criticalPowerQ (r - 1) + a * criticalPowerQ r

/-- initial finite table `2 ≤ r < 10` の recurrence coefficient。 -/
def actualCriticalInitialPartialQuotient
    (r : ℕ) : ℕ :=
  match r with
  | 2 => 1
  | 3 => 2
  | 4 => 2
  | 5 => 3
  | 6 => 1
  | 7 => 5
  | 8 => 2
  | 9 => 23
  | _ => 0

/-- finite initial range の recurrence。 -/
private theorem exists_actualCriticalPartialQuotient_initial
    {r : ℕ}
    (hr2 : 2 ≤ r)
    (hr10 : r < 10) :
    IsActualCriticalPartialQuotient r
      (actualCriticalInitialPartialQuotient r) := by
  unfold IsActualCriticalPartialQuotient
  interval_cases r <;>
    decide

/--
start 以降の連続する二つの determinant-one relation から、
中央 convergent に関する cross-difference identity を得る。
-/
private theorem actualCritical_crossDifference_large
    {r : ℕ}
    (hr : 10 ≤ r) :
    (criticalPowerP r : ℤ) *
        ((criticalPowerQ (r + 1) : ℤ) -
          (criticalPowerQ (r - 1) : ℤ)) =
      ((criticalPowerP (r + 1) : ℤ) -
          (criticalPowerP (r - 1) : ℤ)) *
        (criticalPowerQ r : ℤ) := by
  have hrPrev : 9 ≤ r - 1 := by
    omega
  have hmod : r % 2 = 0 ∨ r % 2 = 1 := by
    have hlt := Nat.mod_lt r (by decide : 0 < 2)
    omega
  rcases hmod with hEven | hOdd
  · have hPrevOdd : (r - 1) % 2 = 1 := by
      omega
    have hPrev :
        criticalPowerP r * criticalPowerQ (r - 1) + 1 =
          criticalPowerP (r - 1) * criticalPowerQ r := by
      simpa only [show r - 1 + 1 = r by omega] using
        actualCriticalFareyDeterminant_odd hrPrev hPrevOdd
    have hNext :
        criticalPowerP r * criticalPowerQ (r + 1) + 1 =
          criticalPowerP (r + 1) * criticalPowerQ r :=
      actualCriticalFareyDeterminant_even
        (by omega : 9 ≤ r) hEven
    have hPrevZ :=
      congrArg (fun n : ℕ => (n : ℤ)) hPrev
    have hNextZ :=
      congrArg (fun n : ℕ => (n : ℤ)) hNext
    push_cast at hPrevZ hNextZ
    have hPrevSolve :
        (criticalPowerP r : ℤ) *
            (criticalPowerQ (r - 1) : ℤ) =
          (criticalPowerP (r - 1) : ℤ) *
              (criticalPowerQ r : ℤ) - 1 := by
      linarith
    have hNextSolve :
        (criticalPowerP r : ℤ) *
            (criticalPowerQ (r + 1) : ℤ) =
          (criticalPowerP (r + 1) : ℤ) *
              (criticalPowerQ r : ℤ) - 1 := by
      linarith
    calc
      (criticalPowerP r : ℤ) *
            ((criticalPowerQ (r + 1) : ℤ) -
              (criticalPowerQ (r - 1) : ℤ))
          =
        (criticalPowerP r : ℤ) *
            (criticalPowerQ (r + 1) : ℤ) -
          (criticalPowerP r : ℤ) *
            (criticalPowerQ (r - 1) : ℤ) := by
              ring
      _ =
        ((criticalPowerP (r + 1) : ℤ) *
              (criticalPowerQ r : ℤ) - 1) -
          ((criticalPowerP (r - 1) : ℤ) *
              (criticalPowerQ r : ℤ) - 1) := by
              rw [hNextSolve, hPrevSolve]
      _ =
        ((criticalPowerP (r + 1) : ℤ) -
            (criticalPowerP (r - 1) : ℤ)) *
          (criticalPowerQ r : ℤ) := by
              ring
  · have hPrevEven : (r - 1) % 2 = 0 := by
      omega
    have hPrev :
        criticalPowerP (r - 1) * criticalPowerQ r + 1 =
          criticalPowerP r * criticalPowerQ (r - 1) := by
      simpa only [show r - 1 + 1 = r by omega] using
        actualCriticalFareyDeterminant_even hrPrev hPrevEven
    have hNext :
        criticalPowerP (r + 1) * criticalPowerQ r + 1 =
          criticalPowerP r * criticalPowerQ (r + 1) :=
      actualCriticalFareyDeterminant_odd
        (by omega : 9 ≤ r) hOdd
    have hPrevZ :=
      congrArg (fun n : ℕ => (n : ℤ)) hPrev
    have hNextZ :=
      congrArg (fun n : ℕ => (n : ℤ)) hNext
    push_cast at hPrevZ hNextZ
    have hPrevSolve :
        (criticalPowerP r : ℤ) *
            (criticalPowerQ (r - 1) : ℤ) =
          (criticalPowerP (r - 1) : ℤ) *
              (criticalPowerQ r : ℤ) + 1 := by
      linarith
    have hNextSolve :
        (criticalPowerP r : ℤ) *
            (criticalPowerQ (r + 1) : ℤ) =
          (criticalPowerP (r + 1) : ℤ) *
              (criticalPowerQ r : ℤ) + 1 := by
      linarith
    calc
      (criticalPowerP r : ℤ) *
            ((criticalPowerQ (r + 1) : ℤ) -
              (criticalPowerQ (r - 1) : ℤ))
          =
        (criticalPowerP r : ℤ) *
            (criticalPowerQ (r + 1) : ℤ) -
          (criticalPowerP r : ℤ) *
            (criticalPowerQ (r - 1) : ℤ) := by
              ring
      _ =
        ((criticalPowerP (r + 1) : ℤ) *
              (criticalPowerQ r : ℤ) + 1) -
          ((criticalPowerP (r - 1) : ℤ) *
              (criticalPowerQ r : ℤ) + 1) := by
              rw [hNextSolve, hPrevSolve]
      _ =
        ((criticalPowerP (r + 1) : ℤ) -
            (criticalPowerP (r - 1) : ℤ)) *
          (criticalPowerQ r : ℤ) := by
              ring


/--
前側の determinant-one relation から、中央 pair `(Q_r,P_r)` は coprime。
-/
private theorem actualCritical_middle_coprime_large
    {r : ℕ}
    (hr : 10 ≤ r) :
    IsCoprime
      (criticalPowerQ r : ℤ)
      (criticalPowerP r : ℤ) := by
  have hrPrev : 9 ≤ r - 1 := by
    omega
  have hmod : r % 2 = 0 ∨ r % 2 = 1 := by
    have hlt := Nat.mod_lt r (by decide : 0 < 2)
    omega
  rcases hmod with hEven | hOdd
  · have hPrevOdd : (r - 1) % 2 = 1 := by
      omega
    have hPrev :
        criticalPowerP r * criticalPowerQ (r - 1) + 1 =
          criticalPowerP (r - 1) * criticalPowerQ r := by
      simpa only [show r - 1 + 1 = r by omega] using
        actualCriticalFareyDeterminant_odd hrPrev hPrevOdd
    have hPrevZ :=
      congrArg (fun n : ℕ => (n : ℤ)) hPrev
    push_cast at hPrevZ
    refine
      ⟨(criticalPowerP (r - 1) : ℤ),
        -(criticalPowerQ (r - 1) : ℤ), ?_⟩
    calc
      (criticalPowerP (r - 1) : ℤ) *
            (criticalPowerQ r : ℤ) +
          -(criticalPowerQ (r - 1) : ℤ) *
            (criticalPowerP r : ℤ)
          =
        (criticalPowerP (r - 1) : ℤ) *
            (criticalPowerQ r : ℤ) -
          (criticalPowerP r : ℤ) *
            (criticalPowerQ (r - 1) : ℤ) := by
              ring
      _ = 1 := by
            linarith
  · have hPrevEven : (r - 1) % 2 = 0 := by
      omega
    have hPrev :
        criticalPowerP (r - 1) * criticalPowerQ r + 1 =
          criticalPowerP r * criticalPowerQ (r - 1) := by
      simpa only [show r - 1 + 1 = r by omega] using
        actualCriticalFareyDeterminant_even hrPrev hPrevEven
    have hPrevZ :=
      congrArg (fun n : ℕ => (n : ℤ)) hPrev
    push_cast at hPrevZ
    refine
      ⟨-(criticalPowerP (r - 1) : ℤ),
        (criticalPowerQ (r - 1) : ℤ), ?_⟩
    calc
      -(criticalPowerP (r - 1) : ℤ) *
            (criticalPowerQ r : ℤ) +
          (criticalPowerQ (r - 1) : ℤ) *
            (criticalPowerP r : ℤ)
          =
        (criticalPowerP r : ℤ) *
            (criticalPowerQ (r - 1) : ℤ) -
          (criticalPowerP (r - 1) : ℤ) *
            (criticalPowerQ r : ℤ) := by
              ring
      _ = 1 := by
            linarith


/--
Q-coordinate の差から positive recurrence coefficient を抽出する。

coprimality と cross-difference により

  Q_(r+1) - Q_(r-1) = a Q_r

となる正整数 `a` が存在する。
-/
private theorem exists_actualCriticalQ_recurrence_large
    {r : ℕ}
    (hr : 10 ≤ r) :
    ∃ a : ℕ,
      0 < a ∧
      criticalPowerQ (r + 1) =
        criticalPowerQ (r - 1) + a * criticalPowerQ r := by
  have hqPrevLt :
      criticalPowerQ (r - 1) < criticalPowerQ r :=
    criticalPowerQ_strict_previous (by omega)
  have hqNextLt :
      criticalPowerQ r < criticalPowerQ (r + 1) := by
    have h :=
      criticalPowerQ_strict_previous
        (j := r + 1) (by omega)
    simpa only [show r + 1 - 1 = r by omega] using h
  have hqPos :
      0 < criticalPowerQ r :=
    criticalPowerQ_pos r
  have hDiffZ :=
    actualCritical_crossDifference_large hr
  have hCoprime :=
    actualCritical_middle_coprime_large hr
  let dq : ℕ :=
    criticalPowerQ (r + 1) -
      criticalPowerQ (r - 1)
  have hdqPos : 0 < dq := by
    dsimp [dq]
    omega
  have hdqCast :
      (dq : ℤ) =
        (criticalPowerQ (r + 1) : ℤ) -
          (criticalPowerQ (r - 1) : ℤ) := by
    dsimp [dq]
    rw [Nat.cast_sub (by omega)]
  have hMulDiv :
      (criticalPowerQ r : ℤ) ∣
        (dq : ℤ) * (criticalPowerP r : ℤ) := by
    refine
      ⟨(criticalPowerP (r + 1) : ℤ) -
          (criticalPowerP (r - 1) : ℤ), ?_⟩
    rw [hdqCast]
    calc
      ((criticalPowerQ (r + 1) : ℤ) -
            (criticalPowerQ (r - 1) : ℤ)) *
          (criticalPowerP r : ℤ)
          =
        (criticalPowerP r : ℤ) *
          ((criticalPowerQ (r + 1) : ℤ) -
            (criticalPowerQ (r - 1) : ℤ)) := by
              ring
      _ =
        ((criticalPowerP (r + 1) : ℤ) -
            (criticalPowerP (r - 1) : ℤ)) *
          (criticalPowerQ r : ℤ) := hDiffZ
      _ =
        (criticalPowerQ r : ℤ) *
          ((criticalPowerP (r + 1) : ℤ) -
            (criticalPowerP (r - 1) : ℤ)) := by
              ring
  have hDiv :
      (criticalPowerQ r : ℤ) ∣ (dq : ℤ) :=
    hCoprime.dvd_of_dvd_mul_right hMulDiv
  rcases hDiv with ⟨tZ, htZ⟩
  have hqPosZ :
      (0 : ℤ) < criticalPowerQ r := by
    exact_mod_cast hqPos
  have hdqPosZ :
      (0 : ℤ) < dq := by
    exact_mod_cast hdqPos
  have htZPos : 0 < tZ := by
    by_contra hnot
    have htZLe : tZ ≤ 0 := le_of_not_gt hnot
    have hProdLe :
        (criticalPowerQ r : ℤ) * tZ ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos
        (le_of_lt hqPosZ) htZLe
    rw [← htZ] at hProdLe
    linarith
  let a : ℕ := tZ.toNat
  have haCast :
      (a : ℤ) = tZ := by
    dsimp [a]
    exact Int.toNat_of_nonneg (le_of_lt htZPos)
  have haPosZ :
      (0 : ℤ) < (a : ℤ) := by
    rw [haCast]
    exact htZPos
  have haPos : 0 < a := by
    exact_mod_cast haPosZ
  have hdqEqZ :
      (dq : ℤ) =
        (a : ℤ) * (criticalPowerQ r : ℤ) := by
    calc
      (dq : ℤ)
          =
        (criticalPowerQ r : ℤ) * tZ := htZ
      _ =
        (a : ℤ) * (criticalPowerQ r : ℤ) := by
          rw [haCast]
          ring
  have hqEqZ :
      (criticalPowerQ (r + 1) : ℤ) =
        (criticalPowerQ (r - 1) : ℤ) +
          (a : ℤ) * (criticalPowerQ r : ℤ) := by
    calc
      (criticalPowerQ (r + 1) : ℤ)
          =
        (criticalPowerQ (r - 1) : ℤ) +
          ((criticalPowerQ (r + 1) : ℤ) -
            (criticalPowerQ (r - 1) : ℤ)) := by
              ring
      _ =
        (criticalPowerQ (r - 1) : ℤ) +
          (dq : ℤ) := by
              rw [← hdqCast]
      _ =
        (criticalPowerQ (r - 1) : ℤ) +
          (a : ℤ) * (criticalPowerQ r : ℤ) := by
              rw [hdqEqZ]
  have hqEq :
      criticalPowerQ (r + 1) =
        criticalPowerQ (r - 1) +
          a * criticalPowerQ r := by
    exact_mod_cast hqEqZ
  exact ⟨a, haPos, hqEq⟩


/--
start 以降では Q-coordinate から得た recurrence coefficient が、
同じ係数で P-coordinate の recurrence も満たす。

したがって actual continued-fraction partial quotient が存在する。
-/
private theorem exists_actualCriticalPartialQuotient_large
    {r : ℕ}
    (hr : 10 ≤ r) :
    ∃ a : ℕ, IsActualCriticalPartialQuotient r a := by
  obtain ⟨a, haPos, hqEq⟩ :=
    exists_actualCriticalQ_recurrence_large hr
  have hDiffZ :=
    actualCritical_crossDifference_large hr
  have hqEqZ :=
    congrArg (fun n : ℕ => (n : ℤ)) hqEq
  push_cast at hqEqZ
  have hQDiffZ :
      (criticalPowerQ (r + 1) : ℤ) -
          (criticalPowerQ (r - 1) : ℤ) =
        (a : ℤ) * (criticalPowerQ r : ℤ) := by
    linarith
  have hEqMul :
      ((criticalPowerP (r + 1) : ℤ) -
          (criticalPowerP (r - 1) : ℤ)) *
          (criticalPowerQ r : ℤ) =
        ((criticalPowerP r : ℤ) * (a : ℤ)) *
          (criticalPowerQ r : ℤ) := by
    calc
      ((criticalPowerP (r + 1) : ℤ) -
            (criticalPowerP (r - 1) : ℤ)) *
          (criticalPowerQ r : ℤ)
          =
        (criticalPowerP r : ℤ) *
          ((criticalPowerQ (r + 1) : ℤ) -
            (criticalPowerQ (r - 1) : ℤ)) :=
              hDiffZ.symm
      _ =
        (criticalPowerP r : ℤ) *
          ((a : ℤ) * (criticalPowerQ r : ℤ)) := by
              rw [hQDiffZ]
      _ =
        ((criticalPowerP r : ℤ) * (a : ℤ)) *
          (criticalPowerQ r : ℤ) := by
              ring
  have hqNeZ :
      (criticalPowerQ r : ℤ) ≠ 0 := by
    have hqPos : 0 < criticalPowerQ r :=
      criticalPowerQ_pos r
    exact_mod_cast hqPos.ne'
  have hpDiffZ :
      (criticalPowerP (r + 1) : ℤ) -
          (criticalPowerP (r - 1) : ℤ) =
        (criticalPowerP r : ℤ) * (a : ℤ) := by
    exact mul_right_cancel₀ hqNeZ hEqMul
  have hpEqZ :
      (criticalPowerP (r + 1) : ℤ) =
        (criticalPowerP (r - 1) : ℤ) +
          (a : ℤ) * (criticalPowerP r : ℤ) := by
    calc
      (criticalPowerP (r + 1) : ℤ)
          =
        (criticalPowerP (r - 1) : ℤ) +
          ((criticalPowerP (r + 1) : ℤ) -
            (criticalPowerP (r - 1) : ℤ)) := by
              ring
      _ =
        (criticalPowerP (r - 1) : ℤ) +
          (criticalPowerP r : ℤ) * (a : ℤ) := by
              rw [hpDiffZ]
      _ =
        (criticalPowerP (r - 1) : ℤ) +
          (a : ℤ) * (criticalPowerP r : ℤ) := by
              ring
  have hpEq :
      criticalPowerP (r + 1) =
        criticalPowerP (r - 1) +
          a * criticalPowerP r := by
    exact_mod_cast hpEqZ
  exact ⟨a, haPos, hpEq, hqEq⟩

/-- actual recurrence coefficient は index 2 以降必ず存在する。 -/
theorem exists_actualCriticalPartialQuotient
    {r : ℕ}
    (hr : 2 ≤ r) :
    ∃ a : ℕ, IsActualCriticalPartialQuotient r a := by
  by_cases hsmall : r < 10
  · exact ⟨actualCriticalInitialPartialQuotient r,
      exists_actualCriticalPartialQuotient_initial hr hsmall⟩
  · exact exists_actualCriticalPartialQuotient_large (by omega)

/-- recurrence から canonical に選ぶ actual partial quotient。 -/
noncomputable def actualCriticalPartialQuotient
    (r : ℕ) : ℕ := by
  classical
  exact
    if hr : 2 ≤ r then
      Nat.find (exists_actualCriticalPartialQuotient hr)
    else
      0

/-- canonical partial quotient は recurrence を満たす。 -/
theorem actualCriticalPartialQuotient_spec
    {r : ℕ}
    (hr : 2 ≤ r) :
    IsActualCriticalPartialQuotient r
      (actualCriticalPartialQuotient r) := by
  classical
  unfold actualCriticalPartialQuotient
  simp only [dif_pos hr]
  exact Nat.find_spec (exists_actualCriticalPartialQuotient hr)

/-- canonical partial quotient は正。 -/
theorem actualCriticalPartialQuotient_pos
    {r : ℕ}
    (hr : 2 ≤ r) :
    0 < actualCriticalPartialQuotient r :=
  (actualCriticalPartialQuotient_spec hr).1

/-- actual `P_r` は index 2 以降 strict に増える。 -/
theorem criticalPowerP_strict_succ
    {r : ℕ}
    (hr : 2 ≤ r) :
    criticalPowerP r < criticalPowerP (r + 1) := by
  have hSpec :=
    actualCriticalPartialQuotient_spec hr
  have ha :
      1 ≤ actualCriticalPartialQuotient r := by
    exact Nat.succ_le_iff.mpr hSpec.1
  have hPrevPos :
      0 < criticalPowerP (r - 1) :=
    criticalPowerP_pos (by omega)
  have hMul :
      criticalPowerP r ≤
        actualCriticalPartialQuotient r * criticalPowerP r := by
    simpa [one_mul] using
      Nat.mul_le_mul_right (criticalPowerP r) ha
  rw [hSpec.2.1]
  omega

/-- `P_(R+2)` は少なくとも `R+1`。よって actual P-basis は cofinal。 -/
theorem criticalPowerP_add_two_linear_lower
    (R : ℕ) :
    R + 1 ≤ criticalPowerP (R + 2) := by
  induction R with
  | zero =>
      norm_num [
        criticalPowerP,
        criticalPowerConvergent,
        criticalInitialConvergent
      ]
  | succ R ih =>
      have hStrict0 :=
        criticalPowerP_strict_succ
          (r := R + 2) (by omega)
      have hStrict :
          criticalPowerP (R + 2) <
            criticalPowerP (R + 3) := by
        simpa only [show R + 2 + 1 = R + 3 by omega] using hStrict0
      change R + 2 ≤ criticalPowerP (R + 3)
      omega

/-- 任意 `n` は `P_(n+3)` より小さい。 -/
theorem self_lt_criticalPowerP_add_three
    (n : ℕ) :
    n < criticalPowerP (n + 3) := by
  have h := criticalPowerP_add_two_linear_lower (n + 1)
  simpa only [show n + 1 + 2 = n + 3 by omega] using
    (lt_of_lt_of_le (by omega : n < n + 2) h)

/-! ## bounded greedy Ostrowski expansion -/

/--
actual `P_2,P_3,...` basis による bounded Ostrowski expansion。
`R` は最高 basis `P_(R+2)` の level。

`step` の `max_remainder` は standard admissibility
「top digit が最大 partial quotient なら一つ下の digit は 0」
を remainder-level で保持する形。
-/
inductive ActualCriticalOstrowskiExpansion : (R n : ℕ) → Type
  | base
      (n : ℕ)
      (bound : n < criticalPowerP 3) :
      ActualCriticalOstrowskiExpansion 0 n
  | step
      {R n rem d : ℕ}
      (lower : ActualCriticalOstrowskiExpansion R rem)
      (bound : n < criticalPowerP (R + 4))
      (decomp : n = rem + d * criticalPowerP (R + 3))
      (digit_le : d ≤ actualCriticalPartialQuotient (R + 3))
      (max_remainder :
        d = actualCriticalPartialQuotient (R + 3) →
          rem < criticalPowerP (R + 2)) :
      ActualCriticalOstrowskiExpansion (R + 1) n

namespace ActualCriticalOstrowskiExpansion

/-- expansion が持つ next-basis upper bound。 -/
theorem bound
    {R n : ℕ}
    (E : ActualCriticalOstrowskiExpansion R n) :
    n < criticalPowerP (R + 3) := by
  cases E with
  | base n h => simpa using h
  | @step R n rem d lower h _ _ _ =>
      simpa [Nat.add_assoc] using h

/-- highest digit。 -/
def topDigit
    {R n : ℕ}
    (E : ActualCriticalOstrowskiExpansion R n) : ℕ :=
  match E with
  | .base n _ => n
  | .step (d := d) _ _ _ _ _ => d

/-- digits を high-to-low order で読む。 -/
def digits :
    {R n : ℕ} → ActualCriticalOstrowskiExpansion R n → List ℕ
  | 0, _, .base n _ => [n]
  | _ + 1, _, .step (d := d) lower _ _ _ _ =>
      d :: digits lower

@[simp] theorem digits_length
    {R n : ℕ}
    (E : ActualCriticalOstrowskiExpansion R n) :
    E.digits.length = R + 1 := by
  induction E with
  | base => simp [digits]
  | step lower _ _ _ _ ih =>
      simp [digits, ih, Nat.add_assoc]

/-- highest digit は canonical partial quotient 以下。 -/
theorem topDigit_le
    {R n : ℕ}
    (E : ActualCriticalOstrowskiExpansion R n) :
    E.topDigit ≤ actualCriticalPartialQuotient (R + 2) := by
  cases E with
  | base n h =>
      have hP3 : criticalPowerP 3 = 2 := by
        norm_num [criticalPowerP, criticalPowerConvergent,
          criticalInitialConvergent]
      have hA2 : actualCriticalPartialQuotient 2 = 1 := by
        have hs := actualCriticalPartialQuotient_spec (r := 2) (by omega)
        have hp2 : criticalPowerP 2 = 1 := by
          norm_num [criticalPowerP, criticalPowerConvergent,
            criticalInitialConvergent]
        have hp1 : criticalPowerP 1 = 1 := by
          norm_num [criticalPowerP, criticalPowerConvergent,
            criticalInitialConvergent]
        have hp3 : criticalPowerP 3 = 2 := by
          norm_num [criticalPowerP, criticalPowerConvergent,
            criticalInitialConvergent]
        unfold IsActualCriticalPartialQuotient at hs
        norm_num [hp1, hp2, hp3] at hs
        omega
      simp [topDigit, hA2, hP3] at h ⊢
      omega
  | @step R n rem d lower hb hd hle hmax =>
      simpa [topDigit, Nat.add_assoc] using hle

end ActualCriticalOstrowskiExpansion

/-- division window から quotient を一意に復元する。 -/
private theorem nat_div_eq_of_mul_le_lt_mul
    {N d k : ℕ}
    (hd : 0 < d)
    (hLo : k * d ≤ N)
    (hHi : N < (k + 1) * d) :
    N / d = k := by
  have hkLe : k ≤ N / d := by
    exact (Nat.le_div_iff_mul_le hd).2 hLo
  have hDivLt : N / d < k + 1 := by
    exact (Nat.div_lt_iff_lt_mul hd).2 hHi
  omega

/--
任意 `n < P_(R+3)` に bounded greedy Ostrowski expansion が存在する。
-/
theorem exists_actualCriticalOstrowskiExpansion
    (R n : ℕ)
    (hn : n < criticalPowerP (R + 3)) :
    Nonempty (ActualCriticalOstrowskiExpansion R n) := by
  induction R generalizing n with
  | zero =>
      exact ⟨.base n (by simpa using hn)⟩
  | succ R ih =>
      let B := criticalPowerP (R + 3)
      let A := actualCriticalPartialQuotient (R + 3)
      let d := n / B
      let rem := n % B
      have hBPos : 0 < B := by
        dsimp [B]
        exact criticalPowerP_pos (by omega)
      have hremLt : rem < B := by
        dsimp [rem]
        exact Nat.mod_lt n hBPos
      obtain ⟨lower⟩ := ih rem (by simpa [B] using hremLt)
      have hSpec :=
        actualCriticalPartialQuotient_spec (r := R + 3) (by omega)
      have hPrevLtB :
          criticalPowerP (R + 2) < B := by
        dsimp [B]
        exact criticalPowerP_strict_succ (r := R + 2) (by omega)
      have hNext :
          criticalPowerP (R + 4) =
            criticalPowerP (R + 2) + A * B := by
        simpa [A, B, Nat.add_assoc] using hSpec.2.1
      have hDivMul : d * B ≤ n := by
        dsimp [d]
        exact Nat.div_mul_le_self n B
      have hnNext :
          n < criticalPowerP (R + 4) := by
        simpa only [show R + 1 + 3 = R + 4 by omega] using hn
      have hdLe : d ≤ A := by
        by_contra hnot
        have hALtD : A < d := by
          omega
        have hABLe :
            (A + 1) * B ≤ d * B := by
          exact Nat.mul_le_mul_right B (by omega)
        have hNextLt :
            criticalPowerP (R + 4) < (A + 1) * B := by
          rw [hNext]
          nlinarith
        have hContra :
            (A + 1) * B < (A + 1) * B := by
          calc
            (A + 1) * B
                ≤ d * B := hABLe
            _ ≤ n := hDivMul
            _ < criticalPowerP (R + 4) := hnNext
            _ < (A + 1) * B := hNextLt
        exact (Nat.lt_irrefl _ hContra)
      have hDecomp : n = rem + d * B := by
        have h := Nat.mod_add_div n B
        dsimp [rem, d]
        simpa [Nat.mul_comm] using h.symm
      have hMax :
          d = A → rem < criticalPowerP (R + 2) := by
        intro hdEq
        rw [hdEq] at hDecomp
        rw [hNext] at hn
        omega
      exact
        ⟨.step lower
          (by simpa [Nat.add_assoc] using hn)
          (by simpa [B] using hDecomp)
          (by simpa [A] using hdLe)
          (by simpa [A] using hMax)⟩

/--
greedy expansion の top digit は ordinary division quotient そのもの。
-/
theorem ActualCriticalOstrowskiExpansion.topDigit_eq_div
    {R n : ℕ}
    (E : ActualCriticalOstrowskiExpansion R n) :
    E.topDigit = n / criticalPowerP (R + 2) := by
  cases E with
  | base n hb =>
      have hP2 : criticalPowerP 2 = 1 := by
        norm_num [criticalPowerP, criticalPowerConvergent,
          criticalInitialConvergent]
      simp [ActualCriticalOstrowskiExpansion.topDigit, hP2]
  | @step R n rem d lower hb hDecomp hDigit hMax =>
      have hBPos : 0 < criticalPowerP (R + 3) :=
        criticalPowerP_pos (by omega)
      have hRemLt := lower.bound
      have hLo :
          d * criticalPowerP (R + 3) ≤ n := by
        rw [hDecomp]
        omega
      have hHi :
          n < (d + 1) * criticalPowerP (R + 3) := by
        rw [hDecomp]
        nlinarith
      have hDiv := nat_div_eq_of_mul_le_lt_mul hBPos hLo hHi
      simpa [ActualCriticalOstrowskiExpansion.topDigit,
        Nat.add_assoc] using hDiv.symm

/-- 同じ bounded value の Ostrowski digit list は一意。 -/
theorem actualCriticalOstrowski_digits_unique
    {R n : ℕ}
    (E₁ E₂ : ActualCriticalOstrowskiExpansion R n) :
    E₁.digits = E₂.digits := by
  induction R generalizing n with
  | zero =>
      cases E₁ with
      | base =>
          cases E₂ with
          | base => rfl
  | succ R ih =>
      cases E₁ with
      | @step _ _ rem₁ d₁ lower₁ hb₁ hDec₁ hd₁ hm₁ =>
          cases E₂ with
          | @step _ _ rem₂ d₂ lower₂ hb₂ hDec₂ hd₂ hm₂ =>
              have hTop₁ :=
                ActualCriticalOstrowskiExpansion.topDigit_eq_div
                  (ActualCriticalOstrowskiExpansion.step
                    lower₁ hb₁ hDec₁ hd₁ hm₁)
              have hTop₂ :=
                ActualCriticalOstrowskiExpansion.topDigit_eq_div
                  (ActualCriticalOstrowskiExpansion.step
                    lower₂ hb₂ hDec₂ hd₂ hm₂)
              have hdEq : d₁ = d₂ := by
                simpa [ActualCriticalOstrowskiExpansion.topDigit,
                  Nat.add_assoc] using hTop₁.trans hTop₂.symm
              subst d₂
              have hRemEq : rem₁ = rem₂ := by
                omega
              subst rem₂
              have hLower := ih lower₁ lower₂
              simp [ActualCriticalOstrowskiExpansion.digits, hLower]

/-- bound proof から canonical digit list を選ぶ。 -/
noncomputable def boundedActualCriticalOstrowskiDigits
    (R n : ℕ)
    (hn : n < criticalPowerP (R + 3)) : List ℕ :=
  (Classical.choice
    (exists_actualCriticalOstrowskiExpansion R n hn)).digits

@[simp] theorem boundedActualCriticalOstrowskiDigits_length
    (R n : ℕ)
    (hn : n < criticalPowerP (R + 3)) :
    (boundedActualCriticalOstrowskiDigits R n hn).length = R + 1 := by
  unfold boundedActualCriticalOstrowskiDigits
  exact ActualCriticalOstrowskiExpansion.digits_length _

/-- 任意 prefix length `n` に canonical finite Ostrowski digit list を与える。 -/
noncomputable def actualCriticalOstrowskiDigits
    (n : ℕ) : List ℕ :=
  boundedActualCriticalOstrowskiDigits n n
    (self_lt_criticalPowerP_add_three n)

@[simp] theorem actualCriticalOstrowskiDigits_length
    (n : ℕ) :
    (actualCriticalOstrowskiDigits n).length = n + 1 := by
  unfold actualCriticalOstrowskiDigits
  exact boundedActualCriticalOstrowskiDigits_length _ _ _

end ExternalArithmetic
end CSTMicro
end Collatz2
