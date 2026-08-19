import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.CriticalChristoffelPacket
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.CriticalPowerFarey

/-!
# Raw Christoffel Wronskian

critical convergent `(p_j,q_j)` に対して

  φ_j = criticalChristoffelPhiAt D j
  Γ_j = 2^q_j - 3^p_j

と置く。

raw Wronskian

  W_j = φ_j Γ_(j+1) - φ_(j+1) Γ_j

は、前段の議論で現れた two-block determinant そのもの。
このファイルでは

* raw gap / raw Wronskian / affine defect を explicit に定義する。
* affine defect から common parameter が消える exact Wronskian identity を証明する。
* concatenation 型の positive linear update に対する determinant transport を証明する。
* Farey determinant-one pair に対する Christoffel mediant recurrence を証明する。
* Stern--Brocot の減算帰納から generic raw Wronskian law を証明する。
* actual power-Farey sequence に対する `CriticalRawChristoffelWronskianLaw` を構成する。

したがって、このファイル以降 raw Wronskian law は追加 certificate ではなく、
actual power-Farey / Christoffel arithmetic から得られる theorem になる。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

open scoped BigOperators

/-- critical convergent の signed raw power gap `2^q - 3^p`。 -/
def criticalRawPowerGap
    (D : CriticalContinuedFractionData)
    (j : ℕ) : ℤ :=
  (2 : ℤ) ^ D.q j - (3 : ℤ) ^ D.p j

/-- consecutive critical Christoffel blocks の raw Wronskian。 -/
def criticalRawChristoffelWronskianNext
    (D : CriticalContinuedFractionData)
    (j : ℕ) : ℤ :=
  criticalChristoffelPhiAt D j * criticalRawPowerGap D (j + 1) -
    criticalChristoffelPhiAt D (j + 1) * criticalRawPowerGap D j

/-- block `j` の affine defect `φ_j - Γ_j*y`。 -/
def criticalRawChristoffelDefect
    (D : CriticalContinuedFractionData)
    (j : ℕ)
    (y : ℤ) : ℤ :=
  criticalChristoffelPhiAt D j - criticalRawPowerGap D j * y

/--
二つの affine defect の cross combination では common parameter `y` が exact に消え、
raw Wronskian だけが残る。
-/
theorem criticalRawChristoffelDefect_cross_eq_wronskian
    (D : CriticalContinuedFractionData)
    (j : ℕ)
    (y : ℤ) :
    criticalRawPowerGap D (j + 1) *
          criticalRawChristoffelDefect D j y -
        criticalRawPowerGap D j *
          criticalRawChristoffelDefect D (j + 1) y =
      criticalRawChristoffelWronskianNext D j := by
  unfold criticalRawChristoffelDefect
    criticalRawChristoffelWronskianNext
  ring

/-! ## generic two-block determinant transport -/

/--
`W = a*U + b*V` という同じ linear update を numerator / gap の両方に施すと、
left-vs-new determinant は `b` 倍になる。
-/
theorem rawWronskian_right_linear_transport
    {AU AV AW GU GV GW a b : ℤ}
    (hA : AW = a * AU + b * AV)
    (hG : GW = a * GU + b * GV) :
    AU * GW - AW * GU =
      b * (AU * GV - AV * GU) := by
  rw [hA, hG]
  ring

/--
同じ linear update に対し、new-vs-right determinant は `a` 倍になる。
-/
theorem rawWronskian_left_linear_transport
    {AU AV AW GU GV GW a b : ℤ}
    (hA : AW = a * AU + b * AV)
    (hG : GW = a * GU + b * GV) :
    AW * GV - AV * GW =
      a * (AU * GV - AV * GU) := by
  rw [hA, hG]
  ring

/--
Christoffel/Farey concatenationで期待する specialization。

numerator と gap がとも

  new = 3^p * left + 2^q * right

で更新されるなら、left-vs-new Wronskian は `2^q` 倍。
-/
theorem rawWronskian_christoffel_right_transport
    {AU AV AW GU GV GW : ℤ}
    {p q : ℕ}
    (hA :
      AW = (3 : ℤ) ^ p * AU + (2 : ℤ) ^ q * AV)
    (hG :
      GW = (3 : ℤ) ^ p * GU + (2 : ℤ) ^ q * GV) :
    AU * GW - AW * GU =
      (2 : ℤ) ^ q * (AU * GV - AV * GU) := by
  exact rawWronskian_right_linear_transport hA hG

/--
同じ Christoffel/Farey concatenationで new-vs-right Wronskian は `3^p` 倍。
-/
theorem rawWronskian_christoffel_left_transport
    {AU AV AW GU GV GW : ℤ}
    {p q : ℕ}
    (hA :
      AW = (3 : ℤ) ^ p * AU + (2 : ℤ) ^ q * AV)
    (hG :
      GW = (3 : ℤ) ^ p * GU + (2 : ℤ) ^ q * GV) :
    AW * GV - AV * GW =
      (3 : ℤ) ^ p * (AU * GV - AV * GU) := by
  exact rawWronskian_left_linear_transport hA hG

/-! ## Farey-neighbor Christoffel recursion -/

/-- ordinary pair `(p,q)` の signed power gap。 -/
private def rawChristoffelPowerGapPQ
    (p q : ℕ) : ℤ :=
  (2 : ℤ) ^ q - (3 : ℤ) ^ p

/-- ordinary two-pair raw Wronskian。 -/
private def rawChristoffelWronskianPQ
    (p q r s : ℕ) : ℤ :=
  criticalChristoffelPhi p q * rawChristoffelPowerGapPQ r s -
    criticalChristoffelPhi r s * rawChristoffelPowerGapPQ p q

/-- `criticalChristoffelPhi` の一 summand。 -/
private def criticalChristoffelTerm
    (p q i : ℕ) : ℤ :=
  (3 : ℤ) ^ (p - 1 - i) *
    (2 : ℤ) ^ ((i * q) / p)

/-- additive fold を `Finset.range` sum へ移す。 -/
private theorem foldl_range_add_eq_sum
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

/-- explicit Christoffel fold を普通の finite sum として読む。 -/
private theorem criticalChristoffelPhi_eq_sum
    (p q : ℕ) :
    criticalChristoffelPhi p q =
      Finset.sum (Finset.range p)
        (fun i => criticalChristoffelTerm p q i) := by
  unfold criticalChristoffelPhi
  exact foldl_range_add_eq_sum p
    (fun i => criticalChristoffelTerm p q i)

/--
`k*d <= N < (k+1)*d` から `N/d = k` を復元する elementary division lemma。
-/
private theorem nat_div_eq_of_mul_le_lt_mul
    {N d k : ℕ}
    (hd : 0 < d)
    (hlo : k * d ≤ N)
    (hi : N < (k + 1) * d) :
    N / d = k := by
  have hmod := Nat.mod_lt N hd
  have hdecomp := Nat.mod_add_div N d
  have hqLower : (N / d) * d ≤ N := by
    rw [Nat.mul_comm]
    omega
  have hqUpper : N < (N / d + 1) * d := by
    calc
      N = N % d + d * (N / d) := hdecomp.symm
      _ < d + d * (N / d) :=
        Nat.add_lt_add_right hmod (d * (N / d))
      _ = (N / d + 1) * d := by ring
  apply Nat.le_antisymm
  · by_contra hnot
    have hk : k < N / d := by omega
    have hmul : (k + 1) * d ≤ (N / d) * d :=
      Nat.mul_le_mul_right d (by omega)
    omega
  · by_contra hnot
    have hk : N / d < k := by omega
    have hmul : (N / d + 1) * d ≤ k * d :=
      Nat.mul_le_mul_right d (by omega)
    omega

/--
Farey determinant `p*s+1=r*q` の下で、mediant の先頭 `r` 項の floor は
high-side floor と一致する。
-/
private theorem farey_mediant_floor_left
    {p q r s i : ℕ}
    (hp : 0 < p)
    (hr : 0 < r)
    (hdet : p * s + 1 = r * q)
    (hi : i < r) :
    (i * (q + s)) / (p + r) =
      (i * s) / r := by
  let a := (i * s) / r
  let t := (i * s) % r
  have ht : t < r := by
    simpa [t] using Nat.mod_lt (i * s) hr
  have hdiv : t + r * a = i * s := by
    simpa [a, t] using Nat.mod_add_div (i * s) r
  have hdetZ :
      (r : ℤ) * q - (p : ℤ) * s = 1 := by
    have h :
        (p : ℤ) * s + 1 = (r : ℤ) * q := by
      exact_mod_cast hdet
    linarith
  have hdivZ :
      (i : ℤ) * s - (r : ℤ) * a = t := by
    have h :
        (t : ℤ) + (r : ℤ) * a = (i : ℤ) * s := by
      exact_mod_cast hdiv
    linarith
  have hidZ :
      (r : ℤ) * ((i : ℤ) * ((q : ℤ) + s)) =
        (r : ℤ) * ((a : ℤ) * ((p : ℤ) + r)) +
          ((p : ℤ) + r) * t + i := by
    linear_combination
      (i : ℤ) * hdetZ + ((p : ℤ) + r) * hdivZ
  have hid :
      r * (i * (q + s)) =
        r * (a * (p + r)) + (p + r) * t + i := by
    exact_mod_cast hidZ
  have hlo : a * (p + r) ≤ i * (q + s) := by
    by_contra hnot
    have hlt : i * (q + s) < a * (p + r) := by omega
    have hmul := (Nat.mul_lt_mul_left hr).2 hlt
    omega
  have hrem : (p + r) * t + i < r * (p + r) := by
    calc
      (p + r) * t + i <
          (p + r) * t + (p + r) := by
        exact Nat.add_lt_add_left (by omega) _
      _ = (p + r) * (t + 1) := by ring
      _ ≤ (p + r) * r :=
        Nat.mul_le_mul_left (p + r) (by omega)
      _ = r * (p + r) := by ring
  have hmulUpper :
      r * (i * (q + s)) <
        r * ((a + 1) * (p + r)) := by
    calc
      r * (i * (q + s)) =
          r * (a * (p + r)) + (p + r) * t + i := hid
      _ < r * (a * (p + r)) + r * (p + r) := by
        simpa [Nat.add_assoc] using
          Nat.add_lt_add_left hrem (r * (a * (p + r)))
      _ = r * ((a + 1) * (p + r)) := by ring
  have hiUpper : i * (q + s) < (a + 1) * (p + r) :=
    (Nat.mul_lt_mul_left hr).1 hmulUpper
  exact nat_div_eq_of_mul_le_lt_mul (by omega) hlo hiUpper

/--
Farey mediant の後半 `p` 項では floor が
`s + floor(i*q/p)` に exact shift する。
-/
private theorem farey_mediant_floor_right
    {p q r s i : ℕ}
    (hp : 0 < p)
    (hr : 0 < r)
    (hdet : p * s + 1 = r * q)
    (hi : i < p) :
    ((r + i) * (q + s)) / (p + r) =
      s + (i * q) / p := by
  let a := (i * q) / p
  let t := (i * q) % p
  have ht : t < p := by
    simpa [t] using Nat.mod_lt (i * q) hp
  have hdiv : t + p * a = i * q := by
    simpa [a, t] using Nat.mod_add_div (i * q) p
  have hdetZ :
      (r : ℤ) * q - (p : ℤ) * s = 1 := by
    have h :
        (p : ℤ) * s + 1 = (r : ℤ) * q := by
      exact_mod_cast hdet
    linarith
  have hdivZ :
      (i : ℤ) * q - (p : ℤ) * a = t := by
    have h :
        (t : ℤ) + (p : ℤ) * a = (i : ℤ) * q := by
      exact_mod_cast hdiv
    linarith
  have hsubZ :
      ((p - i : ℕ) : ℤ) = (p : ℤ) - (i : ℤ) := by
    rw [Nat.cast_sub (by omega)]
  have hidZ :
      (p : ℤ) *
          (((r : ℤ) + i) * ((q : ℤ) + s)) =
        (p : ℤ) *
            (((s : ℤ) + a) * ((p : ℤ) + r)) +
          ((p - i : ℕ) : ℤ) +
          ((p : ℤ) + r) * t := by
    rw [hsubZ]
    linear_combination
      ((p : ℤ) - i) * hdetZ +
        ((p : ℤ) + r) * hdivZ
  have hid :
      p * ((r + i) * (q + s)) =
        p * ((s + a) * (p + r)) +
          (p - i) + (p + r) * t := by
    exact_mod_cast hidZ
  have hlo :
      (s + a) * (p + r) ≤ (r + i) * (q + s) := by
    by_contra hnot
    have hlt :
        (r + i) * (q + s) < (s + a) * (p + r) := by
      omega
    have hmul := (Nat.mul_lt_mul_left hp).2 hlt
    omega
  have hrem :
      (p - i) + (p + r) * t < p * (p + r) := by
    calc
      (p - i) + (p + r) * t
          < (p + r) + (p + r) * t := by
            exact Nat.add_lt_add_right (by omega) _
      _ = (p + r) * (t + 1) := by ring
      _ ≤ (p + r) * p :=
        Nat.mul_le_mul_left (p + r) (by omega)
      _ = p * (p + r) := by ring
  have hmulUpper :
      p * ((r + i) * (q + s)) <
        p * ((s + a + 1) * (p + r)) := by
    calc
      p * ((r + i) * (q + s)) =
          p * ((s + a) * (p + r)) +
            (p - i) + (p + r) * t := hid
      _ < p * ((s + a) * (p + r)) + p * (p + r) := by
        simpa [Nat.add_assoc] using
          Nat.add_lt_add_left hrem (p * ((s + a) * (p + r)))
      _ = p * ((s + a + 1) * (p + r)) := by ring
  have hiUpper :
      (r + i) * (q + s) <
        (s + a + 1) * (p + r) :=
    (Nat.mul_lt_mul_left hp).1 hmulUpper
  have hdivEq :=
    nat_div_eq_of_mul_le_lt_mul
      (d := p + r)
      (k := s + a)
      (N := (r + i) * (q + s))
      (by omega)
      hlo
      (by simpa [Nat.add_assoc] using hiUpper)
  simpa [a] using hdivEq

/--
Farey neighbors の mediant に対する Christoffel numerator recurrence。

  φ(p+r,q+s) = 3^p φ(r,s) + 2^s φ(p,q).
-/
theorem criticalChristoffelPhi_farey_mediant
    {p q r s : ℕ}
    (hdet : p * s + 1 = r * q) :
    criticalChristoffelPhi (p + r) (q + s) =
      (3 : ℤ) ^ p * criticalChristoffelPhi r s +
        (2 : ℤ) ^ s * criticalChristoffelPhi p q := by
  have hq : 0 < q := by
    by_contra hnot
    have hq0 : q = 0 := by omega
    rw [hq0] at hdet
    simp at hdet
  have hr : 0 < r := by
    by_contra hnot
    have hr0 : r = 0 := by omega
    rw [hr0] at hdet
    simp at hdet
  by_cases hp0 : p = 0
  · subst p
    have hrq : r * q = 1 := by omega
    have hr1 : r = 1 := by nlinarith
    have hq1 : q = 1 := by nlinarith
    subst r
    subst q
    simp [criticalChristoffelPhi]
  · have hp : 0 < p := Nat.pos_of_ne_zero hp0
    rw [criticalChristoffelPhi_eq_sum]
    rw [show p + r = r + p by omega]
    rw [Finset.sum_range_add]
    rw [criticalChristoffelPhi_eq_sum, criticalChristoffelPhi_eq_sum]
    have hleft :
        Finset.sum (Finset.range r)
            (fun i => criticalChristoffelTerm (r + p) (q + s) i) =
          (3 : ℤ) ^ p *
            Finset.sum (Finset.range r)
              (fun i => criticalChristoffelTerm r s i) := by
      calc
        Finset.sum (Finset.range r)
            (fun i => criticalChristoffelTerm (r + p) (q + s) i)
            =
          Finset.sum (Finset.range r)
            (fun i =>
              (3 : ℤ) ^ p * criticalChristoffelTerm r s i) := by
                apply Finset.sum_congr rfl
                intro i hi
                have hir : i < r := Finset.mem_range.mp hi
                unfold criticalChristoffelTerm
                have hfloor :
                    (i * (q + s)) / (r + p) = (i * s) / r := by
                  simpa [Nat.add_comm] using
                    farey_mediant_floor_left hp hr hdet hir
                rw [hfloor]
                have hexp : r + p - 1 - i = p + (r - 1 - i) := by
                  omega
                rw [hexp, pow_add]
                ring
        _ =
          (3 : ℤ) ^ p *
            Finset.sum (Finset.range r)
              (fun i => criticalChristoffelTerm r s i) := by
                rw [Finset.mul_sum]
    have hright :
        Finset.sum (Finset.range p)
            (fun i =>
              criticalChristoffelTerm (r + p) (q + s) (r + i)) =
          (2 : ℤ) ^ s *
            Finset.sum (Finset.range p)
              (fun i => criticalChristoffelTerm p q i) := by
      calc
        Finset.sum (Finset.range p)
            (fun i =>
              criticalChristoffelTerm (r + p) (q + s) (r + i))
            =
          Finset.sum (Finset.range p)
            (fun i =>
              (2 : ℤ) ^ s * criticalChristoffelTerm p q i) := by
                apply Finset.sum_congr rfl
                intro i hi
                have hip : i < p := Finset.mem_range.mp hi
                unfold criticalChristoffelTerm
                have hfloor :
                    ((r + i) * (q + s)) / (r + p) =
                      s + (i * q) / p := by
                  simpa [Nat.add_comm] using
                    farey_mediant_floor_right hp hr hdet hip
                rw [hfloor]
                have hexp : r + p - 1 - (r + i) = p - 1 - i := by
                  omega
                rw [hexp, pow_add]
                ring
        _ =
          (2 : ℤ) ^ s *
            Finset.sum (Finset.range p)
              (fun i => criticalChristoffelTerm p q i) := by
                rw [Finset.mul_sum]
    rw [hleft, hright]

/-- power gap は mediant で Christoffel numerator と同じ係数則を満たす。 -/
private theorem rawChristoffelPowerGapPQ_mediant
    (p q r s : ℕ) :
    rawChristoffelPowerGapPQ (p + r) (q + s) =
      (2 : ℤ) ^ s * rawChristoffelPowerGapPQ p q +
        (3 : ℤ) ^ p * rawChristoffelPowerGapPQ r s := by
  unfold rawChristoffelPowerGapPQ
  rw [pow_add, pow_add]
  ring

/--
任意の positive-or-boundary Farey neighbor pair に対する raw Wronskian exact law。

`p*s+1=r*q` は `p/q < r/s` の determinant-one orientation。
Stern--Brocot parent への減算帰納で

  W = -2^(q-1) 3^(r-1)

を得る。
-/
theorem rawChristoffelWronskianPQ_of_farey
    {p q r s : ℕ}
    (hdet : p * s + 1 = r * q) :
    rawChristoffelWronskianPQ p q r s =
      -((2 : ℤ) ^ (q - 1) * (3 : ℤ) ^ (r - 1)) := by
  have haux :
      ∀ N p q r s : ℕ,
        p + r + q + s = N →
        p * s + 1 = r * q →
        rawChristoffelWronskianPQ p q r s =
          -((2 : ℤ) ^ (q - 1) * (3 : ℤ) ^ (r - 1)) := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
        intro p q r s hsum hdet
        have hq : 0 < q := by
          by_contra hnot
          have hq0 : q = 0 := by omega
          rw [hq0] at hdet
          simp at hdet
        have hr : 0 < r := by
          by_contra hnot
          have hr0 : r = 0 := by omega
          rw [hr0] at hdet
          simp at hdet
        by_cases hp0 : p = 0
        · subst p
          have hrq : r * q = 1 := by omega
          have hr1 : r = 1 := by nlinarith
          have hq1 : q = 1 := by nlinarith
          subst r
          subst q
          simp [
            rawChristoffelWronskianPQ,
            rawChristoffelPowerGapPQ,
            criticalChristoffelPhi
          ]
        · have hp : 0 < p := Nat.pos_of_ne_zero hp0
          by_cases hpr : p < r
          · have hqs : q ≤ s := by
              by_contra hnot
              have hsq : s < q := by omega
              have hrle : p + 1 ≤ r := by omega
              have hqle : s + 1 ≤ q := by omega
              have hmul :
                  (p + 1) * (s + 1) ≤ r * q :=
                Nat.mul_le_mul hrle hqle
              have hstrict :
                  p * s + 1 < (p + 1) * (s + 1) := by
                nlinarith
              omega
            have hdet' :
                p * (s - q) + 1 = (r - p) * q := by
              have hrEq : r = (r - p) + p := by omega
              have hsEq : s = (s - q) + q := by omega
              rw [hrEq, hsEq] at hdet
              simp only [Nat.mul_add, Nat.add_mul] at hdet
              omega
            have hmeasure :
                p + (r - p) + q + (s - q) < N := by
              rw [← hsum]
              omega
            have ihW :=
              ih
                (p + (r - p) + q + (s - q))
                hmeasure
                p q (r - p) (s - q)
                rfl
                hdet'
            have hPhi0 :=
              criticalChristoffelPhi_farey_mediant hdet'
            have hGap0 :=
              rawChristoffelPowerGapPQ_mediant
                p q (r - p) (s - q)
            have hrEq : p + (r - p) = r := by omega
            have hsEq : q + (s - q) = s := by omega
            have hPhi :
                criticalChristoffelPhi r s =
                  (3 : ℤ) ^ p *
                      criticalChristoffelPhi (r - p) (s - q) +
                    (2 : ℤ) ^ (s - q) *
                      criticalChristoffelPhi p q := by
              simpa [hrEq, hsEq] using hPhi0
            have hGap :
                rawChristoffelPowerGapPQ r s =
                  (2 : ℤ) ^ (s - q) *
                      rawChristoffelPowerGapPQ p q +
                    (3 : ℤ) ^ p *
                      rawChristoffelPowerGapPQ (r - p) (s - q) := by
              simpa [hrEq, hsEq] using hGap0
            have hTransport :
                rawChristoffelWronskianPQ p q r s =
                  (3 : ℤ) ^ p *
                    rawChristoffelWronskianPQ
                      p q (r - p) (s - q) := by
              unfold rawChristoffelWronskianPQ
              rw [hPhi, hGap]
              ring
            rw [hTransport, ihW]
            have hexp : r - 1 = p + ((r - p) - 1) := by
              omega
            rw [hexp, pow_add]
            ring
          · have hrp : r ≤ p := by omega
            have hsq : s < q := by
              by_contra hnot
              have hqs : q ≤ s := by omega
              have hmul : r * q ≤ p * s :=
                Nat.mul_le_mul hrp hqs
              omega
            have hdet' :
                (p - r) * s + 1 = r * (q - s) := by
              have hpEq : p = (p - r) + r := by omega
              have hqEq : q = (q - s) + s := by omega
              rw [hpEq, hqEq] at hdet
              simp only [Nat.mul_add, Nat.add_mul] at hdet
              omega
            have hmeasure :
                (p - r) + r + (q - s) + s < N := by
              rw [← hsum]
              omega
            have ihW :=
              ih
                ((p - r) + r + (q - s) + s)
                hmeasure
                (p - r) (q - s) r s
                rfl
                hdet'
            have hPhi0 :=
              criticalChristoffelPhi_farey_mediant hdet'
            have hGap0 :=
              rawChristoffelPowerGapPQ_mediant
                (p - r) (q - s) r s
            have hpEq : (p - r) + r = p := by omega
            have hqEq : (q - s) + s = q := by omega
            have hPhi :
                criticalChristoffelPhi p q =
                  (3 : ℤ) ^ (p - r) * criticalChristoffelPhi r s +
                    (2 : ℤ) ^ s *
                      criticalChristoffelPhi (p - r) (q - s) := by
              simpa [hpEq, hqEq] using hPhi0
            have hGap :
                rawChristoffelPowerGapPQ p q =
                  (2 : ℤ) ^ s *
                      rawChristoffelPowerGapPQ (p - r) (q - s) +
                    (3 : ℤ) ^ (p - r) *
                      rawChristoffelPowerGapPQ r s := by
              simpa [hpEq, hqEq] using hGap0
            have hTransport :
                rawChristoffelWronskianPQ p q r s =
                  (2 : ℤ) ^ s *
                    rawChristoffelWronskianPQ
                      (p - r) (q - s) r s := by
              unfold rawChristoffelWronskianPQ
              rw [hPhi, hGap]
              ring
            rw [hTransport, ihW]
            have hexp : q - 1 = s + ((q - s) - 1) := by
              omega
            rw [hexp, pow_add]
            ring
  exact haux (p + r + q + s) p q r s rfl hdet

/-! ## exact raw critical law -/

/--
consecutive critical Christoffel blocks に対する exact raw Wronskian law。

* even `j` は below -> above:

    W_j = - 2^(q_j-1) 3^(p_(j+1)-1)

* odd `j` は above -> below:

    W_j = + 2^(q_(j+1)-1) 3^(p_j-1)
-/
structure CriticalRawChristoffelWronskianLaw
    (D : CriticalContinuedFractionData) : Prop where
  even_next :
    ∀ j : ℕ,
      D.start ≤ j →
      j % 2 = 0 →
      criticalRawChristoffelWronskianNext D j =
        -((2 : ℤ) ^ (D.q j - 1) *
          (3 : ℤ) ^ (D.p (j + 1) - 1))

  odd_next :
    ∀ j : ℕ,
      D.start ≤ j →
      j % 2 = 1 →
      criticalRawChristoffelWronskianNext D j =
        (2 : ℤ) ^ (D.q (j + 1) - 1) *
          (3 : ℤ) ^ (D.p j - 1)

/-- even actual pair は determinant-one の below -> above orientation。 -/
private theorem actual_even_farey_determinant
    {j : ℕ}
    (hj : 9 ≤ j)
    (hjEven : j % 2 = 0) :
    criticalPowerP j * criticalPowerQ (j + 1) + 1 =
      criticalPowerP (j + 1) * criticalPowerQ j := by
  have hBelow := (criticalPower_orientation j).1 hjEven
  have hjOdd : (j + 1) % 2 = 1 := by omega
  have hAbove := (criticalPower_orientation (j + 1)).2 hjOdd
  have hcross :=
    CriticalPowerFraction.cross_lt_of_below_above hBelow hAbove
  have hcross' :
      criticalPowerP j * criticalPowerQ (j + 1) <
        criticalPowerP (j + 1) * criticalPowerQ j := by
    simpa [criticalPowerP, criticalPowerQ] using hcross
  rcases criticalPower_adjacent_next hj with h | h
  · simpa [criticalPowerP, criticalPowerQ] using h
  · have hrev :
        criticalPowerP (j + 1) * criticalPowerQ j + 1 =
          criticalPowerP j * criticalPowerQ (j + 1) := by
      simpa [criticalPowerP, criticalPowerQ] using h
    omega

/-- odd actual pair は next/current を並べると determinant-one の below -> above orientation。 -/
private theorem actual_odd_farey_determinant
    {j : ℕ}
    (hj : 9 ≤ j)
    (hjOdd : j % 2 = 1) :
    criticalPowerP (j + 1) * criticalPowerQ j + 1 =
      criticalPowerP j * criticalPowerQ (j + 1) := by
  have hjEven : (j + 1) % 2 = 0 := by omega
  have hBelow := (criticalPower_orientation (j + 1)).1 hjEven
  have hAbove := (criticalPower_orientation j).2 hjOdd
  have hcross :=
    CriticalPowerFraction.cross_lt_of_below_above hBelow hAbove
  have hcross' :
      criticalPowerP (j + 1) * criticalPowerQ j <
        criticalPowerP j * criticalPowerQ (j + 1) := by
    simpa [criticalPowerP, criticalPowerQ] using hcross
  rcases criticalPower_adjacent_next hj with h | h
  · have hfwd :
        criticalPowerP j * criticalPowerQ (j + 1) + 1 =
          criticalPowerP (j + 1) * criticalPowerQ j := by
      simpa [criticalPowerP, criticalPowerQ] using h
    omega
  · simpa [criticalPowerP, criticalPowerQ] using h

/--
actual power-Farey sequence から raw Christoffel Wronskian law を無仮定で構成する。

consecutive Farey adjacency 自体は `CriticalPowerFarey` の Stern--Brocot recursion から得られ、
上の generic determinant-one theorem が Christoffel numerator 側を閉じる。
-/
theorem actualCriticalRawChristoffelWronskianLaw :
    CriticalRawChristoffelWronskianLaw
      actualCriticalContinuedFractionData := by
  refine {
    even_next := ?_
    odd_next := ?_
  }
  · intro j hjStart hjEven
    have hj : 9 ≤ j := by
      simpa [actualCriticalContinuedFractionData] using hjStart
    have hdet := actual_even_farey_determinant hj hjEven
    change
      rawChristoffelWronskianPQ
          (criticalPowerP j)
          (criticalPowerQ j)
          (criticalPowerP (j + 1))
          (criticalPowerQ (j + 1)) =
        -((2 : ℤ) ^ (criticalPowerQ j - 1) *
          (3 : ℤ) ^ (criticalPowerP (j + 1) - 1))
    exact rawChristoffelWronskianPQ_of_farey hdet
  · intro j hjStart hjOdd
    have hj : 9 ≤ j := by
      simpa [actualCriticalContinuedFractionData] using hjStart
    have hdet := actual_odd_farey_determinant hj hjOdd
    have hW := rawChristoffelWronskianPQ_of_farey hdet
    have hswap :
        rawChristoffelWronskianPQ
            (criticalPowerP j)
            (criticalPowerQ j)
            (criticalPowerP (j + 1))
            (criticalPowerQ (j + 1)) =
          -rawChristoffelWronskianPQ
            (criticalPowerP (j + 1))
            (criticalPowerQ (j + 1))
            (criticalPowerP j)
            (criticalPowerQ j) := by
      unfold rawChristoffelWronskianPQ
      ring
    change
      rawChristoffelWronskianPQ
          (criticalPowerP j)
          (criticalPowerQ j)
          (criticalPowerP (j + 1))
          (criticalPowerQ (j + 1)) =
        (2 : ℤ) ^ (criticalPowerQ (j + 1) - 1) *
          (3 : ℤ) ^ (criticalPowerP j - 1)
    rw [hswap, hW]
    ring

namespace CriticalRawChristoffelWronskianLaw

/-- even branch raw Wronskian は strict negative。 -/
theorem even_next_neg
    {D : CriticalContinuedFractionData}
    (W : CriticalRawChristoffelWronskianLaw D)
    {j : ℕ}
    (hjStart : D.start ≤ j)
    (hjEven : j % 2 = 0) :
    criticalRawChristoffelWronskianNext D j < 0 := by
  rw [W.even_next j hjStart hjEven]
  have hpos :
      0 <
        (2 : ℤ) ^ (D.q j - 1) *
          (3 : ℤ) ^ (D.p (j + 1) - 1) := by
    positivity
  omega

/-- odd branch raw Wronskian は strict positive。 -/
theorem odd_next_pos
    {D : CriticalContinuedFractionData}
    (W : CriticalRawChristoffelWronskianLaw D)
    {j : ℕ}
    (hjStart : D.start ≤ j)
    (hjOdd : j % 2 = 1) :
    0 < criticalRawChristoffelWronskianNext D j := by
  rw [W.odd_next j hjStart hjOdd]
  positivity

/-- exact raw law があれば consecutive Wronskian は全 relevant index で nonzero。 -/
theorem next_ne_zero
    {D : CriticalContinuedFractionData}
    (W : CriticalRawChristoffelWronskianLaw D)
    {j : ℕ}
    (hjStart : D.start ≤ j) :
    criticalRawChristoffelWronskianNext D j ≠ 0 := by
  have hmod : j % 2 < 2 := Nat.mod_lt j (by decide)
  by_cases hjOdd : j % 2 = 1
  · exact ne_of_gt (W.odd_next_pos hjStart hjOdd)
  · have hjEven : j % 2 = 0 := by omega
    exact ne_of_lt (W.even_next_neg hjStart hjEven)

end CriticalRawChristoffelWronskianLaw

end ExternalArithmetic
end CSTMicro
end Collatz2
