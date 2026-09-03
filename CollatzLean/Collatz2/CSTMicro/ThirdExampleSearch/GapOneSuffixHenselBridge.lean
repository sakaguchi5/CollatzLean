import CollatzLean.Collatz2.CSTMicro.DoubleDecomposition.ExactGapOneBeattyCertificate

/-!
# 第3例探索: PureB-free gap-one suffix Hensel bridge

Case II 用 `PureBProfileObstruction` を一切仮定せず、
真の gap-one certificate から得られる actual endpoint

  y = 2*m + 1

に対して、その通常の3進展開を Hensel lift として読む。

r 桁までの residue を

  q_r = y mod 3^r

とし、次の digit を

  d_r = floor(y / 3^r) mod 3

とする。

すると canonical next lift は

  q_r + d_r 3^r

であり、三候補

  q_r,
  q_r + 3^r,
  q_r + 2*3^r

の中で actual y と mod 3^(r+1) で一致するものが一意になる。

この構成には PureB / minimal-bad-word / 3q<m を使わない。
-/

namespace Collatz2
namespace CSTMicro
namespace ThirdExampleSearch

open DoubleDecomposition

/-- gap-one start value n = 3m+1。 -/
def gapOneStartValue
    (m : ℕ) : ℕ :=
  3 * m + 1

/-- first-drop endpoint y = 2m+1。 -/
def gapOneEndpointValue
    (m : ℕ) : ℕ :=
  2 * m + 1

/--
gap-one endpoint と元の start の exact special-return identity。

  3y = 2n + 1.
-/
theorem three_mul_gapOneEndpointValue
    (m : ℕ) :
    3 * gapOneEndpointValue m =
      2 * gapOneStartValue m + 1 := by
  unfold gapOneEndpointValue gapOneStartValue
  omega

/--
r 桁までの actual ternary residue。
-/
def gapOneThreeAdicPrefix
    (y r : ℕ) : ℕ :=
  y % (3 ^ r)

/--
r 番目の actual ternary digit。
値は必ず 0,1,2。
-/
def gapOneThreeAdicDigit
    (y r : ℕ) : ℕ :=
  (y / (3 ^ r)) % 3

theorem gapOneThreeAdicDigit_lt_three
    (y r : ℕ) :
    gapOneThreeAdicDigit y r < 3 := by
  unfold gapOneThreeAdicDigit
  exact Nat.mod_lt _ (by norm_num)

/--
actual digit を `Fin 3` label にする。
-/
def gapOneThreeAdicDigitFin
    (y r : ℕ) : Fin 3 :=
  ⟨gapOneThreeAdicDigit y r,
    gapOneThreeAdicDigit_lt_three y r⟩

@[simp] theorem gapOneThreeAdicDigitFin_val
    (y r : ℕ) :
    (gapOneThreeAdicDigitFin y r).val =
      gapOneThreeAdicDigit y r := rfl

/--
r 桁 residue に次の actual digit を追加した canonical Hensel lift。
-/
def gapOneCanonicalHenselLift
    (y r : ℕ) : ℕ :=
  gapOneThreeAdicPrefix y r +
    gapOneThreeAdicDigit y r * 3 ^ r

/--
actual integer y の base-3 decomposition。

  y =
    canonicalLift_r(y)
      + 3^(r+1) * floor(y / 3^(r+1)).

従って canonical lift は mod 3^(r+1) の actual residue そのもの。
-/
theorem gapOneCanonicalHenselLift_decomposition
    (y r : ℕ) :
    y =
      gapOneCanonicalHenselLift y r +
        3 ^ (r + 1) * (y / 3 ^ (r + 1)) := by
  have hy :=
    Nat.mod_add_div y (3 ^ r)
  have hq :=
    Nat.mod_add_div (y / 3 ^ r) 3
  unfold gapOneCanonicalHenselLift
    gapOneThreeAdicPrefix
    gapOneThreeAdicDigit
  rw [pow_succ]
  calc
    y =
        y % 3 ^ r +
          3 ^ r * (y / 3 ^ r) := by
            simpa [Nat.mul_comm] using hy.symm
    _ =
        y % 3 ^ r +
          3 ^ r *
            (((y / 3 ^ r) % 3) +
              3 * ((y / 3 ^ r) / 3)) := by
            rw [← hq]
            simp
            omega
    _ =
        y % 3 ^ r +
          ((y / 3 ^ r) % 3) * 3 ^ r +
          (3 ^ r * 3) *
            ((y / 3 ^ r) / 3) := by
            ring
    _ =
        y % 3 ^ r +
          ((y / 3 ^ r) % 3) * 3 ^ r +
          3 ^ (r + 1) *
            (y / 3 ^ (r + 1)) := by
            rw [pow_succ]
            congr 1
            simp [Nat.div_div_eq_div_mul]
    _ =
        (y % 3 ^ r +
          ((y / 3 ^ r) % 3) * 3 ^ r) +
          3 ^ (r + 1) *
            (y / 3 ^ (r + 1)) := by
            ring

/--
canonical lift は actual y と mod 3^(r+1) で一致。
-/
theorem gapOneCanonicalHenselLift_mod_next
    (y r : ℕ) :
    gapOneCanonicalHenselLift y r %
        (3 ^ (r + 1)) =
      y % (3 ^ (r + 1)) := by
  have h :=
    gapOneCanonicalHenselLift_decomposition y r
  have hMod :=
    congrArg
      (fun n : ℕ => n % (3 ^ (r + 1)))
      h
  simpa [Nat.add_mod] using hMod.symm


/--
三つの Hensel candidate。

a=0,1,2 に対して

  q_r + a*3^r.
-/
def gapOneHenselThreeLiftValue
    (y r : ℕ)
    (a : Fin 3) : ℕ :=
  gapOneThreeAdicPrefix y r +
    a.val * 3 ^ r

/--
actual endpoint y の次 digit を選んだ canonical candidate。
-/
def gapOneHenselCandidateValue
    (y r : ℕ) : ℕ :=
  gapOneHenselThreeLiftValue
    y r
    (gapOneThreeAdicDigitFin y r)

@[simp] theorem gapOneHenselCandidateValue_eq
    (y r : ℕ) :
    gapOneHenselCandidateValue y r =
      gapOneCanonicalHenselLift y r := by
  rfl

/--
三候補のうち actual y と mod 3^(r+1) で一致すること。
-/
def GapOneHenselLiftSurvives
    (y r : ℕ)
    (v : ℕ) : Prop :=
  ∃ a : Fin 3,
    v = gapOneHenselThreeLiftValue y r a ∧
      a = gapOneThreeAdicDigitFin y r

/-- canonical candidate は survivor。 -/
theorem gapOneHenselCandidateValue_survives
    (y r : ℕ) :
    GapOneHenselLiftSurvives
      y r
      (gapOneHenselCandidateValue y r) := by
  refine
    ⟨gapOneThreeAdicDigitFin y r, rfl, rfl⟩

/--
PureB 条件なしでも、actual endpoint が決まれば
三つの lift のうち actual digit candidate は exact に一つ。
-/
theorem gapOneHenselLiftSurvivor_eq_candidate
    (y r : ℕ)
    {v : ℕ}
    (hv : GapOneHenselLiftSurvives y r v) :
    v = gapOneHenselCandidateValue y r := by
  rcases hv with ⟨a, rfl, ha⟩
  subst a
  rfl

theorem gapOneHenselLiftSurvivor_existsUnique
    (y r : ℕ) :
    ∃! v : ℕ,
      GapOneHenselLiftSurvives y r v := by
  refine
    ⟨gapOneHenselCandidateValue y r,
      gapOneHenselCandidateValue_survives y r,
      ?_⟩
  intro v hv
  exact
    gapOneHenselLiftSurvivor_eq_candidate y r hv

/--
y < 3^R なら、R 桁以降の ternary digit はすべて0。

これが巨大 gap-one window で使う「finite Hensel support」。
-/
theorem gapOneThreeAdicDigit_eq_zero_of_lt_pow
    {y R r : ℕ}
    (hy : y < 3 ^ R)
    (hRr : R ≤ r) :
    gapOneThreeAdicDigit y r = 0 := by
  have hPow :
      3 ^ R ≤ 3 ^ r := by
    exact
      Nat.pow_le_pow_right
        (by norm_num : 0 < (3 : ℕ))
        hRr
  have hy' :
      y < 3 ^ r :=
    lt_of_lt_of_le hy hPow
  unfold gapOneThreeAdicDigit
  rw [Nat.div_eq_of_lt hy']

/--
従って y < 3^R なら R 桁以降では canonical lift は zero-digit lift。
-/
theorem gapOneCanonicalHenselLift_eq_prefix_of_lt_pow
    {y R r : ℕ}
    (hy : y < 3 ^ R)
    (hRr : R ≤ r) :
    gapOneCanonicalHenselLift y r =
      gapOneThreeAdicPrefix y r := by
  unfold gapOneCanonicalHenselLift
  rw [gapOneThreeAdicDigit_eq_zero_of_lt_pow hy hRr]
  simp

/--
Exact gap-one certificate が実際に与える first-drop run。
PureB obstruction は一切使わない。
-/
theorem exactGapOne_has_actual_endpoint
    {w : Word}
    {p H deficit gap m : ℕ}
    (C :
      ExactCriticalGapOneFerrersCertificate
        w p H deficit gap m) :
    Runs w
        (gapOneStartValue m)
        (gapOneEndpointValue m) := by
  have h :=
    gapOneParadoxical_of_exactCriticalFerrersCertificate C
  simpa [
    gapOneStartValue,
    gapOneEndpointValue
  ] using h.1

/--
Exact gap-one certificate の terminal endpoint は
次の exponent-1 step で start+1 へ戻る。
-/
theorem exactGapOne_endpoint_rebounds_to_start_succ
    {w : Word}
    {p H deficit gap m : ℕ}
    (C :
      ExactCriticalGapOneFerrersCertificate
        w p H deficit gap m) :
    Word.Realizes
      ([1] : Word)
      (gapOneEndpointValue m)
      (gapOneStartValue m + 1) := by
  have h :=
    gapOneParadoxical_of_exactCriticalFerrersCertificate C
  simpa [
    gapOneStartValue,
    gapOneEndpointValue
  ] using h.2.2

/--
gap-one endpoint の rebound は単純な整数恒等式

  3 * y = 2 * n + 1

を満たす。

ここで
`n = gapOneStartValue m`,
`y = gapOneEndpointValue m`。
-/
theorem gapOne_specialReturnEquation
    (m : ℕ) :
    3 * gapOneEndpointValue m =
      2 * gapOneStartValue m + 1 := by
  exact three_mul_gapOneEndpointValue m

/--
gap-one endpoint が

  gapOneEndpointValue m < 3^42

を満たすなら、42桁目以降の 3進 digit はすべて 0。
-/
theorem gapOneEndpoint_zero_digit_from_fortyTwo
    {m r : ℕ}
    (hy : gapOneEndpointValue m < 3 ^ 42)
    (hr : 42 ≤ r) :
    gapOneThreeAdicDigit
      (gapOneEndpointValue m) r = 0 := by
  exact
    gapOneThreeAdicDigit_eq_zero_of_lt_pow
      hy hr

end ThirdExampleSearch
end CSTMicro
end Collatz2
