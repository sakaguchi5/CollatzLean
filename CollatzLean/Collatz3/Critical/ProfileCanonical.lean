import CollatzLean.Collatz3.Critical.ProfileAffine
import CollatzLean.Collatz3.Canonical.AffineDataREQ

/-!
# Collatz3: profile canonical coordinates

Profile が決める affine data

`(p,H,B) = (m, criticalTwoDepth m, profileAffineNumerator h)`

を共有 `AffineDataResidue / AffineDataREQ` 核へ渡すだけの薄い wrapper。

`R(h), Y(h), Q(h)` は profile packet field ではなく、すべて affine data から導く。
-/

namespace Collatz3
namespace Critical

/-- profile odd-endpoint residue の法 `2^(H+1)`。 -/
def profileOddEndpointModulus (m : ℕ) : ℕ :=
  oddEndpointModulusOfAffineData (criticalTwoDepth m)

@[simp] theorem profileOddEndpointModulus_eq (m : ℕ) :
    profileOddEndpointModulus m =
      2 ^ (criticalTwoDepth m + 1) := by
  rfl

@[simp] theorem profileOddEndpointModulus_pos (m : ℕ) :
    0 < profileOddEndpointModulus m := by
  exact
    oddEndpointModulusOfAffineData_pos
      (criticalTwoDepth m)

/-- profile affine data が決める odd-start residue class。 -/
def profileOddStartClass
    {m : ℕ}
    (h : Profile m) :
    ZMod (profileOddEndpointModulus m) :=
  oddStartClassOfAffineData
    m
    (criticalTwoDepth m)
    (profileAffineNumerator h)

@[simp] theorem profileOddStartClass_eq_affineData
    {m : ℕ}
    (h : Profile m) :
    profileOddStartClass h =
      oddStartClassOfAffineData
        m
        (criticalTwoDepth m)
        (profileAffineNumerator h) := by
  rfl

/-- profile odd-start class は defining congruence を満たす。 -/
theorem profileOddStartClass_spec
    {m : ℕ}
    (h : Profile m) :
    (((3 ^ m : ℕ) :
        ZMod (profileOddEndpointModulus m)) *
      profileOddStartClass h) +
        ((profileAffineNumerator h : ℕ) :
          ZMod (profileOddEndpointModulus m)) =
      ((2 ^ criticalTwoDepth m : ℕ) :
        ZMod (profileOddEndpointModulus m)) := by
  exact
    oddStartClassOfAffineData_spec
      m
      (criticalTwoDepth m)
      (profileAffineNumerator h)

/-- profile canonical start `R(h)`。 -/
def profileCanonicalStart
    {m : ℕ}
    (h : Profile m) : ℕ :=
  canonicalStartOfAffineData
    m
    (criticalTwoDepth m)
    (profileAffineNumerator h)

theorem profileCanonicalStart_eq_oddStartClass_val
    {m : ℕ}
    (h : Profile m) :
    profileCanonicalStart h =
      (profileOddStartClass h).val := by
  rfl

/-- `R(h)` は modulus 未満。 -/
theorem profileCanonicalStart_lt_modulus
    {m : ℕ}
    (h : Profile m) :
    profileCanonicalStart h <
      profileOddEndpointModulus m := by
  exact
    canonicalStartOfAffineData_lt_modulus
      m
      (criticalTwoDepth m)
      (profileAffineNumerator h)

/-- canonical start を `ZMod` に戻すと元の class。 -/
theorem profileCanonicalStart_cast
    {m : ℕ}
    (h : Profile m) :
    ((profileCanonicalStart h : ℕ) :
        ZMod (profileOddEndpointModulus m)) =
      profileOddStartClass h := by
  exact
    canonicalStartOfAffineData_cast
      m
      (criticalTwoDepth m)
      (profileAffineNumerator h)

/-- profile canonical numerator。 -/
def profileCanonicalNumerator
    {m : ℕ}
    (h : Profile m) : ℕ :=
  canonicalNumeratorOfAffineData
    m
    (criticalTwoDepth m)
    (profileAffineNumerator h)

/-- canonical numerator の `2^(H+1)` 剰余は exactly `2^H`。 -/
theorem profileCanonicalNumerator_mod_modulus
    {m : ℕ}
    (h : Profile m) :
    profileCanonicalNumerator h %
        profileOddEndpointModulus m =
      2 ^ criticalTwoDepth m := by
  exact
    canonicalNumeratorOfAffineData_mod_modulus
      m
      (criticalTwoDepth m)
      (profileAffineNumerator h)

/-- profile canonical numerator は `2^H * odd`。 -/
theorem profileCanonicalNumerator_eq_twoPow_mul_odd
    {m : ℕ}
    (h : Profile m) :
    ∃ k : ℕ,
      profileCanonicalNumerator h =
        2 ^ criticalTwoDepth m * (2 * k + 1) := by
  exact
    canonicalNumeratorOfAffineData_eq_twoPow_mul_odd
      m
      (criticalTwoDepth m)
      (profileAffineNumerator h)

/-- profile canonical endpoint `Y(h)`。 -/
def profileCanonicalEnd
    {m : ℕ}
    (h : Profile m) : ℕ :=
  canonicalEndOfAffineData
    m
    (criticalTwoDepth m)
    (profileAffineNumerator h)

/-- profile canonical endpoint は numerator を exact に割り切る。 -/
theorem twoPow_mul_profileCanonicalEnd
    {m : ℕ}
    (h : Profile m) :
    2 ^ criticalTwoDepth m * profileCanonicalEnd h =
      profileCanonicalNumerator h := by
  exact
    twoPow_mul_canonicalEndOfAffineData
      m
      (criticalTwoDepth m)
      (profileAffineNumerator h)

/-- profile canonical endpoint `Y(h)` は奇数。 -/
theorem profileCanonicalEnd_odd
    {m : ℕ}
    (h : Profile m) :
    Odd (profileCanonicalEnd h) := by
  exact
    canonicalEndOfAffineData_odd
      m
      (criticalTwoDepth m)
      (profileAffineNumerator h)

/-- profile canonical drift `Q(h) = Y(h)-R(h)`。 -/
def profileCanonicalGap
    {m : ℕ}
    (h : Profile m) : ℤ :=
  canonicalGapOfAffineData
    m
    (criticalTwoDepth m)
    (profileAffineNumerator h)

/-- profile 版 REQ 基本等式。 -/
theorem profile_req_equation
    {m : ℕ}
    (h : Profile m) :
    2 ^ criticalTwoDepth m * profileCanonicalEnd h =
      3 ^ m * profileCanonicalStart h +
        profileAffineNumerator h := by
  exact
    reqEquationOfAffineData
      m
      (criticalTwoDepth m)
      (profileAffineNumerator h)

/-- `A(h) = (2^H-3^m)R(h) + 2^H Q(h)`。 -/
theorem profileAffineNumerator_eq_gap_start_add_twoPow_gap
    {m : ℕ}
    (h : Profile m) :
    (profileAffineNumerator h : ℤ) =
      ((2 : ℤ) ^ criticalTwoDepth m -
          (3 : ℤ) ^ m) *
        (profileCanonicalStart h : ℤ) +
      (2 : ℤ) ^ criticalTwoDepth m *
        profileCanonicalGap h := by
  exact
    affineTranslation_eq_scaleGap_start_add_twoPow_gap
      m
      (criticalTwoDepth m)
      (profileAffineNumerator h)

end Critical
end Collatz3
