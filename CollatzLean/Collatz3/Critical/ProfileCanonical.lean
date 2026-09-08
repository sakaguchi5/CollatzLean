import CollatzLean.Collatz3.Critical.ProfileAffine
import CollatzLean.Collatz3.Canonical.OddEndpointResidue

import Mathlib.Tactic.Ring

/-!
# Collatz3: profile canonical coordinates

profile が決める affine data

`(p,H,B) = (m, criticalTwoDepth m, profileAffineNumerator h)`

から odd-endpoint residue と canonical coordinates

`R(h), Y(h), Q(h)`

を直接導く。

これらは profile packet field ではない。

odd-start class と canonical start の構成そのものは
`Canonical.OddEndpointResidue` の affine-data 共有核を使い、
Profile 側では affine data の選択だけを行う。
-/

namespace Collatz3

namespace Critical

/-!
## profile affine data の odd-endpoint residue
-/

/-- profile odd-endpoint residue の法 `2^(H+1)`。 -/
def profileOddEndpointModulus (m : ℕ) : ℕ :=
  Arithmetic.twoPowModulus (criticalTwoDepth m + 1)

@[simp] theorem profileOddEndpointModulus_eq (m : ℕ) :
    profileOddEndpointModulus m =
      2 ^ (criticalTwoDepth m + 1) := by
  rfl

@[simp] theorem profileOddEndpointModulus_pos (m : ℕ) :
    0 < profileOddEndpointModulus m := by
  simp [profileOddEndpointModulus, Arithmetic.twoPowModulus]

/--
profile affine data が決める odd-start residue class。

これは affine data

`(m, criticalTwoDepth m, profileAffineNumerator h)`

に対する共有 odd-start class の薄い wrapper。
-/
def profileOddStartClass
    {m : ℕ}
    (h : Profile m) :
    ZMod (profileOddEndpointModulus m) :=
  oddStartClassOfAffineData
    m
    (criticalTwoDepth m)
    (profileAffineNumerator h)

/--
profile odd-start class は共有 affine-data class そのもの。
-/
@[simp] theorem profileOddStartClass_eq_affineData
    {m : ℕ}
    (h : Profile m) :
    profileOddStartClass h =
      oddStartClassOfAffineData
        m
        (criticalTwoDepth m)
        (profileAffineNumerator h) := by
  rfl

/--
profile odd-start class は defining congruence

`3^m * R + A(h) = 2^H (mod 2^(H+1))`

を満たす。
-/
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
  change
    (((3 ^ m : ℕ) :
        ZMod
          (Arithmetic.twoPowModulus
            (criticalTwoDepth m + 1))) *
      oddStartClassOfAffineData
        m
        (criticalTwoDepth m)
        (profileAffineNumerator h)) +
      ((profileAffineNumerator h : ℕ) :
        ZMod
          (Arithmetic.twoPowModulus
            (criticalTwoDepth m + 1))) =
    ((2 ^ criticalTwoDepth m : ℕ) :
      ZMod
        (Arithmetic.twoPowModulus
          (criticalTwoDepth m + 1)))
  exact
    oddStartClassOfAffineData_spec
      m
      (criticalTwoDepth m)
      (profileAffineNumerator h)

/-!
## profile canonical start
-/

/--
profile canonical start `R(h)`。

primitive data として保存せず、
profile の affine data `(p,H,B)` から導く。
-/
def profileCanonicalStart
    {m : ℕ}
    (h : Profile m) : ℕ :=
  canonicalStartOfAffineData
    m
    (criticalTwoDepth m)
    (profileAffineNumerator h)

/--
profile canonical start は
profile odd-start class の最小非負代表。
-/
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
  change
    canonicalStartOfAffineData
        m
        (criticalTwoDepth m)
        (profileAffineNumerator h) <
      Arithmetic.twoPowModulus
        (criticalTwoDepth m + 1)
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
  change
    ((canonicalStartOfAffineData
        m
        (criticalTwoDepth m)
        (profileAffineNumerator h) : ℕ) :
      ZMod
        (Arithmetic.twoPowModulus
          (criticalTwoDepth m + 1))) =
    oddStartClassOfAffineData
      m
      (criticalTwoDepth m)
      (profileAffineNumerator h)
  exact
    canonicalStartOfAffineData_cast
      m
      (criticalTwoDepth m)
      (profileAffineNumerator h)

/-!
## canonical numerator
-/

/-- profile canonical start を affine equation に代入した分子。 -/
def profileCanonicalNumerator
    {m : ℕ}
    (h : Profile m) : ℕ :=
  3 ^ m * profileCanonicalStart h +
    profileAffineNumerator h

/--
canonical numerator の `2^(H+1)` 剰余は exactly `2^H`。
-/
theorem profileCanonicalNumerator_mod_modulus
    {m : ℕ}
    (h : Profile m) :
    profileCanonicalNumerator h %
        profileOddEndpointModulus m =
      2 ^ criticalTwoDepth m := by
  have : NeZero (profileOddEndpointModulus m) :=
    ⟨Nat.ne_of_gt (profileOddEndpointModulus_pos m)⟩
  have hcast :
      ((profileCanonicalNumerator h : ℕ) :
          ZMod (profileOddEndpointModulus m)) =
        ((2 ^ criticalTwoDepth m : ℕ) :
          ZMod (profileOddEndpointModulus m)) := by
    calc
      ((profileCanonicalNumerator h : ℕ) :
          ZMod (profileOddEndpointModulus m))
          =
          (((3 ^ m : ℕ) :
              ZMod (profileOddEndpointModulus m)) *
            ((profileCanonicalStart h : ℕ) :
              ZMod (profileOddEndpointModulus m))) +
          ((profileAffineNumerator h : ℕ) :
            ZMod (profileOddEndpointModulus m)) := by
              simp [profileCanonicalNumerator]
      _ =
          (((3 ^ m : ℕ) :
              ZMod (profileOddEndpointModulus m)) *
            profileOddStartClass h) +
          ((profileAffineNumerator h : ℕ) :
            ZMod (profileOddEndpointModulus m)) := by
              rw [profileCanonicalStart_cast]
      _ =
          ((2 ^ criticalTwoDepth m : ℕ) :
            ZMod (profileOddEndpointModulus m)) :=
        profileOddStartClass_spec h
  have hval := congrArg ZMod.val hcast
  have hpowlt :
      2 ^ criticalTwoDepth m <
        profileOddEndpointModulus m := by
    unfold profileOddEndpointModulus
      Arithmetic.twoPowModulus
    exact
      Nat.pow_lt_pow_right
        (by omega)
        (Nat.lt_succ_self _)
  calc
    profileCanonicalNumerator h %
        profileOddEndpointModulus m
        =
        (((profileCanonicalNumerator h : ℕ) :
          ZMod (profileOddEndpointModulus m))).val := by
            simp only [ZMod.val_natCast]
    _ =
        (((2 ^ criticalTwoDepth m : ℕ) :
          ZMod (profileOddEndpointModulus m))).val :=
      hval
    _ =
        (2 ^ criticalTwoDepth m) %
          profileOddEndpointModulus m := by
            simp only [ZMod.val_natCast]
    _ =
        2 ^ criticalTwoDepth m :=
      Nat.mod_eq_of_lt hpowlt

/-- profile canonical numerator は `2^H * odd`。 -/
theorem profileCanonicalNumerator_eq_twoPow_mul_odd
    {m : ℕ}
    (h : Profile m) :
    ∃ k : ℕ,
      profileCanonicalNumerator h =
        2 ^ criticalTwoDepth m * (2 * k + 1) := by
  have hdecomp :=
    Nat.mod_add_div
      (profileCanonicalNumerator h)
      (profileOddEndpointModulus m)
  rw [profileCanonicalNumerator_mod_modulus h] at hdecomp
  refine
    ⟨profileCanonicalNumerator h /
        profileOddEndpointModulus m, ?_⟩
  calc
    profileCanonicalNumerator h
        =
        2 ^ criticalTwoDepth m +
          profileOddEndpointModulus m *
            (profileCanonicalNumerator h /
              profileOddEndpointModulus m) := by
                exact hdecomp.symm
    _ =
        2 ^ criticalTwoDepth m *
          (2 *
              (profileCanonicalNumerator h /
                profileOddEndpointModulus m) +
            1) := by
              unfold profileOddEndpointModulus
                Arithmetic.twoPowModulus
              rw [pow_succ]
              ring

/-!
## profile canonical endpoint
-/

/-- profile canonical endpoint `Y(h)`。 -/
def profileCanonicalEnd
    {m : ℕ}
    (h : Profile m) : ℕ :=
  profileCanonicalNumerator h /
    2 ^ criticalTwoDepth m

/--
profile canonical endpoint は numerator を exact に割り切る。
-/
theorem twoPow_mul_profileCanonicalEnd
    {m : ℕ}
    (h : Profile m) :
    2 ^ criticalTwoDepth m *
        profileCanonicalEnd h =
      profileCanonicalNumerator h := by
  rcases
      profileCanonicalNumerator_eq_twoPow_mul_odd h
      with ⟨k, hk⟩
  simp [profileCanonicalEnd, hk]

/-- profile canonical endpoint は奇数。 -/
theorem profileCanonicalEnd_odd
    {m : ℕ}
    (h : Profile m) :
    Odd (profileCanonicalEnd h) := by
  rcases
      profileCanonicalNumerator_eq_twoPow_mul_odd h
      with ⟨k, hk⟩
  have hEnd :
      profileCanonicalEnd h = 2 * k + 1 := by
    simp [profileCanonicalEnd, hk]
  exact ⟨k, hEnd⟩

/-!
## profile canonical drift
-/

/-- profile canonical drift `Q(h) = Y(h) - R(h)`。 -/
def profileCanonicalGap
    {m : ℕ}
    (h : Profile m) : ℤ :=
  (profileCanonicalEnd h : ℤ) -
    (profileCanonicalStart h : ℤ)

/-- profile 版 REQ 基本等式。 -/
theorem profile_req_equation
    {m : ℕ}
    (h : Profile m) :
    2 ^ criticalTwoDepth m *
        profileCanonicalEnd h =
      3 ^ m * profileCanonicalStart h +
        profileAffineNumerator h := by
  rw [twoPow_mul_profileCanonicalEnd]
  rfl

/--
`A(h) = (2^H - 3^m) R(h) + 2^H Q(h)`。
-/
theorem profileAffineNumerator_eq_gap_start_add_twoPow_gap
    {m : ℕ}
    (h : Profile m) :
    (profileAffineNumerator h : ℤ) =
      ((2 : ℤ) ^ criticalTwoDepth m -
          (3 : ℤ) ^ m) *
        (profileCanonicalStart h : ℤ) +
      (2 : ℤ) ^ criticalTwoDepth m *
        profileCanonicalGap h := by
  have hEq :=
    congrArg
      (fun n : ℕ => (n : ℤ))
      (profile_req_equation h)
  push_cast at hEq
  calc
    (profileAffineNumerator h : ℤ)
        =
        (2 : ℤ) ^ criticalTwoDepth m *
            (profileCanonicalEnd h : ℤ) -
          (3 : ℤ) ^ m *
            (profileCanonicalStart h : ℤ) := by
              linarith
    _ =
        ((2 : ℤ) ^ criticalTwoDepth m -
            (3 : ℤ) ^ m) *
          (profileCanonicalStart h : ℤ) +
        (2 : ℤ) ^ criticalTwoDepth m *
          profileCanonicalGap h := by
            simp [profileCanonicalGap]
            ring

end Critical

end Collatz3
