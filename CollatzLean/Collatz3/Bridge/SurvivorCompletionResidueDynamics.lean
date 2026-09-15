import CollatzLean.Collatz3.Bridge.SurvivorCompletionNormalizedLift
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Collatz3 Bridge: completion canonical residue の一歩遷移

`completionCocycleResidue m E` は

`3^(m+1) r + 1 ≡ 2^E (mod 2^(E+1))`

の canonical representative である。このファイルでは、その defining congruence だけから
`m -> m+1` の residue transition を導く。

future-minimum `e_m=1` では defect は flat または `+1` なので、
`E = δ+1` に対して

* flat: `3 r_(m+1) ≡ r_m                 (mod 2^(δ+2))`
* rise: `3 r_(m+1) ≡ r_m + 2^(δ+1)       (mod 2^(δ+2))`

となる。

正規化 `rho = r / 2^δ` では、それぞれ

* `3 rho' = rho + 4 k`
* `6 rho' = rho + 2 + 4 k`

という exact affine relation になる。

新しい residue notion は導入しない。
-/

namespace Collatz3
namespace Bridge

/-- canonical residue の defining equation を `Int.ModEq` で読んだ形。 -/
theorem completionCocycleResidue_spec_intModEq
    (m E : ℕ) :
    (3 : ℤ) ^ (m + 1) * (completionCocycleResidue m E : ℤ) + 1 ≡
      (2 : ℤ) ^ E
      [ZMOD (2 : ℤ) ^ (E + 1)] := by
  let M : ℕ := Arithmetic.twoPowModulus (E + 1)
  have hZ := completionCocycleResidue_spec_zmod m E
  have hCast :
      (((3 : ℤ) ^ (m + 1) *
          (completionCocycleResidue m E : ℤ) + 1 : ℤ) : ZMod M) =
        (((2 : ℤ) ^ E : ℤ) : ZMod M) := by
    push_cast at hZ ⊢
    simpa [M, Arithmetic.twoPowModulus] using hZ
  have hMod :
      (3 : ℤ) ^ (m + 1) * (completionCocycleResidue m E : ℤ) + 1 ≡
        (2 : ℤ) ^ E [ZMOD (M : ℤ)] :=
    (ZMod.intCast_eq_intCast_iff
      ((3 : ℤ) ^ (m + 1) * (completionCocycleResidue m E : ℤ) + 1)
      ((2 : ℤ) ^ E)
      M).1 hCast
  simpa [M, Arithmetic.twoPowModulus] using hMod

/--
2冪法では `3^p` は単元なので、左から掛かった `3^p` を合同式から cancel できる。
後続 residue transition 用の局所補題。
-/
private theorem cancel_threePow_modEq
    {p H : ℕ}
    {a b : ℤ}
    (h :
      (3 : ℤ) ^ p * a ≡ (3 : ℤ) ^ p * b
        [ZMOD (2 : ℤ) ^ H]) :
    a ≡ b [ZMOD (2 : ℤ) ^ H] := by
  rcases Int.mod_coprime (Arithmetic.coprime_threePow_twoPow p H) with
    ⟨y, hy⟩
  have hy' :
      (3 : ℤ) ^ p * y ≡ 1 [ZMOD (2 : ℤ) ^ H] := by
    simpa using hy
  have hMul := h.mul_left y
  have hya := hy'.mul_right a
  have hyb := hy'.mul_right b
  have hMul' :
      ((3 : ℤ) ^ p * y) * a ≡
        ((3 : ℤ) ^ p * y) * b
        [ZMOD (2 : ℤ) ^ H] := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using hMul
  simpa using hya.symm.trans (hMul'.trans hyb)

/--
同じ defect scale を保つ場合の canonical residue transition。

`3 r_(m+1) ≡ r_m (mod 2^(δ+2))`。
-/
theorem completionCocycleResidue_flat_transition_modEq
    (m δ : ℕ) :
    3 * (completionCocycleResidue (m + 1) (δ + 1) : ℤ) ≡
      (completionCocycleResidue m (δ + 1) : ℤ)
      [ZMOD (2 : ℤ) ^ (δ + 2)] := by
  let r0 : ℤ := completionCocycleResidue m (δ + 1)
  let r1 : ℤ := completionCocycleResidue (m + 1) (δ + 1)
  let A : ℤ := (3 : ℤ) ^ (m + 1)
  let M : ℤ := (2 : ℤ) ^ (δ + 2)
  have h0 := completionCocycleResidue_spec_intModEq m (δ + 1)
  have h1 := completionCocycleResidue_spec_intModEq (m + 1) (δ + 1)
  have hEq :
      A * (3 * r1) + 1 ≡ A * r0 + 1 [ZMOD M] := by
    calc
      A * (3 * r1) + 1 =
          (3 : ℤ) ^ ((m + 1) + 1) * r1 + 1 := by
            dsimp [A]
            rw [pow_succ]
            ring
      _ ≡ (2 : ℤ) ^ (δ + 1) [ZMOD M] := by
            simpa [r1, M, Nat.add_assoc] using h1
      _ ≡ A * r0 + 1 [ZMOD M] := by
            simpa [A, r0, M, Nat.add_assoc] using h0.symm
  have hMul : A * (3 * r1) ≡ A * r0 [ZMOD M] :=
    Int.ModEq.add_right_cancel' 1 hEq
  have hCancel : 3 * r1 ≡ r0 [ZMOD M] := by
    simpa [A, M] using
      (cancel_threePow_modEq (p := m + 1) (H := δ + 2) hMul)
  simpa [r0, r1, M] using hCancel

/--
次 defect が `+1` へ上がる場合の canonical residue transition。

`3 r_(m+1) ≡ r_m + 2^(δ+1) (mod 2^(δ+2))`。
-/
theorem completionCocycleResidue_rise_transition_modEq
    (m δ : ℕ) :
    3 * (completionCocycleResidue (m + 1) (δ + 2) : ℤ) ≡
      (completionCocycleResidue m (δ + 1) : ℤ) + (2 : ℤ) ^ (δ + 1)
      [ZMOD (2 : ℤ) ^ (δ + 2)] := by
  let r0 : ℤ := completionCocycleResidue m (δ + 1)
  let r1 : ℤ := completionCocycleResidue (m + 1) (δ + 2)
  let A : ℤ := (3 : ℤ) ^ (m + 1)
  let half : ℤ := (2 : ℤ) ^ (δ + 1)
  let M : ℤ := (2 : ℤ) ^ (δ + 2)
  let M2 : ℤ := (2 : ℤ) ^ (δ + 3)
  have h0 := completionCocycleResidue_spec_intModEq m (δ + 1)
  have h1 := completionCocycleResidue_spec_intModEq (m + 1) (δ + 2)
  have hDiv : M ∣ M2 := by
    refine ⟨2, ?_⟩
    dsimp [M, M2]
    rw [show δ + 3 = (δ + 2) + 1 by omega, pow_succ]
  have h1weak :
      (3 : ℤ) ^ ((m + 1) + 1) * r1 + 1 ≡
        (2 : ℤ) ^ (δ + 2) [ZMOD M] := by
    have hw := h1.of_dvd hDiv
    simpa [r1, M, M2, Nat.add_assoc] using hw
  rcases threePow_odd_nat (m + 1) with ⟨q, hq⟩
  have hA : A = 2 * (q : ℤ) + 1 := by
    dsimp [A]
    exact_mod_cast hq
  have hHalf : A * half ≡ half [ZMOD M] := by
    apply Int.modEq_iff_dvd.2
    refine ⟨-(q : ℤ), ?_⟩
    dsimp [M, half]
    rw [hA]
    rw [show δ + 2 = (δ + 1) + 1 by omega, pow_succ]
    ring
  have hCandidate :
      A * (r0 + half) + 1 ≡ M [ZMOD M] := by
    have hs := h0.add hHalf
    have hs' :
        (A * r0 + 1) + A * half ≡ half + half [ZMOD M] := by
      simpa [A, r0, half, M, Nat.add_assoc] using hs
    convert hs' using 1 <;> dsimp [M, half] <;> ring
  have hNext :
      A * (3 * r1) + 1 ≡ M [ZMOD M] := by
    calc
      A * (3 * r1) + 1 =
          (3 : ℤ) ^ ((m + 1) + 1) * r1 + 1 := by
            dsimp [A]
            rw [pow_succ]
            ring
      _ ≡ (2 : ℤ) ^ (δ + 2) [ZMOD M] := h1weak
      _ = M := by rfl
  have hEq :
      A * (3 * r1) + 1 ≡ A * (r0 + half) + 1 [ZMOD M] :=
    hNext.trans hCandidate.symm
  have hMul :
      A * (3 * r1) ≡ A * (r0 + half) [ZMOD M] :=
    Int.ModEq.add_right_cancel' 1 hEq
  have hCancel :
      3 * r1 ≡ r0 + half [ZMOD M] := by
    simpa [A, M] using
      (cancel_threePow_modEq (p := m + 1) (H := δ + 2) hMul)
  simpa [r0, r1, half, M] using hCancel

/-- flat residue transition を通常の整数 equality と quotient digit に展開する。 -/
theorem exists_completionCocycleResidue_flat_transition_digit
    (m δ : ℕ) :
    ∃ k : ℤ,
      3 * (completionCocycleResidue (m + 1) (δ + 1) : ℤ) =
        (completionCocycleResidue m (δ + 1) : ℤ) +
          (2 : ℤ) ^ (δ + 2) * k := by
  have h := completionCocycleResidue_flat_transition_modEq m δ
  rcases (Int.modEq_iff_add_fac.mp h) with ⟨t, ht⟩
  refine ⟨-t, ?_⟩
  rw [ht]
  ring

/-- rise residue transition を通常の整数 equality と quotient digit に展開する。 -/
theorem exists_completionCocycleResidue_rise_transition_digit
    (m δ : ℕ) :
    ∃ k : ℤ,
      3 * (completionCocycleResidue (m + 1) (δ + 2) : ℤ) =
        (completionCocycleResidue m (δ + 1) : ℤ) +
          (2 : ℤ) ^ (δ + 1) +
          (2 : ℤ) ^ (δ + 2) * k := by
  have h := completionCocycleResidue_rise_transition_modEq m δ
  rcases (Int.modEq_iff_add_fac.mp h) with ⟨t, ht⟩
  refine ⟨-t, ?_⟩
  rw [ht]
  ring

end Bridge

namespace OddOrbit

open Bridge

/--
flat 時の normalized residue exact transition。

`3 rho_(m+1) = rho_m + 4 k`。
-/
theorem exists_normalizedCompletionCocycleResidue_flat_transition_digit
    (m δ : ℕ) :
    ∃ k : ℤ,
      3 * normalizedCompletionCocycleResidue (m + 1) δ =
        normalizedCompletionCocycleResidue m δ + 4 * (k : ℝ) := by
  rcases exists_completionCocycleResidue_flat_transition_digit m δ with
    ⟨k, hk⟩
  refine ⟨k, ?_⟩
  unfold normalizedCompletionCocycleResidue
  have hkR := congrArg (fun z : ℤ => (z : ℝ)) hk
  push_cast at hkR
  have hPow :
      (2 : ℝ) ^ (δ + 2) = 4 * (2 : ℝ) ^ δ := by
    rw [pow_add]
    norm_num
    simp [mul_comm]
  rw [hPow] at hkR
  field_simp
  nlinarith

/--
rise 時の normalized residue exact transition。

`6 rho_(m+1) = rho_m + 2 + 4 k`。
-/
theorem exists_normalizedCompletionCocycleResidue_rise_transition_digit
    (m δ : ℕ) :
    ∃ k : ℤ,
      6 * normalizedCompletionCocycleResidue (m + 1) (δ + 1) =
        normalizedCompletionCocycleResidue m δ + 2 + 4 * (k : ℝ) := by
  rcases exists_completionCocycleResidue_rise_transition_digit m δ with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  unfold normalizedCompletionCocycleResidue
  have hkR := congrArg (fun z : ℤ => (z : ℝ)) hk
  push_cast at hkR
  have hHalf : (2 : ℝ) ^ (δ + 1) = 2 * (2 : ℝ) ^ δ := by
    rw [pow_succ]
    ring
  have hMod : (2 : ℝ) ^ (δ + 2) = 4 * (2 : ℝ) ^ δ := by
    rw [pow_add]
    norm_num
    ring
  rw [hHalf, hMod] at hkR
  rw [pow_succ]
  field_simp
  nlinarith

end OddOrbit
end Collatz3
