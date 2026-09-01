import CollatzLean.Collatz2.Geometry.CriticalFerrersThreeAdicActualWord
import CollatzLean.Collatz2.Core.Realization

/-!
# Collatz2 Geometry: 3進 anchor

actual realization

  2^H y = 3^r x + B

に `3^s ∣ x` を入れると、入口項は `3^(r+s)` で消える。
したがって

  B ≡ 2^H y (mod 3^(r+s))

が得られる。

ここでは可変 modulus の `ZMod` を型に埋め込まず、整数の divisibility として保持する。
-/

namespace Collatz2
namespace Word

/--
`3^s` で割れる入口を持つ realization では、translation と出口項の差に
`3^(r+s)` が入る。
-/
theorem threePow_dvd_realization_residual
    {w : Word}
    {x y s : ℕ}
    (hR : Realizes w x y)
    (hx : 3 ^ s ∣ x) :
    ((3 : ℤ) ^ (oddSteps w + s) ∣
      (2 : ℤ) ^ twoSteps w * (y : ℤ) - (affineConst w : ℤ)) := by
  rcases hx with ⟨t, rfl⟩
  rw [realizes_iff] at hR
  have hRZ :
      (2 : ℤ) ^ twoSteps w * (y : ℤ) =
        (3 : ℤ) ^ oddSteps w * ((3 ^ s * t : ℕ) : ℤ) +
          (affineConst w : ℤ) := by
    exact_mod_cast hR
  refine ⟨(t : ℤ), ?_⟩
  rw [pow_add]
  rw [hRZ]
  push_cast
  ring

/--
同じ `(r,H)` と同じ出口 `y` を持ち、両入口が `3^s` で割れる二 realization では、
二つの `affineConst` は modulo `3^(r+s)` で一致する。
-/
theorem threePow_dvd_affineConst_diff_of_anchored_realizations
    {u v : Word}
    {xu xv y s : ℕ}
    (hRu : Realizes u xu y)
    (hRv : Realizes v xv y)
    (hxu : 3 ^ s ∣ xu)
    (hxv : 3 ^ s ∣ xv)
    (hp : oddSteps u = oddSteps v)
    (hH : twoSteps u = twoSteps v) :
    ((3 : ℤ) ^ (oddSteps u + s) ∣
      (affineConst u : ℤ) - (affineConst v : ℤ)) := by
  have hu := threePow_dvd_realization_residual hRu hxu
  have hv := threePow_dvd_realization_residual hRv hxv
  rw [← hp, ← hH] at hv
  rcases hu with ⟨a, ha⟩
  rcases hv with ⟨b, hb⟩
  refine ⟨b - a, ?_⟩
  have hEqU := ha
  have hEqV := hb
  ring_nf at hEqU hEqV ⊢
  linarith

/-- `3 ∣ x` は通常の `3^r` より一桁深い `3^(r+1)` anchor を与える。 -/
theorem threePow_succ_dvd_realization_residual_of_three_dvd_start
    {w : Word}
    {x y : ℕ}
    (hR : Realizes w x y)
    (hx : 3 ∣ x) :
    ((3 : ℤ) ^ (oddSteps w + 1) ∣
      (2 : ℤ) ^ twoSteps w * (y : ℤ) - (affineConst w : ℤ)) := by
  simpa using threePow_dvd_realization_residual
    (w := w) (x := x) (y := y) (s := 1) hR (by simpa using hx)

end Word
end Collatz2
