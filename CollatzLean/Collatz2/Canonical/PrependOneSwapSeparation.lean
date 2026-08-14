import CollatzLean.Collatz2.Canonical.SwapResidue
import CollatzLean.Collatz2.Local.DeterminantSign
import CollatzLean.Collatz2.Geometry.Center
/-!
# Collatz2 Canonical: prepend-one cyclic swap separation

tail `v` に対し

  omega(v) := affineConst(v) + centerGap(v)

を natural separation magnitude とする。

tail が contracting なら exact に

  affineConst(v ++ [1])
    =
  affineConst(1 :: v) + omega(v)

である。

従って `omega(v)` は `[1]` と `v` の word-swap translation separation の
絶対方向そのもの。
-/

namespace Collatz2
namespace Word

/-- prepend-one cyclic swap の natural translation separation。 -/
def prependOneSwapSeparation (v : Word) : ℕ :=
  affineConst v + (AffineTransfer.ofWord v).centerGap

/-- contracting tail の gap equation。 -/
theorem Contracting.centerGap_add_threePow
    {v : Word}
    (hC : Contracting v) :
    (AffineTransfer.ofWord v).centerGap +
        3 ^ oddSteps v =
      2 ^ twoSteps v := by
  have hNeg :
      (AffineTransfer.ofWord v).determinant < 0 :=
    hC
  have hLe :
      (AffineTransfer.ofWord v).oddCoeff ≤
        (AffineTransfer.ofWord v).twoCoeff := by
    unfold AffineTransfer.determinant at hNeg
    omega
  have h :=
    Nat.sub_add_cancel hLe
  simpa [AffineTransfer.centerGap] using h

/--
contracting tail では swapped translation が original より
exact に `prependOneSwapSeparation` 大きい。
-/
theorem affineConst_swap_prependOne
    {v : Word}
    (hC : Contracting v) :
    affineConst (v ++ [1]) =
      affineConst (1 :: v) +
        prependOneSwapSeparation v := by
  have hGap := hC.centerGap_add_threePow
  have hRot :
      affineConst (v ++ [1]) =
        3 * affineConst v + 2 ^ twoSteps v := by
    rw [affineConst_append]
    simp [oddSteps, twoSteps, affineConst]
  have hFull :
      affineConst (1 :: v) =
        3 ^ oddSteps v + 2 * affineConst v := by
    simp [affineConst, oddSteps]
  rw [hRot, hFull]
  unfold prependOneSwapSeparation
  nlinarith

/--
word-swap `separation([1],v)` の符号反転が natural magnitude。
-/
theorem prependOneSwapSeparation_int_eq_neg_separation
    {v : Word}
    (hC : Contracting v) :
    (prependOneSwapSeparation v : ℤ) =
      -(AffineTransfer.ofWord ([1] : Word)).separation
        (AffineTransfer.ofWord v) := by
  have hSwap :=
    wordSwap_translate_sub ([1] : Word) v
  have hNat :=
    affineConst_swap_prependOne hC
  have hNatZ :
      (affineConst (v ++ [1]) : ℤ) =
        (affineConst (1 :: v) : ℤ) +
          (prependOneSwapSeparation v : ℤ) := by
    exact_mod_cast hNat
  have hSwap' :
      (affineConst (1 :: v) : ℤ) -
          (affineConst (v ++ [1]) : ℤ) =
        (AffineTransfer.ofWord ([1] : Word)).separation
          (AffineTransfer.ofWord v) := by
    simpa using hSwap
  linarith

end Word
end Collatz2
