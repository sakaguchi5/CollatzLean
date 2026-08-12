import CollatzLean.Collatz2.Canonical.Replay
import CollatzLean.Collatz2.Local.DeterminantSign

/-!
# Collatz2: contracting replay extremality

旧 `j = 0` を primitive branch として置かない。
replay layer `q` の displacement を affine transfer determinant で exact に展開し、
contracting (`determinant < 0`) なら quotient を上げるほど displacement が減少することを示す。

従って `q = 0` は contracting replay family の最大 displacement layer として導出される。
-/

namespace Collatz2
namespace Word

/-- replay quotient `q` に対応する start。 -/
def replayStart (w : Word) (q : ℕ) : ℕ :=
  canonicalStart w + residueModulus w * q

/-- replay quotient `q` に対応する endpoint。 -/
def replayEnd (w : Word) (q : ℕ) : ℕ :=
  canonicalEnd w + 2 * 3 ^ oddSteps w * q

/-- replay layer の signed actual displacement。 -/
def replayDisplacement (w : Word) (q : ℕ) : ℤ :=
  (replayEnd w q : ℤ) - (replayStart w q : ℤ)

/--
replay displacement の exact affine formula。
傾きは word transfer の determinant `C-A` の2倍。
-/
theorem replayDisplacement_eq
    (w : Word) (q : ℕ) :
    replayDisplacement w q =
      ((canonicalEnd w : ℕ) : ℤ) - ((canonicalStart w : ℕ) : ℤ) +
        2 * (AffineTransfer.ofWord w).determinant * (q : ℤ) := by
  unfold replayDisplacement replayEnd replayStart
  push_cast
  rw [residueModulus_int_cast]
  rw [AffineTransfer.determinant_ofWord]
  rw [pow_succ]
  ring

/-- contracting word では `q=0` が全自然数 replay layer の最大 displacement。 -/
theorem zeroReplay_maximal_of_contracting
    {w : Word}
    (hC : Contracting w)
    (q : ℕ) :
    replayDisplacement w q ≤ replayDisplacement w 0 := by
  rw [replayDisplacement_eq, replayDisplacement_eq]
  simp only [Int.ofNat_zero, mul_zero, add_zero]
  have hd : (AffineTransfer.ofWord w).determinant < 0 := hC
  have hdNonpos : 2 * (AffineTransfer.ofWord w).determinant ≤ 0 := by
    omega
  have hqNonneg : (0 : ℤ) ≤ (q : ℤ) := by omega
  have hterm :
      (2 * (AffineTransfer.ofWord w).determinant) * (q : ℤ) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hdNonpos hqNonneg
  have hterm' :
      2 * (AffineTransfer.ofWord w).determinant * (q : ℤ) ≤ 0 := by
    simpa [mul_assoc] using hterm
  calc
    ((canonicalEnd w : ℕ) : ℤ) - ((canonicalStart w : ℕ) : ℤ) +
          2 * (AffineTransfer.ofWord w).determinant * (q : ℤ)
        ≤ ((canonicalEnd w : ℕ) : ℤ) - ((canonicalStart w : ℕ) : ℤ) + 0 :=
          Int.add_le_add_left hterm' _
    _ = ((canonicalEnd w : ℕ) : ℤ) - ((canonicalStart w : ℕ) : ℤ) := by ring

/-- 正の quotient では contracting replay displacement は0-layerより真に小さい。 -/
theorem replayDisplacement_lt_zero_of_contracting_of_pos
    {w : Word}
    (hC : Contracting w)
    {q : ℕ}
    (hq : 0 < q) :
    replayDisplacement w q < replayDisplacement w 0 := by
  rw [replayDisplacement_eq, replayDisplacement_eq]
  simp only [Int.ofNat_zero, mul_zero, add_zero]
  have hd :
      (AffineTransfer.ofWord w).determinant < 0 := hC
  have hdNeg :
      2 * (AffineTransfer.ofWord w).determinant < 0 := by
    omega
  have hqPos : (0 : ℤ) < (q : ℤ) := by
    exact_mod_cast hq
  have hterm :
      2 * (AffineTransfer.ofWord w).determinant * (q : ℤ) < 0 := by
    exact Int.mul_neg_of_neg_of_pos hdNeg hqPos
  have hadd :=
    add_lt_add_left hterm
      (((canonicalEnd w : ℕ) : ℤ) -
        ((canonicalStart w : ℕ) : ℤ))
  simpa only [zero_add, add_comm] using hadd

/--
contracting family のどこかの replay layer が positive return なら、
最大 layer `q=0` も positive return である。
これが旧 `j=0` を上位構造から取り出す基本 corollary。
-/
theorem zeroReplay_positive_of_positive_replay
    {w : Word}
    (hC : Contracting w)
    {q : ℕ}
    (hpos : 0 < replayDisplacement w q) :
    0 < replayDisplacement w 0 := by
  exact lt_of_lt_of_le hpos (zeroReplay_maximal_of_contracting hC q)

/--
任意の positive contracting ReplayCoordinate は canonical (`q=0`) positive return を強制する。
-/
theorem ReplayCoordinate.canonical_positive_of_positive
    {w : Word} {X Y : ℕ}
    (C : ReplayCoordinate w X Y)
    (hC : Contracting w)
    (hXY : X < Y) :
    canonicalStart w < canonicalEnd w := by
  have hLayerPos : 0 < replayDisplacement w C.quotient := by
    unfold replayDisplacement replayEnd replayStart
    rw [← C.finish_eq, ← C.start_eq]
    omega
  have hZeroPos : 0 < replayDisplacement w 0 :=
    zeroReplay_positive_of_positive_replay hC hLayerPos
  have hInt :
      ((canonicalStart w : ℕ) : ℤ) < ((canonicalEnd w : ℕ) : ℤ) := by
    simpa [replayDisplacement, replayEnd, replayStart] using hZeroPos
  exact_mod_cast hInt

end Word

namespace Runs

/--
非空 normalized run の positive contracting realization からも、
replay coordinate を経由して canonical positive return が得られる。
-/
theorem canonical_positive_of_contracting_positive
    {w : Word} {X Y : ℕ}
    (h : Runs w X Y)
    (hne : w ≠ [])
    (hC : Word.Contracting w)
    (hXY : X < Y) :
    Word.canonicalStart w < Word.canonicalEnd w := by
  let C : Word.ReplayCoordinate w X Y := Word.ReplayCoordinate.ofRuns h hne
  exact C.canonical_positive_of_positive hC hXY

end Runs
end Collatz2
