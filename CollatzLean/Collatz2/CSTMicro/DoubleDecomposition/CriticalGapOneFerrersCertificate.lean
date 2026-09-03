import CollatzLean.Collatz2.CSTMicro.DoubleDecomposition.GapOneParadoxical
import CollatzLean.Collatz2.CSTMicro.DoubleDecomposition.CriticalDefectProfile

/-!
# critical affine budget を固定した gap-one certificate

既存 `GapOneFerrersDeficitCertificate` は `Bcrit` を外部変数として受け取るため、
`Bcrit` が本当に critical roof の affine budget であること自体は要求していない。

第3例探索ではここを固定する必要がある。
さらに 7・91 型では、最後の下降点までの word は単なる valid word ではなく
`FirstCrossing` でなければならない。

そこで本ファイルでは

  Bcrit = Word.criticalAffineConst p

を型の段階で固定し、同時に `ValidMinimalCrossingBlock w` を保持する
強化 certificate を導入する。
-/

namespace Collatz2
namespace CSTMicro
namespace DoubleDecomposition

/--
7・91 型の第3例探索に使う強化 Ferrers certificate。

* `minimal` により、`w` は coefficient が初めて contracting になる block。
* critical budget は外部変数にせず `Word.criticalAffineConst p` に固定。
* `affine_budget` は actual affine constant と Ferrers deficit の exact 分解。
* 残り二式が gap-one return の算術 certificate。
-/
structure CriticalGapOneFerrersDeficitCertificate
    (w : Word)
    (p H deficit gap m : ℕ) : Prop where
  minimal : ValidMinimalCrossingBlock w
  oddSteps_eq : Word.oddSteps w = p
  twoSteps_eq : Word.twoSteps w = H
  affine_budget :
    Word.affineConst w + deficit = Word.criticalAffineConst p
  deficit_equation :
    3 ^ p + Word.criticalAffineConst p =
      2 ^ H + deficit + m * gap
  next_gap_equation :
    3 ^ (p + 1) + gap = 2 ^ (H + 1)
  multiplier_pos : 0 < m

/--
強化 certificate は既存の一般 certificate へ忘却できる。
ここで `Bcrit` は exact に `Word.criticalAffineConst p` へ固定される。
-/
theorem CriticalGapOneFerrersDeficitCertificate.toGapOneFerrersDeficitCertificate
    {w : Word}
    {p H deficit gap m : ℕ}
    (C : CriticalGapOneFerrersDeficitCertificate
      w p H deficit gap m) :
    GapOneFerrersDeficitCertificate
      w p H (Word.criticalAffineConst p) deficit gap m := by
  have hMinimal : w.Valid ∧ Word.FirstCrossing w := by
    exact C.minimal
  exact {
    valid := hMinimal.1
    oddSteps_eq := C.oddSteps_eq
    twoSteps_eq := C.twoSteps_eq
    affine_budget := C.affine_budget
    deficit_equation := C.deficit_equation
    next_gap_equation := C.next_gap_equation
    multiplier_pos := C.multiplier_pos
  }

/-- 強化 certificate から whole affine realization を復元する。 -/
theorem realizes_gapOne_of_criticalFerrersDeficitEquation
    {w : Word}
    {p H deficit gap m : ℕ}
    (C : CriticalGapOneFerrersDeficitCertificate
      w p H deficit gap m) :
    Word.Realizes w (3 * m + 1) (2 * m + 1) := by
  exact realizes_gapOne_of_ferrersDeficitEquation
    C.toGapOneFerrersDeficitCertificate

/--
critical budget を固定した certificate から genuine gap-one run を得る。

既存5番との違いは、`w` が minimal FirstCrossing であることと、
`Bcrit` が `Word.criticalAffineConst p` に固定されていることである。
このため 19 のような「最後は start+1 へ戻るが、その前にすでに下降済み」の
偽の第3例を certificate の入口で排除できる。
-/
theorem gapOneParadoxical_of_criticalFerrersDeficitEquation
    {w : Word}
    {p H deficit gap m : ℕ}
    (C : CriticalGapOneFerrersDeficitCertificate
      w p H deficit gap m) :
    Runs w (3 * m + 1) (2 * m + 1) ∧
      2 * m + 1 < 3 * m + 1 ∧
      Word.Realizes ([1] : Word) (2 * m + 1) (3 * m + 2) := by
  exact gapOneParadoxical_of_ferrersDeficitEquation
    C.toGapOneFerrersDeficitCertificate

end DoubleDecomposition
end CSTMicro
end Collatz2
