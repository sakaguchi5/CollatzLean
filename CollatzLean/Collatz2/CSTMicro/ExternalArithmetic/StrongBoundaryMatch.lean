import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.BoundaryACandidate
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.StrongDenominatorWindowCover

/-!
# Strong finite matching target for Boundary A

current certified precision

  q_{j+1} + q_{j-1}

より強い

  q_j + q_{j+1} - 1

まで corrected packet と boundary Xi candidate が一致することを、
実際に証明すべき finite arithmetic target として切り出す。

この structure 自体は theorem の代用品ではない。
次段で critical Sturmian overlap を formalize したときに埋める唯一の field を
明示するための interface である。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/-- actual corrected packet の stronger finite 2-adic matching certificate。 -/
structure StrongBoundaryLopezStollMatch
    (L : LopezStollInstantiation) where
  xiTargetAgreement :
    ∀ j e R : ℕ,
      L.start ≤ j →
      e ≤ strongDenominatorWindowUpper L.q j →
      BoundaryXiCandidate e R →
      MatchesAtTwoPower e (L.P j) (L.Q j) R

/-- start 以降で previous denominator が current denominator より真に小さい。 -/
def PreviousDenominatorStrict
    (L : LopezStollInstantiation) : Prop :=
  ∀ j : ℕ,
    L.start ≤ j →
    L.q (j - 1) < L.q j

/-- stronger upper endpoint は current coarse upper endpoint を含む。 -/
theorem denominatorWindowUpper_le_strongDenominatorWindowUpper
    (L : LopezStollInstantiation)
    (hStrict : PreviousDenominatorStrict L)
    {j : ℕ}
    (hj : L.start ≤ j) :
    denominatorWindowUpper L.q j ≤
      strongDenominatorWindowUpper L.q j := by
  have hPrev : L.q (j - 1) < L.q j := hStrict j hj
  unfold denominatorWindowUpper strongDenominatorWindowUpper
  omega

namespace StrongBoundaryLopezStollMatch

/--
strong matching と denominator の strict growth があれば、
既存 coarse `BoundaryLopezStollMatch` は自動で従う。

したがって strong route を追加しても current fallback theorem は失わない。
-/
theorem toBoundaryLopezStollMatch
    {L : LopezStollInstantiation}
    (M : StrongBoundaryLopezStollMatch L)
    (hStrict : PreviousDenominatorStrict L) :
    BoundaryLopezStollMatch L := by
  refine ⟨?_⟩
  intro j e R hjStart hPrecision hCandidate
  apply M.xiTargetAgreement j e R hjStart
  · exact le_trans hPrecision
      (denominatorWindowUpper_le_strongDenominatorWindowUpper
        L hStrict hjStart)
  · exact hCandidate

end StrongBoundaryLopezStollMatch

/-- stronger windows で最初に covered になる precision。 -/
def strongFirstPrecision
    (L : LopezStollInstantiation) : ℕ :=
  strongDenominatorWindowLower L.q L.start

end ExternalArithmetic
end CSTMicro
end Collatz2
