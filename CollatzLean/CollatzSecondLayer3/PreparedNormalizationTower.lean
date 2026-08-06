import CollatzLean.CollatzWindowCore.NormalizationFromWindow
import CollatzLean.CollatzSecondLayer3.PositiveObjects

/-!
# persistent capture部分列のnormalization tower

標準prepared full-window familyでcaptureが任意に遠く現れるなら、
そのcapture位置を狭義単調に選び、各項について一つの初期ordered windowから

* first deferredを持つ有限normalization
* deferredなしのeventual synchronization

のいずれかを実データとして選択する。
-/

namespace CollatzSecondLayer3

open CollatzSupport
open CollatzExternal
open CollatzCore

/-- persistent capture項とそのnormalization outcomeを束ねたtower。 -/
structure PreparedCaptureNormalizationTowerData
    {O : OddOrbit} {F : MovingFirstCrossingData O}
    (P : PolynomialPreparedFullWindowFamily F) where
  select : ℕ → ℕ
  select_strict : StrictMono select
  captured : ∀ j : ℕ,
    O.CapturedWindowAt
      (P.start (select j))
      (F.crossingLength (select j))
  normalization : ∀ j : ℕ,
    OddOrbit.CaptureNormalizationFromWindowOutcome
      (P.packet (select j)).toWindowDifferenceData
  lengths_tend_to_infinity :
    ∀ M : ℕ, ∃ J : ℕ, ∀ j : ℕ, J ≤ j →
      M < F.crossingLength (select j)

/-- persistent captureから標準normalization towerを構成する。 -/
noncomputable def PolynomialPreparedFullWindowFamily.normalizationTower
    {O : OddOrbit} {F : MovingFirstCrossingData O}
    (P : PolynomialPreparedFullWindowFamily F)
    (h : P.HasPersistentCapture) :
    PreparedCaptureNormalizationTowerData P := by
  classical
  let select := P.persistentCaptureSelect h
  refine
    { select := select
      select_strict := P.persistentCaptureSelect_strict h
      captured := ?_
      normalization := ?_
      lengths_tend_to_infinity := ?_ }
  · intro j
    exact Classical.choice (P.persistentCaptureSelect_captured h j)
  · intro j
    exact Classical.choice
      (OddOrbit.captureNormalizationFromWindowOutcome_nonempty
        (P.packet (select j)).toWindowDifferenceData)
  · intro M
    obtain ⟨J, hJ⟩ := F.lengths_tend_to_infinity M
    refine ⟨J, ?_⟩
    intro j hj
    apply hJ (select j)
    have hsel : j ≤ select j :=
      P.persistentCaptureSelect_ge h j
    exact le_trans hj hsel

end CollatzSecondLayer3
