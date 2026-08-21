import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBSingleCornerStrongXiPort

/-!
# Pure B single-corner: Stage 4 large-m reduction, sharpened Xi threshold

Strong Xi port の usable precision は finite Xi scan により

  1538  ->  118

へ改善された。

single-corner packet `S` について

  e := beta(S.b - 1)

が

  118 <= e,
  m + 1 <= e + 2

を満たせば、actual left-prefix divisibility と合わせて contradiction になる。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

namespace PureBProfileObstruction.SingleExposedCornerRigidityPacket

/-- strong left Xi port が読む precision。 -/
def strongLeftPrecision
    {P : PureBProfileObstruction}
    (S : P.SingleExposedCornerRigidityPacket) : ℕ :=
  beattyIndex (S.b - 1)

/--
sharpened strong Xi port に入るための purely geometric readiness。
-/
def StrongLeftReady
    {P : PureBProfileObstruction}
    (S : P.SingleExposedCornerRigidityPacket) : Prop :=
  118 ≤ S.strongLeftPrecision ∧
    P.m + 1 ≤ S.strongLeftPrecision + 2

/-- `StrongLeftReady` を展開した wrapper。 -/
theorem strongLeftReady_iff
    {P : PureBProfileObstruction}
    (S : P.SingleExposedCornerRigidityPacket) :
    S.StrongLeftReady ↔
      118 ≤ beattyIndex (S.b - 1) ∧
        P.m + 1 ≤ beattyIndex (S.b - 1) + 2 := by
  rfl

end PureBProfileObstruction.SingleExposedCornerRigidityPacket

namespace MinimalActualABObstructionPacket

/-- actual single-corner left divisibility の名前付き predicate。 -/
def SingleCornerLeftPrefixDivisibility
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (S :
      (M.toPureBProfileObstruction hL).SingleExposedCornerRigidityPacket) : Prop :=
  (2 : ℤ) ^ beattyIndex (S.b - 1) ∣
    (3 : ℤ) ^ (S.b - 1) *
        (M.actual.firstFailureEdge.step.edge.upperR : ℤ) +
      criticalPrefixPhiZ (S.b - 1)

/--
strong-ready single-corner は left prefix divisibility があれば即 contradiction。
-/
theorem singleCorner_impossible_of_strongLeftReady
    (R : RhinLinearForm14)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (S :
      (M.toPureBProfileObstruction hL).SingleExposedCornerRigidityPacket)
    (hDiv : M.SingleCornerLeftPrefixDivisibility hL S)
    (hReady : S.StrongLeftReady) :
    False := by
  exact
    M.singleCorner_left_impossible_of_strongRange
      R hL S hDiv hReady.1 hReady.2

end MinimalActualABObstructionPacket

/--
Stage 4 の concrete large-m certificate。
-/
structure SingleCornerLargeMEliminationCertificate
    (R : RhinLinearForm14)
    (M0 : ℕ) where
  leftPrefixDivisibility :
    ∀ {L : ℕ}
      (M : MinimalActualABObstructionPacket L)
      (hL : 2 < L)
      (hCard :
        (M.toPureBProfileObstruction hL).exposedPredecessorSet.card = 1),
      let S := M.toSingleExposedCornerRigidityPacket R hL hCard
      M.SingleCornerLeftPrefixDivisibility hL S

  strongReady_of_large :
    ∀ {L : ℕ}
      (M : MinimalActualABObstructionPacket L)
      (hL : 2 < L)
      (hCard :
        (M.toPureBProfileObstruction hL).exposedPredecessorSet.card = 1),
      M0 ≤ (M.toPureBProfileObstruction hL).m →
      let S := M.toSingleExposedCornerRigidityPacket R hL hCard
      S.StrongLeftReady

namespace SingleCornerLargeMEliminationCertificate

/--
certificate が構成できれば single-corner bad packet の odd depth は exact に `m < M0`。
-/
theorem singleCorner_m_lt
    {R : RhinLinearForm14}
    {M0 : ℕ}
    (C : SingleCornerLargeMEliminationCertificate R M0)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (hCard :
      (M.toPureBProfileObstruction hL).exposedPredecessorSet.card = 1) :
    (M.toPureBProfileObstruction hL).m < M0 := by
  by_contra hnot
  have hLarge :
      M0 ≤ (M.toPureBProfileObstruction hL).m := by
    omega
  let S := M.toSingleExposedCornerRigidityPacket R hL hCard
  have hDiv : M.SingleCornerLeftPrefixDivisibility hL S := by
    simpa [S] using C.leftPrefixDivisibility M hL hCard
  have hReady : S.StrongLeftReady := by
    simpa [S] using C.strongReady_of_large M hL hCard hLarge
  exact M.singleCorner_impossible_of_strongLeftReady R hL S hDiv hReady

end SingleCornerLargeMEliminationCertificate

end ExternalArithmetic
end CSTMicro
end Collatz2
