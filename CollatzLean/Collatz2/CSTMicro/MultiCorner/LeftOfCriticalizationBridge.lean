import CollatzLean.Collatz2.CSTMicro.MultiCorner.AttachedTwoCornerHensel
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBProfileNumeratorValuation

/-!
# MultiCorner: exposed corner left of criticalization

previous exposed `a` が arithmetic criticalization start `s` より左にある場合、
`[s,c)` の局所 carry geometry だけでは global extra corner を見失う。

そこで global profile numerator

  N = profileDyadicCellNumerator m h

の exact order

  v_3(N) = m-s

から、最初の nonzero 3-adic digitに相当する canonical quotient を取り出す。
これは将来 `C_s + R_s` と同定する対象だが、このファイルではその未証明 bridge を仮定しない。

同時に、left exposed の Record--Ferrers provenance を保持し、

  left geometry source  +  global 3-adic unit

を一つの packet として後段へ渡す。
-/

namespace Collatz2
namespace CSTMicro
namespace MultiCorner

open ExternalArithmetic

/--
exact divisibility witness から quotient を
計算可能な exact division として取り出す。
-/
def threeAdicExactQuotient
    (z : ℤ)
    (r : ℕ)
    (hDvd : (3 : ℤ) ^ r ∣ z) : ℤ :=
  Int.divExact z ((3 : ℤ) ^ r) hDvd

theorem threeAdicExactQuotient_spec
    (z : ℤ)
    (r : ℕ)
    (hDvd : (3 : ℤ) ^ r ∣ z) :
    z =
      (3 : ℤ) ^ r *
        threeAdicExactQuotient z r hDvd := by
  unfold threeAdicExactQuotient
  rw [Int.divExact_eq_ediv]
  exact (Int.mul_ediv_cancel' hDvd).symm

/-- exact order なら canonical quotient は 3-adic unit。 -/
theorem not_three_dvd_threeAdicExactQuotient_of_exactOrder
    {z : ℤ}
    {r : ℕ}
    (hExact : ExactThreeAdicOrder z r) :
    ¬ (3 : ℤ) ∣ threeAdicExactQuotient z r hExact.1 := by
  intro hThree
  rcases hThree with ⟨u, hu⟩
  apply hExact.2
  refine ⟨u, ?_⟩
  calc
    z =
        (3 : ℤ) ^ r *
          threeAdicExactQuotient z r hExact.1 :=
      threeAdicExactQuotient_spec z r hExact.1
    _ = (3 : ℤ) ^ r * ((3 : ℤ) * u) := by rw [hu]
    _ = (3 : ℤ) ^ (r + 1) * u := by
      rw [pow_succ]
      ring

/--
criticalization start で global numerator を exact に割った canonical unit。
将来の split-state `U_s = C_s + R_s` と同定する候補。
-/
def criticalizationUnit
    (P : PureBProfileObstruction)
    (hStart : 0 < P.criticalizationStart) : ℤ :=
  let hExact :=
    P.profileNumerator_exactThreeAdicOrder_at_criticalization hStart
  threeAdicExactQuotient
    (profileDyadicCellNumerator P.m P.h : ℤ)
    (P.m - P.criticalizationStart)
    hExact.1

/-- global numerator は `3^(m-s) * criticalizationUnit`。 -/
theorem profileNumerator_eq_threePow_mul_criticalizationUnit
    (P : PureBProfileObstruction)
    (hStart : 0 < P.criticalizationStart) :
    (profileDyadicCellNumerator P.m P.h : ℤ) =
      (3 : ℤ) ^ (P.m - P.criticalizationStart) *
        criticalizationUnit P hStart := by
  let hExact :=
    P.profileNumerator_exactThreeAdicOrder_at_criticalization hStart
  exact
    threeAdicExactQuotient_spec
      (profileDyadicCellNumerator P.m P.h : ℤ)
      (P.m - P.criticalizationStart)
      hExact.1

/-- canonical criticalization quotient は 3 で割れない。 -/
theorem criticalizationUnit_not_three_dvd
    (P : PureBProfileObstruction)
    (hStart : 0 < P.criticalizationStart) :
    ¬ (3 : ℤ) ∣ criticalizationUnit P hStart := by
  let hExact :=
    P.profileNumerator_exactThreeAdicOrder_at_criticalization hStart
  exact
    not_three_dvd_threeAdicExactQuotient_of_exactOrder hExact

/-- arithmetic criticalization より左に残る exposed corner とその provenance。 -/
structure LeftOfCriticalizationExposed
    (P : PureBProfileObstruction) where
  index : ℕ
  exposed_mem : index ∈ P.exposedPredecessorSet
  index_lt_criticalization : index < P.criticalizationStart
  provenance : RecordFerrersCutProvenance P index

namespace LeftOfCriticalizationExposed

/-- left exposed も local defect / glue carry のどちらかを必ず持つ。 -/
theorem source
    {P : PureBProfileObstruction}
    (L : LeftOfCriticalizationExposed P) :
    0 < L.provenance.localDefect ∨
      L.provenance.glueCarry = 1 :=
  L.provenance.source_of_mem_exposedPredecessorSet L.exposed_mem

/-- left exposed は geometric terminal start よりも当然左にある。 -/
theorem index_lt_terminalCriticalStart
    {P : PureBProfileObstruction}
    (L : LeftOfCriticalizationExposed P) :
    L.index < P.terminalCriticalStart := by
  have hLe := P.criticalizationStart_le_terminalCriticalStart
  have hLt := L.index_lt_criticalization
  omega

end LeftOfCriticalizationExposed

/--
last-two normal form の previous が `s` より左なら Case II packet を作れる。
provenance 自体は Record--Ferrers factorization 側から渡す。
-/
def leftOfCriticalizationExposed_of_lastTwoPrevious
    (P : PureBProfileObstruction)
    (N : LastTwoExposedNormalForm P)
    (hLeft : N.previous < P.criticalizationStart)
    (Q : RecordFerrersCutProvenance P N.previous) :
    LeftOfCriticalizationExposed P :=
  { index := N.previous
    exposed_mem := N.previous_mem
    index_lt_criticalization := hLeft
    provenance := Q }

/--
Case II の bridge packet。
left geometry と global exact 3-adic unit を同時に保持する。
-/
structure LeftOfCriticalizationBridge
    (P : PureBProfileObstruction) where
  hStart : 0 < P.criticalizationStart
  left : LeftOfCriticalizationExposed P

namespace LeftOfCriticalizationBridge

/-- bridge の global arithmetic half: canonical unit は 3 で割れない。 -/
theorem globalUnit_not_three_dvd
    {P : PureBProfileObstruction}
    (B : LeftOfCriticalizationBridge P) :
    ¬ (3 : ℤ) ∣ criticalizationUnit P B.hStart :=
  criticalizationUnit_not_three_dvd P B.hStart

/-- bridge の geometry half と arithmetic half を一つにまとめた形。 -/
theorem source_and_globalUnit
    {P : PureBProfileObstruction}
    (B : LeftOfCriticalizationBridge P) :
    (0 < B.left.provenance.localDefect ∨
      B.left.provenance.glueCarry = 1) ∧
    ¬ (3 : ℤ) ∣ criticalizationUnit P B.hStart := by
  constructor
  · exact B.left.source
  · exact B.globalUnit_not_three_dvd

/-- canonical quotient の defining equationも bridge から直接読める。 -/
theorem profileNumerator_eq_scaled_globalUnit
    {P : PureBProfileObstruction}
    (B : LeftOfCriticalizationBridge P) :
    (profileDyadicCellNumerator P.m P.h : ℤ) =
      (3 : ℤ) ^ (P.m - P.criticalizationStart) *
        criticalizationUnit P B.hStart :=
  profileNumerator_eq_threePow_mul_criticalizationUnit P B.hStart

end LeftOfCriticalizationBridge

end MultiCorner
end CSTMicro
end Collatz2
