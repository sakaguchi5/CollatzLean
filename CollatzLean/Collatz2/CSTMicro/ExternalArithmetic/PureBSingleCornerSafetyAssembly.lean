import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBSingleCornerFiniteBridge

/-!
# Pure B single-corner: Stage 4/5 safety assembly

Stage 4 が

  |E(B)| = 1 -> m < M0

を与え、Stage 5 の finite exact arithmetic が

  |E(B)| = 1 -> m < M0 -> False

を与えれば、actual minimal B の single-corner branch は完全に消える。

`PureBProfileObstruction.q` は actual bad packet では `Nat` なので、ここで formal に正しい
Single-Corner Safety は

  exposedPredecessorSet.card != 1

である。これは「single-corner なら本来 safe (`q<0`) でなければならないため、
bad packet としては存在しない」の actual-obstruction 版。

最後に `Gu>K <-> q<0` を signed CRT identity として別に定式化する。
これにより actual bad packet の `Nat q` と、安全側の signed q を混同しない。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/--
Stage 4 + Stage 5 の最終 assembler。
-/
theorem no_singleExposedCorner_of_large_and_finite
    {R : RhinLinearForm14}
    {M0 : ℕ}
    (hLarge : SingleCornerLargeMEliminationCertificate R M0)
    (hFinite : SingleCornerFiniteRangeEliminationCertificate M0)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L) :
    (M.toPureBProfileObstruction hL).exposedPredecessorSet.card ≠ 1 := by
  intro hCard
  have hm :
      (M.toPureBProfileObstruction hL).m < M0 :=
    hLarge.singleCorner_m_lt M hL hCard
  exact hFinite.eliminate M hL hCard hm

/--
Single-Corner Safety の word-level form。

actual minimal bad packet に `|E(B)|=1` を仮定すると contradiction なので、
その branch の word は vacuously `WordPureSeparation` を満たす。
実際の数学的内容は直前 theorem の `card != 1`。
-/
theorem singleCorner_wordPureSeparation
    {R : RhinLinearForm14}
    {M0 : ℕ}
    (hLarge : SingleCornerLargeMEliminationCertificate R M0)
    (hFinite : SingleCornerFiniteRangeEliminationCertificate M0)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (hCard :
      (M.toPureBProfileObstruction hL).exposedPredecessorSet.card = 1) :
    WordPureSeparation M.word := by
  exact False.elim
    ((no_singleExposedCorner_of_large_and_finite
      hLarge hFinite M hL) hCard)

/-! ## signed CRT form of `Gu > K` -/

/--
数学側で得た single-corner CRT identity の Lean interface。

  den * q = K - G*u,
  den > 0.

`q` は safety/badness の符号を保持するため `ℤ`。
-/
structure SingleCornerCRTIdentity where
  G : ℕ
  u : ℕ
  K : ℕ
  den : ℕ
  q : ℤ
  den_pos : 0 < den
  balance :
    (den : ℤ) * q =
      (K : ℤ) - ((G * u : ℕ) : ℤ)

namespace SingleCornerCRTIdentity

/--
exact equivalence

  q < 0  <->  G*u > K.

したがって `Gu>K` は単なる sufficient condition ではなく single-corner safety そのもの。
-/
theorem q_neg_iff_G_mul_u_gt_K
    (C : SingleCornerCRTIdentity) :
    C.q < 0 ↔ C.K < C.G * C.u := by
  have hden : (0 : ℤ) < C.den := by
    exact_mod_cast C.den_pos
  constructor
  · intro hq
    have hmul : (C.den : ℤ) * C.q < 0 :=
      mul_neg_of_pos_of_neg hden hq
    have hk :
        (C.K : ℤ) < ((C.G * C.u : ℕ) : ℤ) := by
      rw [C.balance] at hmul
      linarith
    exact_mod_cast hk
  · intro hGu
    have hGuZ :
        (C.K : ℤ) < ((C.G * C.u : ℕ) : ℤ) := by
      exact_mod_cast hGu
    have hmul : (C.den : ℤ) * C.q < 0 := by
      rw [C.balance]
      linarith
    by_contra hnot
    have hq0 : (0 : ℤ) ≤ C.q := by omega
    have hnonneg :
        (0 : ℤ) ≤ (C.den : ℤ) * C.q :=
      mul_nonneg (le_of_lt hden) hq0
    linarith

end SingleCornerCRTIdentity

/-! ## real fixed-point inequality without division -/

/--
`R > A/G` を division-free に保持する最小 arithmetic packet。
-/
structure SingleCornerFixedPointData where
  A : ℕ
  G : ℕ
  R : ℕ
  G_pos : 0 < G

namespace SingleCornerFixedPointData

/-- division-free safety。 -/
def Safe (D : SingleCornerFixedPointData) : Prop :=
  D.A < D.G * D.R

/--
自然数 capacity `A/G` 版。
strict real inequalityそのものを Nat divisionに置換するのではなく、
repo の `MicroObject` と同じ division-free statementを primary にする。
-/
theorem safe_iff_div_lt_R
    (D : SingleCornerFixedPointData) :
    D.Safe ↔ D.A / D.G < D.R := by
  unfold Safe
  constructor
  · intro h
    exact (Nat.div_lt_iff_lt_mul D.G_pos).2
      (by simpa [Nat.mul_comm] using h)
  · intro h
    have h' := (Nat.div_lt_iff_lt_mul D.G_pos).1 h
    simpa [Nat.mul_comm] using h'

end SingleCornerFixedPointData

end ExternalArithmetic
end CSTMicro
end Collatz2
