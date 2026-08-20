import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBSingleCornerFiniteArithmetic

/-!
# Pure B single-corner: finite model -> actual B bridge target

`PureBSingleCornerFiniteArithmetic` は `(m,b,c)` から作る pure arithmetic model を
`m <= 500` まで exact native check する。

actual minimal B の finite branch を閉じるには、single-corner rigidity packetから得る

  m,
  b,
  c = terminalCriticalStart

がその executable model と同じ affine numerator / same canonical residue を持つことを
一度だけ示せばよい。

このファイルはその bridge の最小 interface を固定する。
外部数論仮定ではなく、既存 actual profile-coordinate bridge と canonical representative
trace から構成すべき finite-model correctness certificate である。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/--
Stage 5 の actual finite-range elimination certificate。

finite arithmetic model の correctness bridgeを埋めた最終 output はこの structure の inhabitant になる。
-/
structure SingleCornerFiniteRangeEliminationCertificate
    (M0 : ℕ) where
  eliminate :
    ∀ {L : ℕ}
      (M : MinimalActualABObstructionPacket L)
      (hL : 2 < L)
      (_hCard :
        (M.toPureBProfileObstruction hL).exposedPredecessorSet.card = 1),
      (M.toPureBProfileObstruction hL).m < M0 →
      False

/--
finite arithmetic model と actual single-corner packet の一致 certificate。

`model_safe` field は native scanner が返す division-free inequalityを actual bad packetの
`WordPureSeparation` に移す最終 correctness bridge。
-/
structure SingleCornerFiniteModelBridge
    (M0 : ℕ) where
  model_safe :
    ∀ {L : ℕ}
      (M : MinimalActualABObstructionPacket L)
      (hL : 2 < L)
      (_hCard :
        (M.toPureBProfileObstruction hL).exposedPredecessorSet.card = 1),
      (M.toPureBProfileObstruction hL).m < M0 →
      singleCornerFiniteModelCheckBelow M0 = true →
      WordPureSeparation M.word

namespace SingleCornerFiniteModelBridge

/--
model bridge と native finite check から Stage-5 actual elimination certificate を作る。

minimal B は definition 上 `WordPureSeparation` failure なので、model-safe と矛盾する。
-/
theorem toFiniteRangeEliminationCertificate
    {M0 : ℕ}
    (B : SingleCornerFiniteModelBridge M0)
    (hCheck : singleCornerFiniteModelCheckBelow M0 = true) :
    SingleCornerFiniteRangeEliminationCertificate M0 := by
  refine {
    eliminate := ?_
  }
  intro L M hL hCard hm
  have hSafe : WordPureSeparation M.word :=
    B.model_safe M hL hCard hm hCheck
  exact M.word_failure hSafe

end SingleCornerFiniteModelBridge
/-

/-- checked cutoff corresponding to `m <= 500`。 -/
def singleCornerCheckedCutoff500 : ℕ := 501

/-- executable check at the named cutoff。 -/
theorem singleCornerCheckedCutoff500_ok :
    singleCornerFiniteModelCheckBelow singleCornerCheckedCutoff500 = true := by
  simpa [singleCornerCheckedCutoff500] using singleCornerFiniteModelCheck500

/--
actual model bridgeが構成できれば `m<501` branch は即座に閉じる。
-/
theorem finiteRange500_of_modelBridge
    (B : SingleCornerFiniteModelBridge singleCornerCheckedCutoff500) :
    SingleCornerFiniteRangeEliminationCertificate
      singleCornerCheckedCutoff500 := by
  exact B.toFiniteRangeEliminationCertificate singleCornerCheckedCutoff500_ok

-/
end ExternalArithmetic
end CSTMicro
end Collatz2
