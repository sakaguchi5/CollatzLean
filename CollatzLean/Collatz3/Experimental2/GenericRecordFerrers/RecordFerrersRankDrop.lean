import CollatzLean.Collatz3.Experimental2.GenericRecordFerrers.RecordFerrers
import CollatzLean.Collatz3.Experimental2.GenericRecordFerrers.RecordRankEnvelope
import Mathlib.Tactic.Ring

/-!
# Collatz3 Experimental2: RecordFerrers の弦順位包絡線の successive drop

`RecordRankEnvelope` では canonical record cut が弦順位の過去最小包絡線の
strict corner そのものであることを固定した。

このファイルでは、完成 `RecordFerrers` の各 canonical block が持つ
local criticality を使い、隣接する包絡線 corner 間の弦順位落差を exact に計算する。

block の start を `a`、長さを `r`、全体幅を `m` とすると、中心式は

`chordRank(a) - chordRank(a+r)`
`  = m * criticalDepth β r - criticalDepth β m * r`

である。

右辺から start `a` が消えるため、屋根 `β` と全体幅 `m` を固定すれば
canonical block の横幅 `r` だけで、その block に対応する包絡線の縦落差が決まる。
最後にこの式を canonical block 列全体へ再帰的に持ち上げる。
-/

namespace Collatz3
namespace Experimental2
namespace GenericRecordFerrers

/--
一つの local critical block では、start と endpoint の弦順位の差は
block 長 `r` だけで決まる。

endpoint が terminal `m` の場合も admissible path の terminal 条件を使って
同じ式に統一する。
-/
theorem chordRank_sub_next_eq_of_localRoofCriticalBlock
    {β : ℕ → ℕ}
    {m : ℕ}
    {height : ℕ → ℕ}
    (A : IsAdmissibleRoofPath β m height)
    {a r : ℕ}
    (B : IsLocalRoofCriticalBlock β m height a r) :
    chordRank β m height a -
        chordRank β m height (a + r) =
      (m : ℤ) * (criticalDepth β r : ℤ) -
        (criticalDepth β m : ℤ) * (r : ℤ) := by
  have hrPos : 0 < r := B.1
  have harLe : a + r ≤ m := B.2.1
  have haLt : a < m := by
    omega
  have hStartDepth :
      cutDepth β m height a = height a :=
    cutDepth_of_lt haLt
  have hEndDepth :
      cutDepth β m height (a + r) = height (a + r) := by
    by_cases hEndLt : a + r < m
    · exact cutDepth_of_lt hEndLt
    · have hEndEq : a + r = m := by
        omega
      rw [hEndEq, cutDepth_terminal]
      have hTerminal : height m = criticalDepth β m := by
        simpa [HasCriticalTerminal] using A.2.2
      exact hTerminal.symm
  have hMono : height a ≤ height (a + r) :=
    A.height_le_add a r harLe
  have hLocalNat :
      height (a + r) - height a = criticalDepth β r := by
    simpa [localDepth] using B.2.2.1
  have hLocalInt :
      (height (a + r) : ℤ) - (height a : ℤ) =
        (criticalDepth β r : ℤ) := by
    rw [← Nat.cast_sub hMono]
    exact_mod_cast hLocalNat
  calc
    chordRank β m height a - chordRank β m height (a + r) =
        (m : ℤ) *
            ((height (a + r) : ℤ) - (height a : ℤ)) -
          (criticalDepth β m : ℤ) * (r : ℤ) := by
      unfold chordRank
      rw [hStartDepth, hEndDepth]
      push_cast
      ring
    _ =
        (m : ℤ) * (criticalDepth β r : ℤ) -
          (criticalDepth β m : ℤ) * (r : ℤ) := by
      rw [hLocalInt]

/--
block 列に沿って successive rank drop 公式がすべて成立すること。

空列では自明とし、`r :: rs` では現在 block の落差公式と
次の start `a+r` からの tail law を組にする。
-/
def RankEnvelopeDropLawFrom
    (β : ℕ → ℕ)
    (m : ℕ)
    (height : ℕ → ℕ) : ℕ → List ℕ → Prop
  | _a, [] => True
  | a, r :: rs =>
      chordRank β m height a -
          chordRank β m height (a + r) =
        (m : ℤ) * (criticalDepth β r : ℤ) -
          (criticalDepth β m : ℤ) * (r : ℤ) ∧
        RankEnvelopeDropLawFrom β m height (a + r) rs

/--
全 block が local critical なら、同じ block 列に沿って
弦順位包絡線の successive drop 公式がすべて成立する。
-/
theorem rankEnvelopeDropLawFrom_of_localRoofCriticalBlocksFrom
    {β : ℕ → ℕ}
    {m : ℕ}
    {height : ℕ → ℕ}
    (A : IsAdmissibleRoofPath β m height) :
    ∀ (a : ℕ) (rs : List ℕ),
      LocalRoofCriticalBlocksFrom β m height a rs →
        RankEnvelopeDropLawFrom β m height a rs
  | _a, [], _L => by
      trivial
  | a, r :: rs, L => by
      simp only [LocalRoofCriticalBlocksFrom] at L
      simp only [RankEnvelopeDropLawFrom]
      refine ⟨?_, ?_⟩
      · exact chordRank_sub_next_eq_of_localRoofCriticalBlock A L.1
      · exact
          rankEnvelopeDropLawFrom_of_localRoofCriticalBlocksFrom
            A (a + r) rs L.2

namespace RecordFerrers

/--
完成 RecordFerrers の canonical block 列全体では、各 block 長 `r` に対して

`rank drop = m * criticalDepth β r - criticalDepth β m * r`

が順番に成立する。

従って屋根 `β` と幅 `m` を固定すれば、`canonicalRecordLengths` から
記録包絡線の successive vertical drop をすべて読み取れる。
-/
theorem rankEnvelopeDropLaw
    {β : ℕ → ℕ}
    {m : ℕ}
    (R : RecordFerrers β m) :
    RankEnvelopeDropLawFrom
      β m R.height canonicalAnchor
        (canonicalRecordLengths β m R.height) := by
  exact
    rankEnvelopeDropLawFrom_of_localRoofCriticalBlocksFrom
      R.admissible
      canonicalAnchor
      (canonicalRecordLengths β m R.height)
      R.localCriticalBlocks

end RecordFerrers

end GenericRecordFerrers
end Experimental2
end Collatz3
