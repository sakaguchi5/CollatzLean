import CollatzLean.Collatz3.Ferrers.RecordCanonical
import CollatzLean.Collatz3.Critical.RecordCarryExact
import Mathlib.Tactic.Linarith

/-!
# Collatz3: canonical exact carry law

deterministic partition と weak/strict record geometry は下位層へ分離した。

* `RecordPartition`: `initialRecordCuts` から `canonicalRecordLengths` を有限計算する。
* `RecordCanonical`: canonical cuts が切り出す weak geometry と、
  `NoRecordLevelTie` による constructive strict skeleton を扱う。
* このファイル: exact carry compatibility が weak geometry を strict geometry へ
  昇格させる別の十分条件を扱う。

真の `RecordFerrers` 自体はまだ定義しない。
`IsPrimitiveWidth` / `IsBestUpperWidth` もここでは使わない。
-/

namespace Collatz3
namespace Ferrers

open Critical

/--
canonical strict-cut partition に沿った exact carry compatibility。

最後だけ terminal carry `0` を要求し、それ以前の各区間では
premature carry-1 roof return だけを禁止する。
-/
def CanonicalCarryCompatibleFrom
    {m : ℕ}
    (h : Profile m) : ℕ → List ℕ → Prop
  | a, [] =>
      NoPrematureCarryOneRoofReturn h a (m - a) ∧
        beattyCarry a (m - a) = 0
  | a, k :: ks =>
      NoPrematureCarryOneRoofReturn h a (k - a) ∧
        CanonicalCarryCompatibleFrom h k ks

/--
local proper-prefix Beatty bound は chord rank の strict interior inequality を与える。
これが carry compatibility から record-level tie を消す算術 bridge。
-/
theorem profileChordRank_lt_add_of_localDepth_le_beatty
    {m : ℕ}
    {h : Profile m}
    (A : Admissible h)
    {a j : ℕ}
    (hStartRoof : IsRoofCut h a)
    (hjPos : 0 < j)
    (hEndLt : a + j < m)
    (hDepth : localDepth h a j ≤ beattyIndex j) :
    profileChordRank h a < profileChordRank h (a + j) := by
  have hm : 0 < m := lt_trans hStartRoof.pos hStartRoof.lt_width
  have hChord :=
    beattyIndex_below_criticalChord
      (m := m) (r := j) hm hjPos
  have hScaled :
      m * localDepth h a j < criticalTwoDepth m * j :=
    lt_of_le_of_lt
      (Nat.mul_le_mul_left m hDepth)
      hChord
  have hScaledZ :
      (m : ℤ) * (localDepth h a j : ℤ) <
        (criticalTwoDepth m : ℤ) * (j : ℤ) := by
    exact_mod_cast hScaled
  have hDiff :=
    profileChordRank_add_sub A (Nat.le_of_lt hEndLt)
  have hPos :
      0 < profileChordRank h (a + j) - profileChordRank h a := by
    rw [hDiff]
    linarith
  exact sub_pos.mp hPos

/--
一つの weak record block は、premature carry-1 roof return が無ければ strict record block。
-/
theorem isRecordBlock_of_weak_of_noPrematureCarryOneRoofReturn
    {m : ℕ}
    {h : Profile m}
    (A : Admissible h)
    {a r : ℕ}
    (hStartRoof : IsRoofCut h a)
    (hEnd : a + r ≤ m)
    (W : IsWeakRecordBlock h a r)
    (C : NoPrematureCarryOneRoofReturn h a r) :
    Combinatorics.IsRecordBlock (profileChordRank h) a r := by
  have hPrefix :=
    (localProperPrefixBound_iff_noPrematureCarryOneRoofReturn
      A hStartRoof hEnd).2 C
  refine ⟨W.length_pos, ?_, W.end_drop⟩
  intro j hjPos hjLt
  have hEndLt : a + j < m := by omega
  exact profileChordRank_lt_add_of_localDepth_le_beatty
    A hStartRoof hjPos hEndLt (hPrefix j hjPos hjLt)

/--
canonical weak blocks は exact carry compatibility により strict canonical blocks へ昇格する。
-/
theorem canonicalStrictBlocksFrom_of_weak_of_carry
    {m : ℕ}
    {h : Profile m}
    (A : Admissible h) :
    ∀ (a : ℕ) (cuts : List ℕ),
      IsRoofCut h a →
      StrictCutChainFrom m a cuts →
      CanonicalWeakBlocksFrom h a cuts →
      CanonicalCarryCompatibleFrom h a cuts →
      CanonicalStrictBlocksFrom h a cuts
  | a, [], hRoof, hChain, hWeak, hCarry => by
      simp only [StrictCutChainFrom] at hChain
      simp only [CanonicalWeakBlocksFrom] at hWeak
      simp only [CanonicalCarryCompatibleFrom] at hCarry
      simp only [CanonicalStrictBlocksFrom]
      have hEnd : a + (m - a) ≤ m := by omega
      exact isRecordBlock_of_weak_of_noPrematureCarryOneRoofReturn
        A hRoof hEnd hWeak hCarry.1
  | a, k :: ks, hRoof, hChain, hWeak, hCarry => by
      simp only [StrictCutChainFrom] at hChain
      simp only [CanonicalWeakBlocksFrom] at hWeak
      simp only [CanonicalCarryCompatibleFrom] at hCarry
      simp only [CanonicalStrictBlocksFrom]
      have hEnd : a + (k - a) ≤ m := by omega
      have hStrict :
          Combinatorics.IsRecordBlock
            (profileChordRank h) a (k - a) :=
        isRecordBlock_of_weak_of_noPrematureCarryOneRoofReturn
          A hRoof hEnd hWeak.1 hCarry.1
      refine ⟨hStrict, hWeak.2.1, ?_⟩
      exact canonicalStrictBlocksFrom_of_weak_of_carry
        A k ks hWeak.2.1 hChain.2.2 hWeak.2.2 hCarry.2

/--
canonical exact carry law だけで、deterministic record partition の全区間が
strict record excursions になる。

`NoRecordLevelTie` を独立仮定にしない carry 側の中心結論。
-/
theorem canonicalStrictBlocksFrom_of_carry
    {m : ℕ}
    {h : Profile m}
    (A : Admissible h)
    (hm : 1 < m)
    (C : CanonicalCarryCompatibleFrom
      h initialRoofAnchor (initialRecordCuts h)) :
    CanonicalStrictBlocksFrom
      h initialRoofAnchor (initialRecordCuts h) := by
  exact canonicalStrictBlocksFrom_of_weak_of_carry
    A initialRoofAnchor (initialRecordCuts h)
    (initialRoofAnchor_isRoofCut A hm)
    (initialRecordCuts_strictCutChain (h := h) hm)
    (canonicalWeakBlocksFrom_initialRecordCuts A hm)
    C

end Ferrers
end Collatz3
