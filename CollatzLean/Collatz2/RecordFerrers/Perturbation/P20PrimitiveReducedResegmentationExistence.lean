import CollatzLean.Collatz2.RecordFerrers.Perturbation.P19AdmissibleRecordContact
import CollatzLean.Collatz2.RecordFerrers.Record.Canonicality

/-!
# Record–Ferrers 摂動理論 20: primitive/reduced target の canonical 再分割存在

P19 では、primitive + StripReduced FirstCrossing fiber の正の roof anchor から
必ず次の genuine `RecordBlock` が存在することを示した。

本ファイルでは、その一歩存在定理を terminal まで反復する。
残り odd length `p-anchor` に関する強帰納法を使い、

  positive roof anchor
      -> next RecordBlock
      -> interior なら次の roof anchor へ進む
      -> terminal なら終了

という `RecordChain` の `cons / last` 構造そのものを再構成する。

これにより primitive + StripReduced FirstCrossing target は、
外部から block list や carry-compatible factorization を与えなくても、
任意の正の roof anchor から genuine `RecordDecomposition` を持つ。

P19 の `RecordBlock.length_unique` と既存 canonicality により、
構成された length skeleton は自動的に一意である。
-/

namespace Collatz2
namespace RecordFerrers

open Word

/--
primitive + StripReduced FirstCrossing fiber では、任意の正の proper roof anchor から
terminal までを覆う genuine `RecordChain` が存在する。
-/
theorem exists_recordChain_from_positive_roof_of_primitiveReduced
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (v : FiberPoint P.oddCount P.twoDepth)
    (hF : FirstCrossing v.word)
    {anchor : ℕ}
    (hAnchorPos : 0 < anchor)
    (hAnchorLt : anchor < P.oddCount)
    (hAnchorRoof : RoofContact v anchor) :
    ∃ lengths : List ℕ,
      Nonempty (RecordChain v anchor lengths) := by
  classical
  have hQ :
      ∀ n : ℕ,
        ∀ a : ℕ,
          0 < a →
          a < P.oddCount →
          RoofContact v a →
          P.oddCount - a = n →
          ∃ lengths : List ℕ,
            Nonempty (RecordChain v a lengths) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro a haPos haLt haRoof hRemain
        obtain ⟨len, B⟩ :=
          exists_nextRecordBlock_of_primitiveReduced
            P hPrimitive hReduced v hF
            haPos haLt haRoof
        by_cases hTerminal : a + len = P.oddCount
        · exact
            ⟨[len],
              ⟨RecordChain.last B hTerminal⟩⟩
        · have hInterior : a + len < P.oddCount := by
            have hEnd := B.end_le_terminal
            omega
          have hNextPos : 0 < a + len := by
            omega
          have hNextRoof : RoofContact v (a + len) := by
            unfold RoofContact
            exact B.next_roof_if_interior hInterior
          have hRemainLt :
              P.oddCount - (a + len) < n := by
            have hLenPos := B.length_pos
            rw [← hRemain]
            omega
          obtain ⟨rest, ⟨T⟩⟩ :=
            ih
              (P.oddCount - (a + len))
              hRemainLt
              (a + len)
              hNextPos
              hInterior
              hNextRoof
              rfl
          exact
            ⟨len :: rest,
              ⟨RecordChain.cons B hInterior T⟩⟩
  exact
    hQ (P.oddCount - anchor)
      anchor hAnchorPos hAnchorLt hAnchorRoof rfl

/--
上の chain に whole FirstCrossing 証明を付け、genuine `RecordDecomposition` を得る。
-/
theorem exists_recordDecomposition_from_positive_roof_of_primitiveReduced
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (v : FiberPoint P.oddCount P.twoDepth)
    (hF : FirstCrossing v.word)
    {anchor : ℕ}
    (hAnchorPos : 0 < anchor)
    (hAnchorLt : anchor < P.oddCount)
    (hAnchorRoof : RoofContact v anchor) :
    Nonempty (RecordDecomposition v anchor) := by
  obtain ⟨lengths, ⟨C⟩⟩ :=
    exists_recordChain_from_positive_roof_of_primitiveReduced
      P hPrimitive hReduced v hF
      hAnchorPos hAnchorLt hAnchorRoof
  exact
    ⟨{
      lengths := lengths
      chain := C
      whole_firstCrossing := hF
    }⟩

/--
P20 で得た decomposition の length skeleton は、同じ target / anchor に対して一意。
存在定理と既存 canonicality を一つの公開定理にまとめる。
-/
theorem exists_unique_recordLengthSkeleton_from_positive_roof_of_primitiveReduced
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (v : FiberPoint P.oddCount P.twoDepth)
    (hF : FirstCrossing v.word)
    {anchor : ℕ}
    (hAnchorPos : 0 < anchor)
    (hAnchorLt : anchor < P.oddCount)
    (hAnchorRoof : RoofContact v anchor) :
    ∃ lengths : List ℕ,
      (∃ D : RecordDecomposition v anchor, D.lengths = lengths) ∧
      (∀ E : RecordDecomposition v anchor, E.lengths = lengths) := by
  obtain ⟨D⟩ :=
    exists_recordDecomposition_from_positive_roof_of_primitiveReduced
      P hPrimitive hReduced v hF
      hAnchorPos hAnchorLt hAnchorRoof
  refine ⟨D.lengths, ?_, ?_⟩
  · exact ⟨D, rfl⟩
  · intro E
    exact E.lengths_unique D

/--
whole denominator が 1 より大きい場合、cut 1 は自動的に critical roof 上にある。
validity により最初の exponent は少なくとも 1、FirstCrossing により高々
`criticalHeight 1 = 1` なので equality になる。
-/
theorem roofContact_one_of_firstCrossing
    {p H : ℕ}
    (v : FiberPoint p H)
    (hF : FirstCrossing v.word)
    (hp : 1 < p) :
    RoofContact v 1 := by
  have hLower : 1 ≤ v.height 1 :=
    v.index_le_height (by omega)
  have hWordLt : 1 < oddSteps v.word := by
    rw [v.oddSteps_eq]
    exact hp
  have hUpperRaw :=
    hF.prefixTwoDepth_le_criticalHeight
      (by omega : 0 < 1) hWordLt
  have hUpper : v.height 1 ≤ criticalHeight 1 := by
    simpa [FiberPoint.height] using hUpperRaw
  have hCriticalOne : criticalHeight 1 = 1 := by
    norm_num [criticalHeight]
    decide
  unfold RoofContact
  rw [hCriticalOne]
  omega

/--
特に `p>1` なら initial positive cut 1 から canonical record decomposition が存在する。
これは外部 block list を要求しない pure target-side existence theorem である。
-/
theorem exists_recordDecomposition_one_of_primitiveReduced
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (v : FiberPoint P.oddCount P.twoDepth)
    (hF : FirstCrossing v.word)
    (hp : 1 < P.oddCount) :
    Nonempty (RecordDecomposition v 1) := by
  have hRoof : RoofContact v 1 :=
    roofContact_one_of_firstCrossing v hF hp
  exact
    exists_recordDecomposition_from_positive_roof_of_primitiveReduced
      P hPrimitive hReduced v hF
      (by omega) hp hRoof

/--
`p>1` の primitive + StripReduced pair は terminal depth も自動的に minimal になる。
P20 の decomposition existence と既存 canonicality の直接の帰結。
-/
theorem twoDepth_eq_criticalHeight_add_one_of_primitiveReduced
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (v : FiberPoint P.oddCount P.twoDepth)
    (hF : FirstCrossing v.word)
    (hp : 1 < P.oddCount) :
    P.twoDepth = criticalHeight P.oddCount + 1 := by
  obtain ⟨D⟩ :=
    exists_recordDecomposition_one_of_primitiveReduced
      P hPrimitive hReduced v hF hp
  simpa using D.twoDepth_eq_criticalHeight_add_one

end RecordFerrers
end Collatz2
