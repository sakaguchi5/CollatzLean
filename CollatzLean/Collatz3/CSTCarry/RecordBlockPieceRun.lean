import CollatzLean.Collatz3.CSTCarry.RecordBlockRowFactorization
import CollatzLean.Collatz3.CSTCarry.CarryBudgetChain
import CollatzLean.Collatz3.CSTCarry.CarryDeterministicSplit

/-!
# Collatz3 CSTCarry: Record block 列の exact piece run

canonical record rows を terminal block から initial block へ
`List (List FerrersRow)` として切り出し、その piece 列上で deterministic carry を走らせる。

これにより telescope に必要な

* piece rows,
* piece digits,
* block boundary carry

を lossless に得る。
-/

namespace Collatz3
open Ferrers
namespace CSTCarry

open Critical

/--
forward length 列を carry 順の row-piece 列へ変換する。

`rs = [r₀,...,rₙ]` に対し terminal 側 piece が先頭になる。
-/
def profileBlockPiecesFromLengths
    {m : ℕ}
    (h : Profile m) :
    (a : ℕ) → (rs : List ℕ) → a + rs.sum ≤ m →
      List (List FerrersRow)
  | _a, [], _hEnd => []
  | a, r :: rs, hEnd =>
      profileBlockPiecesFromLengths h (a + r) rs (by
        simpa [List.sum_cons, Nat.add_assoc] using hEnd) ++
      [profileBlockCarryRows h a r (by
        have hLe : a + r ≤ a + (r + rs.sum) := by omega
        exact le_trans hLe (by
          simpa [List.sum_cons, Nat.add_assoc] using hEnd))]

/-- piece 列を flatten すると既存 `profileRowsFromLengths` と exact に一致する。 -/
theorem flatten_profileBlockPiecesFromLengths
    {m : ℕ}
    (h : Profile m) :
    ∀ (a : ℕ) (rs : List ℕ) (hEnd : a + rs.sum ≤ m),
      (profileBlockPiecesFromLengths h a rs hEnd).flatten =
        profileRowsFromLengths h a rs hEnd
  | _a, [], _hEnd => rfl
  | a, r :: rs, hEnd => by
      simp only [profileBlockPiecesFromLengths, profileRowsFromLengths,
        List.flatten_append, List.flatten_singleton]
      rw [flatten_profileBlockPiecesFromLengths
        h (a + r) rs (by
          simpa [List.sum_cons, Nat.add_assoc] using hEnd)]

namespace Ferrers.RecordFerrers

/-- canonical Record blocks を carry 順の row-piece 列として読む。 -/
def canonicalRecordBlockPieces
    {m : ℕ}
    (R : RecordFerrers m) :
    List (List FerrersRow) :=
  profileBlockPiecesFromLengths
    R.profile.1
    initialRoofAnchor
    (canonicalRecordLengths R.profile.1)
    (by
      rw [R.initialRoofAnchor_add_sum_canonicalRecordLengths_eq_width])

/-- canonical block pieces の flatten は canonical record carry rows。 -/
theorem flatten_canonicalRecordBlockPieces
    {m : ℕ}
    (R : RecordFerrers m) :
    (canonicalRecordBlockPieces R).flatten =
      canonicalRecordCarryRows R := by
  have hEnd :
      initialRoofAnchor +
          (canonicalRecordLengths R.profile.1).sum ≤ m := by
    rw [R.initialRoofAnchor_add_sum_canonicalRecordLengths_eq_width]
  unfold canonicalRecordBlockPieces
  unfold canonicalRecordCarryRows
  exact flatten_profileBlockPiecesFromLengths
    R.profile.1
    initialRoofAnchor
    (canonicalRecordLengths R.profile.1)
    hEnd

end Ferrers.RecordFerrers

/--
row-piece 列を順に deterministic carry し、各 piece の digits を保存する。
-/
def canonicalBudgetPieces
    (H : ℕ) :
    List (List FerrersRow) → ℕ → List CarryBudgetPiece
  | [], _E => []
  | rows :: pieces, E =>
      let digits := canonicalCarryDigits H rows E
      let F := canonicalFinalCarry H rows E
      { rows := rows, digits := digits } ::
        canonicalBudgetPieces H pieces F

/-- canonical piece run の row flatten は元 piece 列の flatten。 -/
theorem rowsOfBudgetPieces_canonicalBudgetPieces
    (H : ℕ) :
    ∀ (pieces : List (List FerrersRow)) (E : ℕ),
      rowsOfBudgetPieces (canonicalBudgetPieces H pieces E) =
        pieces.flatten
  | [], E => rfl
  | rows :: pieces, E => by
      simp only [canonicalBudgetPieces, rowsOfBudgetPieces,
        List.flatten_cons]
      rw [rowsOfBudgetPieces_canonicalBudgetPieces
        H pieces (canonicalFinalCarry H rows E)]

/-- canonical piece run の digit flatten は whole canonical digit run。 -/
theorem digitsOfBudgetPieces_canonicalBudgetPieces
    (H : ℕ) :
    ∀ (pieces : List (List FerrersRow)) (E : ℕ),
      digitsOfBudgetPieces (canonicalBudgetPieces H pieces E) =
        canonicalCarryDigits H pieces.flatten E
  | [], E => by
      simp [canonicalBudgetPieces, digitsOfBudgetPieces]
  | rows :: pieces, E => by
      simp only [canonicalBudgetPieces, digitsOfBudgetPieces,
        List.flatten_cons]
      rw [digitsOfBudgetPieces_canonicalBudgetPieces
        H pieces (canonicalFinalCarry H rows E)]
      symm
      exact canonicalCarryDigits_append H rows pieces.flatten E

/-- canonical piece は必ず digit length compatible。 -/
theorem canonicalBudgetPieces_lengthCompatible
    (H : ℕ) :
    ∀ (pieces : List (List FerrersRow)) (E : ℕ)
      (B : CarryBudgetPiece),
      B ∈ canonicalBudgetPieces H pieces E →
        B.LengthCompatible
  | [], E, B, hMem => by
      simp [canonicalBudgetPieces] at hMem
  | rows :: pieces, E, B, hMem => by
      simp only [canonicalBudgetPieces, List.mem_cons] at hMem
      rcases hMem with rfl | hTail
      · unfold CarryBudgetPiece.LengthCompatible
        exact (canonicalCarryRun_realizes H rows E).digits_length_eq
      · exact canonicalBudgetPieces_lengthCompatible
          H pieces (canonicalFinalCarry H rows E) B hTail

/--
terminal strict piece + weak interior chain が揃えば、
canonical piece run 全体に strict complement budget が telescope する。

これは Record-specific geometry を仮定せず、piece run の純粋な終端 theorem。
-/
theorem canonicalPieces_complementBudget_of_head_strict_tail_weak
    {H E : ℕ}
    {terminalRows : List FerrersRow}
    {rest : List (List FerrersRow)}
    (hTerminal :
      ComplementBudget
        (2 ^ H)
        terminalRows
        (canonicalCarryDigits H terminalRows E))
    (hTail :
      WeakBudgetChain
        (2 ^ H)
        (canonicalBudgetPieces H rest
          (canonicalFinalCarry H terminalRows E))) :
    ComplementBudget
      (2 ^ H)
      (terminalRows ++ rest.flatten)
      (canonicalCarryDigits H
        (terminalRows ++ rest.flatten) E) := by
  have hLen :
      (canonicalCarryDigits H terminalRows E).length =
        terminalRows.length := by
    exact (canonicalCarryRun_realizes H terminalRows E).digits_length_eq
  have hTel :=
    complementBudget_telescope_chain
      hLen hTerminal hTail
  rw [rowsOfBudgetPieces_canonicalBudgetPieces] at hTel
  rw [digitsOfBudgetPieces_canonicalBudgetPieces] at hTel
  simpa [canonicalCarryDigits_append] using hTel


namespace Ferrers.RecordFerrers

/--
canonical Record block pieces が `terminalRows :: rest` と分解され、
先頭が strict budget、残りが weak budget chain なら、
record suffix 全体の strict complement budget が得られる。
-/
theorem canonicalRecordRows_complementBudget_of_blockPieces
    {m H E : ℕ}
    (R : RecordFerrers m)
    {terminalRows : List FerrersRow}
    {rest : List (List FerrersRow)}
    (hPieces :
      canonicalRecordBlockPieces R = terminalRows :: rest)
    (hTerminal :
      ComplementBudget
        (2 ^ H)
        terminalRows
        (canonicalCarryDigits H terminalRows E))
    (hTail :
      WeakBudgetChain
        (2 ^ H)
        (canonicalBudgetPieces H rest
          (canonicalFinalCarry H terminalRows E))) :
    ComplementBudget
      (2 ^ H)
      (canonicalRecordCarryRows R)
      (canonicalCarryDigits H (canonicalRecordCarryRows R) E) := by
  have hWhole :=
    canonicalPieces_complementBudget_of_head_strict_tail_weak
      hTerminal hTail
  have hFlat := flatten_canonicalRecordBlockPieces R
  rw [hPieces] at hFlat
  simp only [List.flatten_cons] at hFlat
  have hRows :
      canonicalRecordCarryRows R =
        terminalRows ++ rest.flatten := hFlat.symm
  simpa [hRows] using hWhole

end Ferrers.RecordFerrers

end CSTCarry
end Collatz3
