import CollatzLean.Collatz2.CSTMicro.CarryGeometry.MinimalActualABObstructionPacket
import CollatzLean.Collatz2.CSTMicro.CarryGeometry.FerrersCellResiduePotential

/-!
# Minimal bad predecessor geometry

`MinimalActualABObstructionPacket` では、同じ length の bad first-passage word のうち
Ferrers inversion が最小の word `B` を target に選び、actual A -> B provenance の
first-failure upper が exact に `B` 自身であることまで得た。

このファイルでは minimality を B の全 adjacent predecessor に使う。

任意の first-passage Ferrers predecessor

  lower -> B

は inversion が B より 1 小さいため safe である。したがってこの edge 自身が
`FirstFailureEdge` へ canonical に昇格し、全 predecessor について同時に

  HasCarry,
  0 < D < G,
  q_B < D,
  R_B < deltaR

を得る。

さらに binary Ferrers prefix order を使い、actual critical boundary と B の間に
留まる adjacent predecessor を一つ選ぶ。この predecessor の cell 座標

  i = position,
  a = oddCount(leftContext) + 1

を明示し、その residue が endpoint `(length B, oddCount B)` と `(i,a)` だけから
作る `ferrersCellResidueWeight` に一致することまで packet に保持する。
-/

namespace Collatz2
namespace CSTMicro

/-! ## 1. PrefixBelow と Ferrers chain の接続 -/

namespace PrefixBelow

/-- prefix dominance の推移律。 -/
theorem trans
    {u v w : ParityWord}
    (huv : PrefixBelow u v)
    (hvw : PrefixBelow v w) :
    PrefixBelow u w := by
  rcases huv with ⟨hlenUV, hoddUV, hpreUV⟩
  rcases hvw with ⟨hlenVW, hoddVW, hpreVW⟩
  refine ⟨hlenUV.trans hlenVW, hoddUV.trans hoddVW, ?_⟩
  intro j hj
  have hjV : j ≤ v.length := by
    rw [← hlenUV]
    exact hj
  exact le_trans (hpreUV j hj) (hpreVW j hjV)

end PrefixBelow

namespace AdjacentFerrersSwap

/-- 一つの `01 -> 10` Ferrers move は lower から upper への prefix dominance。 -/
theorem prefixBelow_lower_upper
    (S : AdjacentFerrersSwap) :
    PrefixBelow S.lowerWord S.upperWord := by
  refine ⟨?_, ?_, ?_⟩
  · rw [S.lowerWord_length, S.upperWord_length]
  · rw [S.lowerWord_oddCount, S.upperWord_oddCount]
  · intro j _hj
    have h :=
      prefixOddCount_swap_exact
        S.leftContext S.rightContext j
    change
      prefixOddCount
          (S.leftContext ++ ([false, true] ++ S.rightContext)) j ≤
        prefixOddCount
          (S.leftContext ++ ([true, false] ++ S.rightContext)) j
    rw [h]
    exact Nat.le_add_right _ _

/-- carry edge では upper representative は local increment より strict に小さい。 -/
theorem upperR_lt_deltaR_of_hasCarry
    (S : AdjacentFerrersSwap)
    (hCarry : S.HasCarry) :
    S.upperR < S.deltaR := by
  have hEq :=
    S.lowerR_add_deltaR_eq_modulus_add_upperR_of_hasCarry hCarry
  have hLower := S.lowerR_lt_modulus
  omega

end AdjacentFerrersSwap

namespace FerrersStep

/-- FerrersStep endpoint で書いた prefix dominance。 -/
theorem prefixBelow
    {lower upper : ParityWord}
    (S : FerrersStep lower upper) :
    PrefixBelow lower upper := by
  have h := S.edge.prefixBelow_lower_upper
  rw [← S.lower_eq, ← S.upper_eq] at h
  exact h

end FerrersStep

namespace FerrersChain

/-- Ferrers chain の start は prefix order で finish 以下。 -/
theorem prefixBelow
    {start finish : ParityWord}
    (C : FerrersChain start finish) :
    PrefixBelow start finish := by
  induction C with
  | refl =>
      exact PrefixBelow.refl _
  | step C S ih =>
      exact ih.trans S.prefixBelow

end FerrersChain

/-! ## 2. minimal B の任意 predecessor を FirstFailureEdge へ昇格 -/

namespace ExternalArithmetic
namespace MinimalActualABObstructionPacket

/--
minimal bad word `B` に入る任意の first-passage predecessor edge は、
lower safe / upper bad を持つ genuine `FirstFailureEdge`。
-/
def predecessorFirstFailureEdge
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    {lower : ParityWord}
    (S : FerrersStep lower M.word)
    (hLowerFP : IsFirstPassageWord lower) :
    FirstFailureEdge := {
  lower := lower
  upper := M.word
  step := S
  lower_firstPassage := hLowerFP
  upper_firstPassage := M.word_firstPassage
  lower_safe := M.minimal.predecessor_safe S hLowerFP
  upper_failure := M.word_failure
}

/-- minimal B に入る全 first-passage predecessor は carry。 -/
theorem predecessor_hasCarry
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    {lower : ParityWord}
    (S : FerrersStep lower M.word)
    (hLowerFP : IsFirstPassageWord lower) :
    S.edge.HasCarry := by
  have h :=
    (M.predecessorFirstFailureEdge S hLowerFP).hasCarry
  simpa [predecessorFirstFailureEdge] using h

/-- minimal B に入る全 first-passage predecessor cell の Farey residue は正。 -/
theorem predecessor_residue_pos
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    {lower : ParityWord}
    (S : FerrersStep lower M.word)
    (hLowerFP : IsFirstPassageWord lower) :
    0 < S.edge.toFareyCellPacket.residue := by
  let F := M.predecessorFirstFailureEdge S hLowerFP
  let D := F.toFirstFailureFareyData
  have h : 0 < D.farey.residue :=
    D.residue_pos
  change 0 < F.step.edge.toFareyCellPacket.residue at h
  change 0 < S.edge.toFareyCellPacket.residue at h
  exact h

/-- minimal B に入る全 first-passage predecessor cell で `D < G`。 -/
theorem predecessor_residue_lt_gap
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    {lower : ParityWord}
    (S : FerrersStep lower M.word)
    (hLowerFP : IsFirstPassageWord lower) :
    S.edge.toFareyCellPacket.residue <
      S.edge.toFareyCellPacket.G := by
  let F := M.predecessorFirstFailureEdge S hLowerFP
  let D := F.toFirstFailureFareyData
  have h :
      D.farey.residue < D.farey.G :=
    D.residue_lt_gap
  change
    F.step.edge.toFareyCellPacket.residue <
      F.step.edge.toFareyCellPacket.G at h
  change
    S.edge.toFareyCellPacket.residue <
      S.edge.toFareyCellPacket.G at h
  exact h

/--
minimal bad word 自身の normalized coordinate `q_B` は、
任意の first-passage predecessor cell の `D` より strict に小さい。
-/
theorem predecessor_normalizedQ_lt_residue
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    {lower : ParityWord}
    (S : FerrersStep lower M.word)
    (hLowerFP : IsFirstPassageWord lower) :
    normalizedSeparationDefectInt M.word <
      S.edge.toFareyCellPacket.residue := by
  let F := M.predecessorFirstFailureEdge S hLowerFP
  let D := F.toFirstFailureFareyData
  have h :
      normalizedSeparationDefectInt F.step.edge.upperWord <
        D.farey.residue :=
    D.upper_normalizedSeparationDefectInt_lt_residue
  change
    normalizedSeparationDefectInt F.step.edge.upperWord <
      F.step.edge.toFareyCellPacket.residue at h
  change
    normalizedSeparationDefectInt S.edge.upperWord <
      S.edge.toFareyCellPacket.residue at h
  have hUpper :
      normalizedSeparationDefectInt M.word =
        normalizedSeparationDefectInt S.edge.upperWord :=
    congrArg normalizedSeparationDefectInt S.upper_eq
  calc
    normalizedSeparationDefectInt M.word
        =
      normalizedSeparationDefectInt S.edge.upperWord := hUpper
    _ < S.edge.toFareyCellPacket.residue := h

/-- actual packet の natural `q` を minimal bad word 自身の normalized coordinate と同定。 -/
theorem actual_q_cast_eq_word_normalized
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L) :
    (M.actual.q : ℤ) =
      normalizedSeparationDefectInt M.word := by
  have h := M.actual.q_cast_eq_upper_normalized
  unfold ActualABObstructionPacket.firstFailureEdge at h
  unfold ActualBoundaryFirstFailureCocyclePacket.firstFailureEdge at h
  unfold FirstFailureProvenance.toFirstFailureEdge at h
  dsimp at h
  rw [M.failureStep_upperWord_eq_word] at h
  exact h

/-- natural `q_B` で書いた全-predecessor inequality `q_B < D`。 -/
theorem predecessor_actualQ_lt_residue
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    {lower : ParityWord}
    (S : FerrersStep lower M.word)
    (hLowerFP : IsFirstPassageWord lower) :
    (M.actual.q : ℤ) <
      S.edge.toFareyCellPacket.residue := by
  rw [M.actual_q_cast_eq_word_normalized]
  exact M.predecessor_normalizedQ_lt_residue S hLowerFP

/--
minimal B に入る全 first-passage predecessor carry で
`R_B < deltaR`。
-/
theorem predecessor_leastRepresentative_lt_deltaR
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    {lower : ParityWord}
    (S : FerrersStep lower M.word)
    (hLowerFP : IsFirstPassageWord lower) :
    leastRepresentative M.word < S.edge.deltaR := by
  have hCarry := M.predecessor_hasCarry S hLowerFP
  have h := S.edge.upperR_lt_deltaR_of_hasCarry hCarry
  unfold AdjacentFerrersSwap.upperR at h
  rw [← S.upper_eq] at h
  exact h

/--
minimal B の任意の first-passage predecessor に同時に課される中心 geometry。
-/
theorem predecessor_geometry_packet
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    {lower : ParityWord}
    (S : FerrersStep lower M.word)
    (hLowerFP : IsFirstPassageWord lower) :
    S.edge.HasCarry
      ∧
    0 < S.edge.toFareyCellPacket.residue
      ∧
    S.edge.toFareyCellPacket.residue <
        S.edge.toFareyCellPacket.G
      ∧
    (M.actual.q : ℤ) <
        S.edge.toFareyCellPacket.residue
      ∧
    leastRepresentative M.word < S.edge.deltaR := by
  exact
    ⟨M.predecessor_hasCarry S hLowerFP,
      M.predecessor_residue_pos S hLowerFP,
      M.predecessor_residue_lt_gap S hLowerFP,
      M.predecessor_actualQ_lt_residue S hLowerFP,
      M.predecessor_leastRepresentative_lt_deltaR S hLowerFP⟩

/-! ## 3. critical boundary を下回らない predecessor を選ぶ -/

/-- actual critical boundary から minimal B までの underlying Ferrers chain。 -/
def boundaryToWordChain
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L) :
    FerrersChain
      M.actual.cocycle.provenance.boundary
      M.word := by
  have C :
      FerrersChain
        M.actual.cocycle.provenance.boundary
        M.actual.cocycle.provenance.upper :=
    FerrersChain.step
      M.actual.cocycle.provenance.safePrefixChain.toFerrersChain
      M.actual.cocycle.provenance.failureStep
  rw [M.provenance_upper_eq_word] at C
  exact C

/-- actual critical boundary は prefix order で minimal B 以下。 -/
theorem boundary_prefixBelow_word
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L) :
    PrefixBelow
      M.actual.cocycle.provenance.boundary
      M.word := by
  exact M.boundaryToWordChain.prefixBelow

/-- boundary は safe、minimal B は bad なので両者は異なる。 -/
theorem boundary_ne_word
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L) :
    M.actual.cocycle.provenance.boundary ≠ M.word := by
  intro hEq
  have hSafe :
      WordPureSeparation
        M.actual.cocycle.provenance.boundary :=
    M.actual.cocycle.provenance.safePrefixChain.start_safe
  apply M.word_failure
  rw [← hEq]
  exact hSafe

/--
critical boundary と minimal B の間に留まる adjacent predecessor が存在する。
-/
theorem exists_boundaryRespectingPredecessorData
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L) :
    Nonempty
      (FerrersPredecessorData
        M.actual.cocycle.provenance.boundary
        M.word) := by
  exact
    exists_ferrersPredecessor_of_prefixBelow_ne
      M.boundary_prefixBelow_word
      M.boundary_ne_word

/--
boundary-respecting predecessor と、その exposed Ferrers cell `(i,a)` の全 geometry。
-/
structure BoundaryRespectingPredecessorCell
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L) where
  pred : ParityWord
  step : FerrersStep pred M.word
  below_boundary :
    PrefixBelow M.actual.cocycle.provenance.boundary pred
  pred_firstPassage : IsFirstPassageWord pred
  pred_safe : WordPureSeparation pred

  i : ℕ
  a : ℕ
  i_eq_position : i = step.edge.position
  i_eq_leftLength : i = step.edge.leftContext.length
  a_eq_leftExponent : a = step.edge.fareyLeftExponent
  a_eq_leftOdd_succ : a = oddCount step.edge.leftContext + 1

  hasCarry : step.edge.HasCarry
  residue_pos : 0 < step.edge.toFareyCellPacket.residue
  residue_lt_gap :
    step.edge.toFareyCellPacket.residue <
      step.edge.toFareyCellPacket.G
  q_lt_residue :
    (M.actual.q : ℤ) <
      step.edge.toFareyCellPacket.residue
  R_lt_deltaR :
    leastRepresentative M.word < step.edge.deltaR

  residue_eq_cellWeight :
    step.edge.toFareyCellPacket.residue =
      ferrersCellResidueWeight
        M.word.length (oddCount M.word) i a

namespace BoundaryRespectingPredecessorCell

/-- selected predecessor edge 自身を genuine first-failure edge として読む。 -/
def firstFailureEdge
    {L : ℕ}
    {M : MinimalActualABObstructionPacket L}
    (C : BoundaryRespectingPredecessorCell M) :
    FirstFailureEdge :=
  M.predecessorFirstFailureEdge C.step C.pred_firstPassage

/-- selected cell の座標を `(position, odd(left)+1)` で直接読む。 -/
theorem coordinate_eq
    {L : ℕ}
    {M : MinimalActualABObstructionPacket L}
    (C : BoundaryRespectingPredecessorCell M) :
    C.i = C.step.edge.position
      ∧
    C.a = oddCount C.step.edge.leftContext + 1 :=
  ⟨C.i_eq_position, C.a_eq_leftOdd_succ⟩

end BoundaryRespectingPredecessorCell

/--
minimal actual B には、critical boundary を下回らない predecessor と
explicit cell `(i,a)` が存在し、その cell は全-predecessor first-failure geometry を満たす。
-/
theorem exists_boundaryRespectingPredecessorCell
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L) :
    Nonempty (BoundaryRespectingPredecessorCell M) := by
  rcases M.exists_boundaryRespectingPredecessorData with ⟨D⟩
  have hPredFP : IsFirstPassageWord D.pred :=
    IsFirstPassageWord.of_prefixBelow
      M.actual.cocycle.provenance.boundary_isBoundary.1
      D.below
  have hPredSafe : WordPureSeparation D.pred :=
    M.minimal.predecessor_safe D.step hPredFP
  let i := D.step.edge.position
  let a := D.step.edge.fareyLeftExponent
  have hCell :=
    D.step.edge.fareyResidue_eq_ferrersCellResidueWeight
  have hLen :
      D.step.edge.length = M.word.length := by
    calc
      D.step.edge.length = D.step.edge.upperWord.length :=
        D.step.edge.upperWord_length.symm
      _ = M.word.length :=
        (congrArg List.length D.step.upper_eq).symm
  have hOdd :
      D.step.edge.oddTotal = oddCount M.word := by
    calc
      D.step.edge.oddTotal = oddCount D.step.edge.upperWord :=
        D.step.edge.upperWord_oddCount.symm
      _ = oddCount M.word :=
        (congrArg oddCount D.step.upper_eq).symm
  rw [hLen, hOdd] at hCell
  refine ⟨{
    pred := D.pred
    step := D.step
    below_boundary := D.below
    pred_firstPassage := hPredFP
    pred_safe := hPredSafe
    i := i
    a := a
    i_eq_position := by rfl
    i_eq_leftLength := by
      rfl
    a_eq_leftExponent := by rfl
    a_eq_leftOdd_succ := by
      rfl
    hasCarry := M.predecessor_hasCarry D.step hPredFP
    residue_pos := M.predecessor_residue_pos D.step hPredFP
    residue_lt_gap := M.predecessor_residue_lt_gap D.step hPredFP
    q_lt_residue := M.predecessor_actualQ_lt_residue D.step hPredFP
    R_lt_deltaR := M.predecessor_leastRepresentative_lt_deltaR D.step hPredFP
    residue_eq_cellWeight := ?_
  }⟩
  simpa [i, a] using hCell

/--
最終 summary：minimal bad B が存在するなら、critical boundary 以上の exposed predecessor cell
`(i,a)` が存在し、その cell で

  HasCarry,
  0 < D < G,
  q_B < D,
  R_B < deltaR

が同時に成立する。
-/
theorem exists_boundaryRespectingPredecessorCell_geometry
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L) :
    ∃ C : BoundaryRespectingPredecessorCell M,
      C.step.edge.HasCarry
        ∧
      0 < C.step.edge.toFareyCellPacket.residue
        ∧
      C.step.edge.toFareyCellPacket.residue <
          C.step.edge.toFareyCellPacket.G
        ∧
      (M.actual.q : ℤ) <
          C.step.edge.toFareyCellPacket.residue
        ∧
      leastRepresentative M.word < C.step.edge.deltaR
        ∧
      C.step.edge.toFareyCellPacket.residue =
        ferrersCellResidueWeight
          M.word.length (oddCount M.word) C.i C.a := by
  rcases M.exists_boundaryRespectingPredecessorCell with ⟨C⟩
  exact
    ⟨C,
      C.hasCarry,
      C.residue_pos,
      C.residue_lt_gap,
      C.q_lt_residue,
      C.R_lt_deltaR,
      C.residue_eq_cellWeight⟩

end MinimalActualABObstructionPacket
end ExternalArithmetic

end CSTMicro
end Collatz2
