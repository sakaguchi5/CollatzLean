import CollatzLean.Collatz3.Critical.RecordTerminal

/-!
# Collatz3: record local geometry の exact carry 条件

このファイルでは、真の `RecordFerrers` を再導入する前に、
local critical geometry に本当に必要な carry 条件を exact に切り出す。

中心結果は次の三つ。

1. local proper-prefix failure は、途中の global roof return と Beatty carry `1`
   が同時に起きる場合に限る。
2. terminal block の minimal depth は terminal Beatty carry `0` と同値。
3. roof-compatible strict record chain 上では、exact carry compatibility と
   `LocalCriticalBlocksFrom` が同値。

`IsPrimitiveWidth` と `IsBestUpperWidth` はここでは仮定しない。
前者は canonical skeleton の存在を、後者は exact carry compatibility を
一括して保証する十分条件として別 theorem から使う。
-/

namespace Collatz3
namespace Critical

/--
一つの local block の途中で禁止すべき exact event。

proper local position `j` で global critical roof に戻り、同時に
Beatty addition carry が `1` になることだけを禁止する。
roof return 自体や carry `1` 自体を単独では禁止しない。
-/
def NoPrematureCarryOneRoofReturn
    {m : ℕ}
    (h : Profile m)
    (a r : ℕ) : Prop :=
  ∀ j : ℕ,
    0 < j →
    j < r →
    ¬ (IsRoofCut h (a + j) ∧ beattyCarry a j = 1)

/--
local prefix が Beatty roof を破ることと、
`premature roof return + carry 1` は exact に同値。

start が roof 上にあり `a+j` が proper cut なら、admissibility により
local depth は `beattyIndex j` より高々一つだけ上に出られる。
その一つ上へ出る場合は global endpoint が roof に exact に乗り、carry が `1` になる。
-/
theorem localPrefixFailure_iff_prematureCarryOneRoofReturn
    {m : ℕ}
    {h : Profile m}
    (A : Admissible h)
    {a j : ℕ}
    (hStartRoof : IsRoofCut h a)
    (hjPos : 0 < j)
    (hEndLt : a + j < m) :
    beattyIndex j < localDepth h a j ↔
      IsRoofCut h (a + j) ∧ beattyCarry a j = 1 := by
  have hDepthAdd :=
    profileHeight_add_localDepth A (Nat.le_of_lt hEndLt)
  have hStart := hStartRoof.height_eq
  have hEndLe :
      profileHeight h (a + j) ≤ beattyIndex (a + j) := by
    rw [profileHeight_of_lt h hEndLt]
    unfold checkpoint
    exact Nat.sub_le _ _
  have hCarry := beattyIndex_add_eq a j
  have hCarryLe := beattyCarry_le_one a j
  constructor
  · intro hFail
    have hOne : beattyCarry a j = 1 := by
      rw [hStart] at hDepthAdd
      omega
    have hEndEq :
        profileHeight h (a + j) = beattyIndex (a + j) := by
      rw [hStart] at hDepthAdd
      rw [hOne] at hCarry
      omega
    refine ⟨?_, hOne⟩
    refine ⟨?_, hEndLt, hEndEq⟩
    omega
  · rintro ⟨hEndRoof, hOne⟩
    have hEndEq := hEndRoof.height_eq
    rw [hStart] at hDepthAdd
    rw [hOne] at hCarry
    omega

/--
一 block の proper-prefix Beatty bound は、premature carry-1 roof return が
存在しないことと exact に同値。
-/
theorem localProperPrefixBound_iff_noPrematureCarryOneRoofReturn
    {m : ℕ}
    {h : Profile m}
    (A : Admissible h)
    {a r : ℕ}
    (hStartRoof : IsRoofCut h a)
    (hEnd : a + r ≤ m) :
    (∀ j : ℕ,
      0 < j →
      j < r →
      localDepth h a j ≤ beattyIndex j) ↔
      NoPrematureCarryOneRoofReturn h a r := by
  constructor
  · intro hBound j hjPos hjLt hBad
    have hEndLt : a + j < m := by omega
    have hFail :=
      (localPrefixFailure_iff_prematureCarryOneRoofReturn
        A hStartRoof hjPos hEndLt).2 hBad
    exact (Nat.not_lt_of_ge (hBound j hjPos hjLt)) hFail
  · intro hNo j hjPos hjLt
    by_contra hNot
    have hFail : beattyIndex j < localDepth h a j := by omega
    have hEndLt : a + j < m := by omega
    have hBad :=
      (localPrefixFailure_iff_prematureCarryOneRoofReturn
        A hStartRoof hjPos hEndLt).1 hFail
    exact hNo j hjPos hjLt hBad

/--
terminal singleton block の minimal depth は terminal Beatty carry `0` と exact に同値。

`a+r=m` なので terminal height は `criticalTwoDepth m`。
start roof を引くと local terminal depth は
`criticalTwoDepth r + beattyCarry a r` になり、minimality は carry `0` と同値になる。
-/
theorem terminalMinimal_iff_beattyCarry_eq_zero
    {m : ℕ}
    {h : Profile m}
    (A : Admissible h)
    {a r : ℕ}
    (hStartRoof : IsRoofCut h a)
    (hTerminal : a + r = m) :
    localDepth h a r = criticalTwoDepth r ↔
      beattyCarry a r = 0 := by
  have hDepthAdd :=
    profileHeight_add_localDepth A (Nat.le_of_eq hTerminal)
  have hStart := hStartRoof.height_eq
  have hTerminalHeight :
      profileHeight h (a + r) = criticalTwoDepth m := by
    rw [hTerminal]
    exact profileHeight_terminal h
  have hLocal :
      beattyIndex a + localDepth h a r = criticalTwoDepth m := by
    simpa [hStart, hTerminalHeight] using hDepthAdd
  have hCarry := beattyIndex_add_eq a r
  rw [hTerminal] at hCarry
  unfold criticalTwoDepth at hLocal ⊢
  constructor
  · intro hMinimal
    omega
  · intro hZero
    omega

/--
block chain の最後の block だけが terminal carry `0` を持つという predicate。
interior block の endpoint carry は strict roof-to-roof record drop から導かれるため、
ここには保存しない。
-/
def TerminalCarryZeroFrom
    {m : ℕ}
    (h : Profile m) : ℕ → List ℕ → Prop
  | _a, [] => False
  | a, [r] => beattyCarry a r = 0
  | a, r :: s :: rs => TerminalCarryZeroFrom h (a + r) (s :: rs)

/--
roof-compatible record chain 上では、既存の `TerminalMinimalFrom` と
terminal carry `0` は exact に同値。
-/
theorem terminalMinimalFrom_iff_terminalCarryZeroFrom
    {m : ℕ}
    {h : Profile m}
    (A : Admissible h) :
    ∀ (a : ℕ) (rs : List ℕ),
      IsRoofCut h a →
      RoofRecordSkeleton.RealizesBlocksFrom h a rs →
      (TerminalMinimalFrom h a rs ↔ TerminalCarryZeroFrom h a rs)
  | _a, [], _hRoof, hFalse => False.elim hFalse
  | a, [r], hRoof, hOne => by
      simp only [TerminalMinimalFrom, TerminalCarryZeroFrom]
      exact terminalMinimal_iff_beattyCarry_eq_zero A hRoof hOne.2
  | a, r :: s :: rs, _hRoof, hMany => by
      simp only [TerminalMinimalFrom, TerminalCarryZeroFrom]
      exact terminalMinimalFrom_iff_terminalCarryZeroFrom
        A (a + r) (s :: rs) hMany.2.1 hMany.2.2

/--
真の Record--Ferrers に残す候補となる exact local carry compatibility。

* 各 block の proper interior では premature carry-1 roof return を禁止する。
* 最後の block だけ terminal carry `0` を要求する。
* interior record endpoint の carry `1` は derived theorem なので保存しない。
-/
def RecordCarryCompatibleFrom
    {m : ℕ}
    (h : Profile m) : ℕ → List ℕ → Prop
  | _a, [] => False
  | a, [r] =>
      NoPrematureCarryOneRoofReturn h a r ∧
        beattyCarry a r = 0
  | a, r :: s :: rs =>
      NoPrematureCarryOneRoofReturn h a r ∧
        RecordCarryCompatibleFrom h (a + r) (s :: rs)

/--
roof-compatible strict record chain 上では、exact carry compatibility と
全 block の local critical geometry は同値。

従って `RecordCarryCompatibleFrom` は BestUpper のような十分条件ではなく、
`LocalCriticalBlocksFrom` 自体を carry/roof の語彙だけで exact に特徴付ける。
-/
theorem recordCarryCompatibleFrom_iff_localCriticalBlocksFrom
    {m : ℕ}
    {h : Profile m}
    (A : Admissible h) :
    ∀ (a : ℕ) (rs : List ℕ),
      IsRoofCut h a →
      RoofRecordSkeleton.RealizesBlocksFrom h a rs →
      (RecordCarryCompatibleFrom h a rs ↔
        LocalCriticalBlocksFrom h a rs)
  | _a, [], _hRoof, hFalse => False.elim hFalse
  | a, [r], hRoof, hOne => by
      have hEnd : a + r ≤ m := Nat.le_of_eq hOne.2
      have hPrefixIff :=
        localProperPrefixBound_iff_noPrematureCarryOneRoofReturn
          A hRoof hEnd
      have hTerminalIff :=
        terminalMinimal_iff_beattyCarry_eq_zero
          A hRoof hOne.2
      constructor
      · intro C
        simp only [RecordCarryCompatibleFrom] at C
        refine ⟨?_, by trivial⟩
        refine ⟨hOne.1.length_pos, hEnd, ?_, ?_⟩
        · exact hTerminalIff.2 C.2
        · exact hPrefixIff.2 C.1
      · intro L
        have B := L.1
        simp only [RecordCarryCompatibleFrom]
        refine ⟨?_, ?_⟩
        · exact hPrefixIff.1 B.2.2.2
        · exact hTerminalIff.1 B.2.2.1
  | a, r :: s :: rs, hRoof, hMany => by
      have hEndRoof : IsRoofCut h (a + r) := hMany.2.1
      have hEnd : a + r ≤ m := Nat.le_of_lt hEndRoof.lt_width
      have hPrefixIff :=
        localProperPrefixBound_iff_noPrematureCarryOneRoofReturn
          A hRoof hEnd
      have hMinimal :
          localDepth h a r = criticalTwoDepth r :=
        interior_localDepth_eq_criticalTwoDepth
          A hMany.1 hRoof hEndRoof
      have hTailIff :=
        recordCarryCompatibleFrom_iff_localCriticalBlocksFrom
          A (a + r) (s :: rs) hEndRoof hMany.2.2
      constructor
      · intro C
        simp only [RecordCarryCompatibleFrom] at C
        refine ⟨?_, hTailIff.1 C.2⟩
        refine ⟨hMany.1.length_pos, hEnd, hMinimal, ?_⟩
        exact hPrefixIff.2 C.1
      · intro L
        simp only [RecordCarryCompatibleFrom]
        refine ⟨?_, ?_⟩
        · exact hPrefixIff.1 L.1.2.2.2
        · exact hTailIff.2 L.2

end Critical
end Collatz3
