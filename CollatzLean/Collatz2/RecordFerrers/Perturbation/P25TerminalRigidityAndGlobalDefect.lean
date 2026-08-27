import CollatzLean.Collatz2.RecordFerrers.Perturbation.P24CanonicalInteriorFlexibility

/-!
# Record–Ferrers 摂動理論 25: terminal rigid の小例外化と global defect skeleton

P24 は cut 1 以下の phase にある anchor 上で、outer endpoint も interior である
adjacent RecordBlock pair の lower-best rigid branch を排除した。

本ファイルでは terminal pair を扱う。

まず primitive + StripReduced + FirstCrossing では P19 の complement identity と
P20 の terminal depth identity から、whole denominator `p` の phase が
全 proper denominator より strict に大きいことを示す。
これは continued fraction を使わない pure Record–Ferrers / carry theorem である。

次に terminal adjacent pair

  a -- r -- (a+r) -- s -- p

で outer length `L=r+s` が lower-best rigid だと仮定する。
left block は interior carry 1、right block は terminal carry 0 なので、
local rigid carry `criticalCarry r s = 1` と cocycle を合わせると outer carry `criticalCarry a L = 0`。

anchor phase ≤ phase(1)、rigid L の phase ≤ phase(2) から

  phase(p) = phase(a) phase(L) ≤ 27/16 = phase(3)

となる。一方 whole `p` は strict upper-best なので `p>3` なら

  phase(3) < phase(p)

で矛盾する。

従って terminal rigid pair が残れるのは `p=3` だけ。
最後に RecordChain を再帰して、`p>3` の cut-1 canonical decomposition では
terminal pair を含む全 adjacent pair が defect split を持つことを一つの theorem にまとめる。
-/

namespace Collatz2
namespace RecordFerrers

open Word

/--
`L` の critical phase が、それ以前の全 positive denominator より strict に大きいこと。
P22 の `CriticalLowerPhaseLess x L` をそのまま upper-record 条件として使う。
-/
def CriticalUpperBestDenominator (L : ℕ) : Prop :=
  0 < L ∧
    ∀ x : ℕ,
      0 < x →
      x < L →
      CriticalLowerPhaseLess x L

/-- `criticalHeight 3 = 4`。従って cut 3 の phase は `27/16`。 -/
theorem criticalHeight_three_recordFerrers :
    criticalHeight 3 = 4 := by
  norm_num [criticalHeight]
  decide

/--
## 主定理 1: primitive/reduced whole denominator は strict upper-best

P19:

  criticalHeight x + criticalHeight (p-x) + 1 = H

P20:

  H = criticalHeight p + 1

を合わせると、全 proper split で

  criticalCarry x (p-x) = 0.

P22 によりこれは `phase(x) < phase(p)` と exact に同値。
continued fraction は一切使わない。
-/
theorem criticalUpperBestDenominator_of_primitiveReduced
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (v : FiberPoint P.oddCount P.twoDepth)
    (hF : FirstCrossing v.word)
    (hp : 1 < P.oddCount) :
    CriticalUpperBestDenominator P.oddCount := by
  refine ⟨P.oddCount_pos, ?_⟩
  intro x hxPos hxLt
  have hComplement :=
    criticalHeight_add_complement_add_one_eq_twoDepth_of_primitiveReduced
      P hPrimitive hReduced hxPos hxLt
  have hTerminalDepth :=
    twoDepth_eq_criticalHeight_add_one_of_primitiveReduced
      P hPrimitive hReduced v hF hp
  have hAdd :=
    criticalHeight_add_eq x (P.oddCount - x)
  have hSum : x + (P.oddCount - x) = P.oddCount := by
    omega
  rw [hSum] at hAdd
  have hCarryLe :=
    criticalCarry_le_one x (P.oddCount - x)
  have hCarryZero :
      criticalCarry x (P.oddCount - x) = 0 := by
    omega
  exact
    (criticalCarry_eq_zero_iff_criticalLowerPhaseLess hxLt).1
      hCarryZero

/--
source canonical chain の terminal adjacent pair。
右 block の endpoint は terminal `p` そのもの。
-/
structure AdjacentTerminalRecordPair
    (P : Word.ContractingExponentPair)
    (u : FiberPoint P.oddCount P.twoDepth)
    (a r s : ℕ) : Prop where
  anchor_pos : 0 < a
  leftSource : RecordBlock u a r
  rightSource : RecordBlock u (a + r) s
  outerTerminal : (a + r) + s = P.oddCount

namespace AdjacentTerminalRecordPair

/-- terminal pair の左 block は interior。 -/
theorem leftInterior
    {P : Word.ContractingExponentPair}
    {u : FiberPoint P.oddCount P.twoDepth}
    {a r s : ℕ}
    (T : AdjacentTerminalRecordPair P u a r s) :
    a + r < P.oddCount := by
  calc
    a + r < (a + r) + s := by
      exact Nat.lt_add_of_pos_right T.rightSource.length_pos
    _ = P.oddCount :=
      T.outerTerminal

/-- terminal pair の whole denominator は少なくとも 3。 -/
theorem oddCount_ge_three
    {P : Word.ContractingExponentPair}
    {u : FiberPoint P.oddCount P.twoDepth}
    {a r s : ℕ}
    (T : AdjacentTerminalRecordPair P u a r s) :
    3 ≤ P.oddCount := by
  have ha : 0 < a :=
    T.anchor_pos
  have hr : 0 < r :=
    T.leftSource.length_pos
  have hs : 0 < s :=
    T.rightSource.length_pos
  calc
    3 ≤ (a + r) + s := by
      omega
    _ = P.oddCount :=
      T.outerTerminal

/-- 左 block の anchor carry は 1。 -/
theorem anchorLeftCarry_one
    {P : Word.ContractingExponentPair}
    {u : FiberPoint P.oddCount P.twoDepth}
    {a r s : ℕ}
    (T : AdjacentTerminalRecordPair P u a r s) :
    criticalCarry a r = 1 :=
  T.leftSource.criticalCarry_eq_one_of_interior T.leftInterior

/-- right terminal block の carry は whole FirstCrossing から 0。 -/
theorem rightTerminalCarry_zero
    {P : Word.ContractingExponentPair}
    {u : FiberPoint P.oddCount P.twoDepth}
    {a r s : ℕ}
    (T : AdjacentTerminalRecordPair P u a r s)
    (hFu : FirstCrossing u.word) :
    criticalCarry (a + r) s = 0 :=
  T.rightSource.criticalCarry_eq_zero_of_terminal
    T.outerTerminal hFu

/-- lower-best rigid outer length なら old local split `r|s` の carry は 1。 -/
theorem localCarry_one_of_lowerBest
    {P : Word.ContractingExponentPair}
    {u : FiberPoint P.oddCount P.twoDepth}
    {a r s : ℕ}
    (T : AdjacentTerminalRecordPair P u a r s)
    (hBest : CriticalLowerBestDenominator (r + s)) :
    criticalCarry r s = 1 := by
  have hrPos := T.leftSource.length_pos
  have hsPos := T.rightSource.length_pos
  have hAll :=
    (criticalLowerBest_iff_all_proper_carry_one hBest.1).1 hBest
  have hCarry :
      criticalCarry r ((r + s) - r) = 1 :=
    hAll r hrPos (by omega)
  have hSub : (r + s) - r = s := by omega
  rw [hSub] at hCarry
  exact hCarry

/--
terminal pair が lower-best rigid なら anchor から terminal までの outer carry は 0。

  1 + 0 = 1 + outerCarry

という cocycle から従う。
-/
theorem outerCarry_zero_of_lowerBest
    {P : Word.ContractingExponentPair}
    {u : FiberPoint P.oddCount P.twoDepth}
    {a r s : ℕ}
    (T : AdjacentTerminalRecordPair P u a r s)
    (hFu : FirstCrossing u.word)
    (hBest : CriticalLowerBestDenominator (r + s)) :
    criticalCarry a (r + s) = 0 := by
  have hLeft : criticalCarry a r = 1 :=
    T.anchorLeftCarry_one
  have hRight : criticalCarry (a + r) s = 0 :=
    T.rightTerminalCarry_zero hFu
  have hLocal : criticalCarry r s = 1 :=
    T.localCarry_one_of_lowerBest hBest
  have hCoc := criticalCarry_cocycle a r s
  rw [hLeft, hRight, hLocal] at hCoc
  have hOuter := criticalCarry_le_one a (r + s)
  omega

/--
terminal rigid 仮定の下で whole phase は cut 3 の phase `27/16` 以下になる。
-/
theorem sixteen_mul_threePow_terminal_le_twentySeven_mul_twoPow
    {P : Word.ContractingExponentPair}
    {u : FiberPoint P.oddCount P.twoDepth}
    {a r s : ℕ}
    (T : AdjacentTerminalRecordPair P u a r s)
    (hFu : FirstCrossing u.word)
    (hA : CriticalPhaseAtMostOne a)
    (hBest : CriticalLowerBestDenominator (r + s)) :
    16 * 3 ^ P.oddCount ≤
      27 * 2 ^ criticalHeight P.oddCount := by
  have hTwo : 2 ≤ r + s := by
    have hr := T.leftSource.length_pos
    have hs := T.rightSource.length_pos
    omega
  have hScaled :=
    sixteen_mul_threePow_add_le_twentySeven_mul_twoPow_add
      hA hBest hTwo
  have hOuterCarry : criticalCarry a (r + s) = 0 :=
    T.outerCarry_zero_of_lowerBest hFu hBest
  have hAdd := criticalHeight_add_eq a (r + s)
  rw [hOuterCarry] at hAdd
  simp only [Nat.add_zero] at hAdd
  have hIndex : a + (r + s) = P.oddCount := by
    simpa [Nat.add_assoc] using T.outerTerminal
  rw [hIndex] at hAdd
  have hScaled' := hScaled
  rw [hIndex, ← hAdd] at hScaled'
  exact hScaled'

/--
## 主定理 2: terminal rigid は `p=3` にしか残れない

primitive + StripReduced FirstCrossing whole fiber で、anchor phase が cut 1 以下なら、
terminal adjacent pair の outer length が lower-best rigid であるためには
whole denominator が exactly 3 でなければならない。
-/
theorem oddCount_eq_three_of_lowerBest
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (hFu : FirstCrossing u.word)
    {a r s : ℕ}
    (T : AdjacentTerminalRecordPair P u a r s)
    (hA : CriticalPhaseAtMostOne a)
    (hBest : CriticalLowerBestDenominator (r + s)) :
    P.oddCount = 3 := by
  have hpGe : 3 ≤ P.oddCount := T.oddCount_ge_three
  by_contra hNe
  have hpGt : 3 < P.oddCount := by omega
  have hUpperBest :=
    criticalUpperBestDenominator_of_primitiveReduced
      P hPrimitive hReduced u hFu (by omega)
  have hPhaseThree :
      CriticalLowerPhaseLess 3 P.oddCount :=
    hUpperBest.2 3 (by omega) hpGt
  have hStrict :
      27 * 2 ^ criticalHeight P.oddCount <
        16 * 3 ^ P.oddCount := by
    unfold CriticalLowerPhaseLess at hPhaseThree
    rw [criticalHeight_three_recordFerrers] at hPhaseThree
    norm_num at hPhaseThree
    simpa [Nat.mul_comm] using hPhaseThree
  have hWeak :=
    T.sixteen_mul_threePow_terminal_le_twentySeven_mul_twoPow
      hFu hA hBest
  exact (Nat.not_lt_of_ge hWeak) hStrict

/-- `p>3` なら terminal adjacent pair も lower-best rigid ではない。 -/
theorem not_criticalLowerBest_of_phaseAtMostOne_of_gt_three
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (hFu : FirstCrossing u.word)
    {a r s : ℕ}
    (T : AdjacentTerminalRecordPair P u a r s)
    (hA : CriticalPhaseAtMostOne a)
    (hpGt : 3 < P.oddCount) :
    ¬ CriticalLowerBestDenominator (r + s) := by
  intro hBest
  have hEq :=
    T.oddCount_eq_three_of_lowerBest
      P hPrimitive hReduced u hFu hA hBest
  omega

/-- `p>3` の terminal pair には defect split が自動的に存在する。 -/
theorem exists_defectSplit_of_phaseAtMostOne_of_gt_three
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (hFu : FirstCrossing u.word)
    {a r s : ℕ}
    (T : AdjacentTerminalRecordPair P u a r s)
    (hA : CriticalPhaseAtMostOne a)
    (hpGt : 3 < P.oddCount) :
    ∃ x : ℕ, DefectSplit (r + s) x := by
  have hLPos : 0 < r + s := by
    have hr := T.leftSource.length_pos
    omega
  exact
    (exists_defectSplit_iff_not_criticalLowerBest hLPos).2
      (T.not_criticalLowerBest_of_phaseAtMostOne_of_gt_three
        P hPrimitive hReduced u hFu hA hpGt)

end AdjacentTerminalRecordPair

/--
length list の全 adjacent pair が defect split を持つこと。

`[r,s]` も含めて最後の terminal adjacent pair まで要求する。
-/
def AllAdjacentDefectSplits : List ℕ → Prop
  | [] => True
  | [_] => True
  | r :: s :: rest =>
      (∃ x : ℕ, DefectSplit (r + s) x) ∧
        AllAdjacentDefectSplits (s :: rest)

namespace RecordChain

/--
## 主定理 3: cut-1 phase 領域の whole RecordChain は全 adjacent pair で flexible

`p>3` の primitive + StripReduced FirstCrossing fiber で、
start anchor の phase が cut 1 以下なら、terminal pair を含む chain の全 adjacent pair に
P22 defect split が存在する。

interior pair には P24、最後の terminal pair には本ファイルの `p=3` 排除を使う。
-/
theorem allAdjacentDefectSplits_of_phaseAtMostOne
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (hFu : FirstCrossing u.word)
    {start : ℕ}
    {lengths : List ℕ}
    (C : RecordChain u start lengths)
    (hpGt : 3 < P.oddCount) :
    0 < start →
      CriticalPhaseAtMostOne start →
        AllAdjacentDefectSplits lengths := by
  induction C with
  | @last start len B hTerminal =>
      intro hStartPos hPhase
      simp [AllAdjacentDefectSplits]
  | @cons start len rest B hInterior T ih =>
      intro hStartPos hPhase
      have hCarry : criticalCarry start len = 1 :=
        B.criticalCarry_eq_one_of_interior hInterior
      have hNextPhase :
          CriticalPhaseAtMostOne (start + len) :=
        hPhase.step_of_carry_one hCarry
      have hNextPos : 0 < start + len := by
        omega
      have hTailAll : AllAdjacentDefectSplits rest :=
        ih hNextPos hNextPhase
      cases T with
      | @last _ len2 B2 hTerminal2 =>
          have hPair :
              AdjacentTerminalRecordPair P u start len len2 := {
            anchor_pos := hStartPos
            leftSource := B
            rightSource := B2
            outerTerminal := hTerminal2
          }
          have hDefect :=
            hPair.exists_defectSplit_of_phaseAtMostOne_of_gt_three
              P hPrimitive hReduced u hFu hPhase hpGt
          simp only [AllAdjacentDefectSplits]
          exact ⟨hDefect, trivial⟩
      | @cons _ len2 rest2 B2 hInterior2 T2 =>
          have hPair :
              AdjacentInteriorRecordPair P u start len len2 := {
            anchor_pos := hStartPos
            leftSource := B
            rightSource := B2
            outerInterior := hInterior2
          }
          have hDefect :=
            hPair.exists_defectSplit_of_phaseAtMostOne hPhase
          simp only [AllAdjacentDefectSplits]
          exact ⟨hDefect, hTailAll⟩

end RecordChain

namespace RecordDecomposition

/--
`p>3` なら cut 1 から始まる genuine decomposition の全 adjacent pair が defect split を持つ。
-/
theorem allAdjacentDefectSplits_one_of_gt_three
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    {u : FiberPoint P.oddCount P.twoDepth}
    (D : RecordDecomposition u 1)
    (hpGt : 3 < P.oddCount) :
    AllAdjacentDefectSplits D.lengths := by
  exact
    D.chain.allAdjacentDefectSplits_of_phaseAtMostOne
      P hPrimitive hReduced u D.whole_firstCrossing hpGt
      (by omega) criticalPhaseAtMostOne_one

end RecordDecomposition

/--
## 主定理 4: primitive/reduced FirstCrossing canonical skeleton の global defect existence

`p>3` なら P20 により cut 1 から canonical RecordDecomposition が存在し、
その全 adjacent pair は P22 defect split を持つ。

これは continued fraction 分類を使わずに、canonical skeleton 上の rigid branch を
whole list から排除する theorem である。

注意: interior pair の defect split は P23 により actual perturbation まで既に実現できる。
terminal pair の actual realization は次段の課題として残る。
-/
theorem exists_recordDecomposition_one_with_allAdjacentDefectSplits
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (hFu : FirstCrossing u.word)
    (hpGt : 3 < P.oddCount) :
    ∃ D : RecordDecomposition u 1,
      AllAdjacentDefectSplits D.lengths := by
  obtain ⟨D⟩ :=
    exists_recordDecomposition_one_of_primitiveReduced
      P hPrimitive hReduced u hFu (by omega)
  exact
    ⟨D,
      D.allAdjacentDefectSplits_one_of_gt_three
        P hPrimitive hReduced hpGt⟩

end RecordFerrers
end Collatz2
