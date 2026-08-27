import CollatzLean.Collatz2.RecordFerrers.Perturbation.P25TerminalRigidityAndGlobalDefect

/-!
# Record–Ferrers 摂動理論 26: terminal actual merge と canonical adjacent-pair flexibility

P24 は canonical interior adjacent pair について lower-best rigid branch を排除し、
P23 の actual two-plateau perturbation へ接続した。
P25 は terminal adjacent pair についても `p > 3` なら defect split が必ず存在することを示したが、
terminal endpoint は critical roof ではないため P23 の realization をそのまま適用できなかった。

本ファイルでは terminal 専用の two-plateau Ferrers target を構成する。
source terminal pair

  a -- r -- (a+r) -- s -- p

と defect split `x` に対し `k := a+x` と置き、proper columns 上で

  j ≤ a      : source excess
  a < j < k  : criticalExcess a
  k ≤ j < p  : criticalExcess k

という二段 plateau を作る。terminal `p` は Ferrers column ではなく、decoder によって
fixed depth `H` に自動的に戻る。

primitive + StripReduced + FirstCrossing では anchor `a` から terminal までの outer carry は 0。
defect split の local carry も 0 なので cocycle から

  criticalCarry a x = 0
  criticalCarry (a+x) ((r+s)-x) = 0

が同時に従う。従って target cut `k` は roof contact だが anchor `a` から admissible ではない。
さらに plateau 全体には proper admissible contact が一つも存在せず、P19 terminal absorption により

  RecordBlock v a (r+s)

が得られる。つまり source の最後の二 block `[r,s]` は target で一つの `[r+s]` に merge する。

最後に P24 の interior actual perturbation と本 terminal merge を一つにまとめ、`p > 3` の
canonical phase 領域では任意の adjacent pair が actual fixed-chord deformation を持つことを示す。
-/

namespace Collatz2
namespace RecordFerrers

open Word

namespace AdjacentTerminalRecordPair

/-- terminal pair の anchor は proper。 -/
theorem anchor_lt_terminal
    {P : Word.ContractingExponentPair}
    {u : FiberPoint P.oddCount P.twoDepth}
    {a r s : ℕ}
    (T : AdjacentTerminalRecordPair P u a r s) :
    a < P.oddCount := by
  have hLeft := T.leftInterior
  exact lt_trans (Nat.lt_add_of_pos_right T.leftSource.length_pos) hLeft

/-- terminal pair の anchor は source roof 上。 -/
theorem anchorRoof
    {P : Word.ContractingExponentPair}
    {u : FiberPoint P.oddCount P.twoDepth}
    {a r s : ℕ}
    (T : AdjacentTerminalRecordPair P u a r s) :
    RoofContact u a := by
  unfold RoofContact
  exact T.leftSource.start_roof

/-- terminal pair の outer length は `p-a`。 -/
theorem anchor_add_outerLength_eq_terminal
    {P : Word.ContractingExponentPair}
    {u : FiberPoint P.oddCount P.twoDepth}
    {a r s : ℕ}
    (T : AdjacentTerminalRecordPair P u a r s) :
    a + (r + s) = P.oddCount := by
  simpa [Nat.add_assoc] using T.outerTerminal

/-- terminal pair の outer length は exact に `p-a`。 -/
theorem outerLength_eq_terminal_sub_anchor
    {P : Word.ContractingExponentPair}
    {u : FiberPoint P.oddCount P.twoDepth}
    {a r s : ℕ}
    (T : AdjacentTerminalRecordPair P u a r s) :
    r + s = P.oddCount - a := by
  have h := T.anchor_add_outerLength_eq_terminal
  omega

/--
primitive + StripReduced + whole FirstCrossing では、terminal pair の anchor から terminal までの
outer carry は必ず 0。

P19 の complement identity と P20 の terminal-depth identity を直接比較する。
-/
theorem outerCarry_zero_of_primitiveReduced
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (hFu : FirstCrossing u.word)
    {a r s : ℕ}
    (T : AdjacentTerminalRecordPair P u a r s) :
    criticalCarry a (r + s) = 0 := by
  have hAnchorPos : 0 < a := T.anchor_pos
  have hAnchorLt : a < P.oddCount := T.anchor_lt_terminal
  have hComplement :=
    criticalHeight_add_complement_add_one_eq_twoDepth_of_primitiveReduced
      P hPrimitive hReduced hAnchorPos hAnchorLt
  have hTerminalDepth :=
    twoDepth_eq_criticalHeight_add_one_of_primitiveReduced
      P hPrimitive hReduced u hFu (by omega)
  have hOuterLen : r + s = P.oddCount - a :=
    T.outerLength_eq_terminal_sub_anchor
  rw [← hOuterLen] at hComplement
  have hAdd := criticalHeight_add_eq a (r + s)
  have hIndex : a + (r + s) = P.oddCount :=
    T.anchor_add_outerLength_eq_terminal
  rw [hIndex] at hAdd
  have hCarryLe := criticalCarry_le_one a (r + s)
  omega

/--
primitive/reduced terminal pair の old local split `r|s` は carry one。

  anchor-left = 1,
  right-terminal = 0,
  outer = 0

を cocycle に入れる。
-/
theorem sourceLocalCarry_one_of_primitiveReduced
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (hFu : FirstCrossing u.word)
    {a r s : ℕ}
    (T : AdjacentTerminalRecordPair P u a r s) :
    criticalCarry r s = 1 := by
  have hLeft : criticalCarry a r = 1 := T.anchorLeftCarry_one
  have hRight : criticalCarry (a + r) s = 0 :=
    T.rightTerminalCarry_zero hFu
  have hOuter : criticalCarry a (r + s) = 0 :=
    T.outerCarry_zero_of_primitiveReduced P hPrimitive hReduced u hFu
  have hCoc := criticalCarry_cocycle a r s
  rw [hLeft, hRight, hOuter] at hCoc
  have hLocalLe := criticalCarry_le_one r s
  omega

/-- defect split は old middle `x=r` と一致しない。 -/
theorem defectSplit_ne_oldMiddle_of_primitiveReduced
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (hFu : FirstCrossing u.word)
    {a r s x : ℕ}
    (T : AdjacentTerminalRecordPair P u a r s)
    (D : DefectSplit (r + s) x) :
    x ≠ r := by
  intro hx
  subst x
  have hLocal : criticalCarry r ((r + s) - r) = 0 := D.2.2
  have hSub : (r + s) - r = s := by omega
  rw [hSub] at hLocal
  have hOne :=
    T.sourceLocalCarry_one_of_primitiveReduced
      P hPrimitive hReduced u hFu
  omega

/--
terminal outer carry=0 と defect local carry=0 の組合せでは、
new cut の左右 carry は両方とも 0 に固定される。
-/
theorem defectSideCarries_zero_of_primitiveReduced
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (hFu : FirstCrossing u.word)
    {a r s x : ℕ}
    (T : AdjacentTerminalRecordPair P u a r s)
    (D : DefectSplit (r + s) x) :
    criticalCarry a x = 0 ∧
      criticalCarry (a + x) ((r + s) - x) = 0 := by
  let y := (r + s) - x
  have hy : y = (r + s) - x := rfl
  have hxy : x + y = r + s := by
    dsimp [y]
    have hx : x < r + s := D.2.1
    omega
  have hLocal : criticalCarry x y = 0 := by
    simpa [y] using D.2.2
  have hOuter : criticalCarry a (r + s) = 0 :=
    T.outerCarry_zero_of_primitiveReduced P hPrimitive hReduced u hFu
  have hCoc := criticalCarry_cocycle a x y
  rw [hLocal, hxy, hOuter] at hCoc
  constructor --<;> omega
  · have hCoc' :
      criticalCarry a x + criticalCarry (a + x) y = 0 := by
      simpa using hCoc
    omega
  · rw [← hy]
    have hCoc' :
      criticalCarry a x + criticalCarry (a + x) y = 0 := by
      simpa using hCoc
    omega

end AdjacentTerminalRecordPair

/--
terminal 用 two-plateau excess。
proper column `p` までは source に戻さず、`k` 以後を `criticalExcess k` に固定する。
-/
def terminalTwoPlateauExcess
    {p H : ℕ}
    (u : FiberPoint p H)
    (a k j : ℕ) : ℕ :=
  if j ≤ a then
    u.excessAt j
  else if j < k then
    criticalExcess a
  else
    criticalExcess k

@[simp] theorem terminalTwoPlateauExcess_of_le_anchor
    {p H : ℕ}
    (u : FiberPoint p H)
    (a k j : ℕ)
    (hj : j ≤ a) :
    terminalTwoPlateauExcess u a k j = u.excessAt j := by
  simp [terminalTwoPlateauExcess, hj]

@[simp] theorem terminalTwoPlateauExcess_of_leftPlateau
    {p H : ℕ}
    (u : FiberPoint p H)
    (a k j : ℕ)
    (haj : a < j)
    (hjk : j < k) :
    terminalTwoPlateauExcess u a k j = criticalExcess a := by
  simp [terminalTwoPlateauExcess, not_le.mpr haj, hjk]

@[simp] theorem terminalTwoPlateauExcess_of_rightPlateau
    {p H : ℕ}
    (u : FiberPoint p H)
    (a k j : ℕ)
    (hak : a < k)
    (hkj : k ≤ j) :
    terminalTwoPlateauExcess u a k j = criticalExcess k := by
  have haj : a < j := lt_of_lt_of_le hak hkj
  simp [terminalTwoPlateauExcess, not_le.mpr haj, not_lt.mpr hkj]

/-- terminal two-plateau profile は nondecreasing。 -/
theorem terminalTwoPlateauExcess_mono
    {p H : ℕ}
    (u : FiberPoint p H)
    {a k i j : ℕ}
    (hak : a < k)
    (hkp : k < p)
    (hRoofA : RoofContact u a)
    (hij : i ≤ j)
    (hjp : j < p) :
    terminalTwoPlateauExcess u a k i ≤
      terminalTwoPlateauExcess u a k j := by
  have hap : a < p := lt_trans hak hkp
  have hRoofAEx : u.excessAt a = criticalExcess a :=
    excessAt_eq_criticalExcess_of_roof hRoofA
  by_cases hjA : j ≤ a
  · have hiA : i ≤ a := le_trans hij hjA
    rw [terminalTwoPlateauExcess_of_le_anchor u a k i hiA,
        terminalTwoPlateauExcess_of_le_anchor u a k j hjA]
    exact u.excess_mono hij (Nat.le_of_lt hjp)
  · have hAj : a < j := by omega
    by_cases hiA : i ≤ a
    · rw [terminalTwoPlateauExcess_of_le_anchor u a k i hiA]
      by_cases hjK : j < k
      · rw [terminalTwoPlateauExcess_of_leftPlateau u a k j hAj hjK]
        have hMono := u.excess_mono hiA (Nat.le_of_lt hap)
        rw [hRoofAEx] at hMono
        exact hMono
      · have hKj : k ≤ j := by omega
        rw [terminalTwoPlateauExcess_of_rightPlateau u a k j hak hKj]
        have hMono := u.excess_mono hiA (Nat.le_of_lt hap)
        rw [hRoofAEx] at hMono
        exact hMono.trans (criticalExcess_mono (Nat.le_of_lt hak))
    · have hAi : a < i := by omega
      by_cases hiK : i < k
      · rw [terminalTwoPlateauExcess_of_leftPlateau u a k i hAi hiK]
        by_cases hjK : j < k
        · rw [terminalTwoPlateauExcess_of_leftPlateau u a k j hAj hjK]
        · have hKj : k ≤ j := by omega
          rw [terminalTwoPlateauExcess_of_rightPlateau u a k j hak hKj]
          exact criticalExcess_mono (Nat.le_of_lt hak)
      · have hKi : k ≤ i := by omega
        have hKj : k ≤ j := le_trans hKi hij
        rw [terminalTwoPlateauExcess_of_rightPlateau u a k i hak hKi,
            terminalTwoPlateauExcess_of_rightPlateau u a k j hak hKj]

/-- terminal two-plateau natural profile を Ferrers shape にする。 -/
def terminalTwoPlateauShape
    {p H : ℕ}
    (u : FiberPoint p H)
    (a k : ℕ)
    (hak : a < k)
    (hkp : k < p)
    (hRoofA : RoofContact u a) : FerrersShape p :=
  { column := fun i => terminalTwoPlateauExcess u a k i.1
    mono := by
      intro i j hij
      have hijNat : i.1 ≤ j.1 := hij
      exact terminalTwoPlateauExcess_mono
        u hak hkp hRoofA hijNat j.isLt }

/--
terminal depth `H = criticalHeight p + 1` の下で terminal plateau は fixed rectangle 内に収まる。
-/
def terminalTwoPlateauFiberShape
    {p H : ℕ}
    (u : FiberPoint p H)
    (a k : ℕ)
    (hak : a < k)
    (hkp : k < p)
    (hRoofA : RoofContact u a)
    (hTerminalDepth : H = criticalHeight p + 1) : FiberShape p H := by
  have hp : 0 < p := by omega
  have hpH : p ≤ H := by
    have h := FiberPoint.oddSteps_le_twoSteps_of_valid u.valid
    rw [u.oddSteps_eq, u.twoSteps_eq] at h
    exact h
  have hRoofAEx : u.excessAt a = criticalExcess a :=
    excessAt_eq_criticalExcess_of_roof hRoofA
  have hABound : criticalExcess a ≤ H - p := by
    rw [← hRoofAEx]
    exact u.excess_le_rectangleHeight (Nat.le_of_lt (lt_trans hak hkp))
  have hKPBound : criticalExcess k ≤ H - p := by
    have hQMono : criticalExcess k ≤ criticalExcess p :=
      criticalExcess_mono (Nat.le_of_lt hkp)
    have hpCrit := index_le_criticalHeight p
    have hQp : criticalExcess p ≤ H - p := by
      unfold criticalExcess
      rw [hTerminalDepth]
      omega
    exact hQMono.trans hQp
  refine {
    shape := terminalTwoPlateauShape u a k hak hkp hRoofA
    p_pos := hp
    p_le_H := hpH
    first_zero := ?_
    bounded := ?_
  }
  · change terminalTwoPlateauExcess u a k 0 = 0
    rw [terminalTwoPlateauExcess_of_le_anchor u a k 0 (Nat.zero_le _)]
    exact u.excessAt_zero
  · intro i
    change terminalTwoPlateauExcess u a k i.1 ≤ H - p
    by_cases hiA : i.1 ≤ a
    · rw [terminalTwoPlateauExcess_of_le_anchor u a k i.1 hiA]
      exact u.excess_le_rectangleHeight (Nat.le_of_lt i.isLt)
    · have hAi : a < i.1 := by omega
      by_cases hiK : i.1 < k
      · rw [terminalTwoPlateauExcess_of_leftPlateau u a k i.1 hAi hiK]
        exact hABound
      · have hKi : k ≤ i.1 := by omega
        rw [terminalTwoPlateauExcess_of_rightPlateau u a k i.1 hak hKi]
        exact hKPBound

@[simp] theorem terminalTwoPlateauFiberShape_shape
    {p H : ℕ}
    (u : FiberPoint p H)
    (a k : ℕ)
    (hak : a < k)
    (hkp : k < p)
    (hRoofA : RoofContact u a)
    (hTerminalDepth : H = criticalHeight p + 1) :
    (terminalTwoPlateauFiberShape u a k
      hak hkp hRoofA hTerminalDepth).shape =
      terminalTwoPlateauShape u a k hak hkp hRoofA := rfl

/-- exact decoder による terminal two-plateau actual target。 -/
def terminalTwoPlateauTarget
    {p H : ℕ}
    (u : FiberPoint p H)
    (a k : ℕ)
    (hak : a < k)
    (hkp : k < p)
    (hRoofA : RoofContact u a)
    (hTerminalDepth : H = criticalHeight p + 1) : FiberPoint p H :=
  (terminalTwoPlateauFiberShape
    u a k hak hkp hRoofA hTerminalDepth).toFiberPoint

/-- terminal target proper height の closed form。 -/
theorem terminalTwoPlateauTarget_height
    {p H : ℕ}
    (u : FiberPoint p H)
    (a k : ℕ)
    (hak : a < k)
    (hkp : k < p)
    (hRoofA : RoofContact u a)
    (hTerminalDepth : H = criticalHeight p + 1)
    {j : ℕ}
    (hjp : j < p) :
    (terminalTwoPlateauTarget u a k
      hak hkp hRoofA hTerminalDepth).height j =
      j + terminalTwoPlateauExcess u a k j := by
  have hPrefix :=
    (terminalTwoPlateauFiberShape
      u a k hak hkp hRoofA hTerminalDepth).prefixTwoDepth_toWord hjp
  have hAt :
      (terminalTwoPlateauFiberShape
        u a k hak hkp hRoofA hTerminalDepth).shape.atNat j =
        terminalTwoPlateauExcess u a k j := by
    rw [terminalTwoPlateauFiberShape_shape]
    simp [terminalTwoPlateauShape, FerrersShape.atNat, hjp]
  rw [hAt] at hPrefix
  change
    prefixTwoDepth
        (terminalTwoPlateauFiberShape
          u a k hak hkp hRoofA hTerminalDepth).toWord j =
      j + terminalTwoPlateauExcess u a k j
  exact hPrefix

/-- terminal target の anchor は source と同じ roof contact。 -/
theorem terminalTwoPlateauTarget_anchorRoof
    {p H : ℕ}
    (u : FiberPoint p H)
    (a k : ℕ)
    (hak : a < k)
    (hkp : k < p)
    (hRoofA : RoofContact u a)
    (hTerminalDepth : H = criticalHeight p + 1) :
    RoofContact
      (terminalTwoPlateauTarget u a k
        hak hkp hRoofA hTerminalDepth) a := by
  have hap : a < p := lt_trans hak hkp
  have hHeight :=
    terminalTwoPlateauTarget_height
      u a k hak hkp hRoofA hTerminalDepth hap
  have hEx := terminalTwoPlateauExcess_of_le_anchor u a k a le_rfl
  rw [hEx] at hHeight
  have hSource := u.height_eq_index_add_excess (Nat.le_of_lt hap)
  unfold RoofContact at hRoofA ⊢
  rw [hHeight, ← hSource, hRoofA]

/-- 新 cut `k` は target roof に exact に接触する。 -/
theorem terminalTwoPlateauTarget_roof_cut
    {p H : ℕ}
    (u : FiberPoint p H)
    (a k : ℕ)
    (hak : a < k)
    (hkp : k < p)
    (hRoofA : RoofContact u a)
    (hTerminalDepth : H = criticalHeight p + 1) :
    RoofContact
      (terminalTwoPlateauTarget u a k
        hak hkp hRoofA hTerminalDepth) k := by
  have hHeight :=
    terminalTwoPlateauTarget_height
      u a k hak hkp hRoofA hTerminalDepth hkp
  have hEx :
      terminalTwoPlateauExcess u a k k = criticalExcess k :=
    terminalTwoPlateauExcess_of_rightPlateau u a k k hak le_rfl
  rw [hEx] at hHeight
  unfold RoofContact
  rw [hHeight]
  unfold criticalExcess
  have hBase := index_le_criticalHeight k
  omega

/-- anchor より左では source height と完全に一致する。 -/
theorem terminalTwoPlateauTarget_height_eq_source_of_le_anchor
    {p H : ℕ}
    (u : FiberPoint p H)
    (a k : ℕ)
    (hak : a < k)
    (hkp : k < p)
    (hRoofA : RoofContact u a)
    (hTerminalDepth : H = criticalHeight p + 1)
    {j : ℕ}
    (hja : j ≤ a) :
    (terminalTwoPlateauTarget u a k
      hak hkp hRoofA hTerminalDepth).height j =
      u.height j := by
  have hjp : j < p := lt_of_le_of_lt hja (lt_trans hak hkp)
  have hHeight :=
    terminalTwoPlateauTarget_height
      u a k hak hkp hRoofA hTerminalDepth hjp
  rw [terminalTwoPlateauExcess_of_le_anchor u a k j hja] at hHeight
  have hSource := u.height_eq_index_add_excess (Nat.le_of_lt hjp)
  exact hHeight.trans hSource.symm

/-- terminal two-plateau target は actual `BlockReplacement u v a p`。 -/
theorem terminalTwoPlateauTarget_blockReplacement
    {p H : ℕ}
    (u : FiberPoint p H)
    (a k : ℕ)
    (hak : a < k)
    (hkp : k < p)
    (hRoofA : RoofContact u a)
    (hTerminalDepth : H = criticalHeight p + 1) :
    BlockReplacement u
      (terminalTwoPlateauTarget u a k
        hak hkp hRoofA hTerminalDepth)
      a p := by
  refine {
    start_lt_stop := lt_trans hak hkp
    stop_le_terminal := le_rfl
    outside := ?_
  }
  intro j hjp hOutside
  rcases hOutside with hJA | hPJ
  · have hEq :=
      terminalTwoPlateauTarget_height_eq_source_of_le_anchor
        u a k hak hkp hRoofA hTerminalDepth hJA
    unfold profileDisplacement
    rw [hEq]
    ring
  · have hjEq : j = p := by omega
    subst j
    unfold profileDisplacement
    simp

/-- terminal two-plateau shape は critical roof の下側にある。 -/
theorem terminalTwoPlateauShape_isCriticalSubshape
    {p H : ℕ}
    (u : FiberPoint p H)
    (a k : ℕ)
    (hak : a < k)
    (hkp : k < p)
    (hRoofA : RoofContact u a)
    (hFu : FirstCrossing u.word) :
    IsCriticalSubshape
      (terminalTwoPlateauShape u a k hak hkp hRoofA) := by
  have hp : 0 < p := by omega
  have hContract : ContractingChord p H := by
    have hPow :=
      (contracting_iff_threePow_lt_twoPow).1 hFu.terminalContracting
    simpa [ContractingChord, u.oddSteps_eq, u.twoSteps_eq] using hPow
  have hSource : IsCriticalSubshape u.toFerrersShape :=
    (firstCrossing_iff_criticalSubshape u hp hContract).1 hFu
  intro i
  have hSourceI := hSource i
  change u.excessAt i.1 ≤ criticalExcess i.1 at hSourceI
  change terminalTwoPlateauExcess u a k i.1 ≤ criticalExcess i.1
  by_cases hiA : i.1 ≤ a
  · rw [terminalTwoPlateauExcess_of_le_anchor u a k i.1 hiA]
    exact hSourceI
  · have hAi : a < i.1 := by omega
    by_cases hiK : i.1 < k
    · rw [terminalTwoPlateauExcess_of_leftPlateau u a k i.1 hAi hiK]
      exact criticalExcess_mono (Nat.le_of_lt hAi)
    · have hKi : k ≤ i.1 := by omega
      rw [terminalTwoPlateauExcess_of_rightPlateau u a k i.1 hak hKi]
      exact criticalExcess_mono hKi

/-- terminal two-plateau actual target は FirstCrossing を保つ。 -/
theorem terminalTwoPlateauTarget_firstCrossing
    {p H : ℕ}
    (u : FiberPoint p H)
    (a k : ℕ)
    (hak : a < k)
    (hkp : k < p)
    (hRoofA : RoofContact u a)
    (hTerminalDepth : H = criticalHeight p + 1)
    (hFu : FirstCrossing u.word) :
    FirstCrossing
      (terminalTwoPlateauTarget u a k
        hak hkp hRoofA hTerminalDepth).word := by
  have hContract : ContractingChord p H := by
    have hPow :=
      (contracting_iff_threePow_lt_twoPow).1 hFu.terminalContracting
    simpa [ContractingChord, u.oddSteps_eq, u.twoSteps_eq] using hPow
  unfold terminalTwoPlateauTarget
  apply
    ((terminalTwoPlateauFiberShape
      u a k hak hkp hRoofA hTerminalDepth).firstCrossing_toFiberPoint_iff
        hContract).2
  rw [terminalTwoPlateauFiberShape_shape]
  exact terminalTwoPlateauShape_isCriticalSubshape
    u a k hak hkp hRoofA hFu

/-- terminal adjacent cut の actual realization packet。 -/
structure RealizedTerminalCutTransfer
    {p H : ℕ}
    (u v : FiberPoint p H)
    (a r s k : ℕ) : Prop where
  leftSource : RecordBlock u a r
  rightSource : RecordBlock u (a + r) s
  outerTerminal : (a + r) + s = p
  replacement : BlockReplacement u v a p
  newCutInside : a < k ∧ k < p
  newCutRoof : RoofContact v k

namespace RealizedTerminalCutTransfer

/-- target anchor は replacement により source roof のまま。 -/
theorem targetAnchorRoof
    {p H a r s k : ℕ}
    {u v : FiberPoint p H}
    (R : RealizedTerminalCutTransfer u v a r s k) :
    RoofContact v a := by
  have hEq := R.replacement.height_start
  unfold RoofContact
  rw [← hEq]
  exact R.leftSource.start_roof

end RealizedTerminalCutTransfer

/--
terminal actual merge の公開 result predicate。
source `[r,s]` が target `[r+s]` に exact に merge することまで保持する。
-/
def TerminalAdjacentActualMerge
    (P : Word.ContractingExponentPair)
    (u : FiberPoint P.oddCount P.twoDepth)
    (a r s : ℕ) : Prop :=
  ∃ v : FiberPoint P.oddCount P.twoDepth,
    ∃ k : ℕ,
      RealizedTerminalCutTransfer u v a r s k ∧
      FirstCrossing v.word ∧
      criticalCarry (k - a) (P.oddCount - k) = 0 ∧
      criticalCarry a (k - a) = 0 ∧
      criticalCarry k (P.oddCount - k) = 0 ∧
      twoSteps (blockWord v a (k - a)) =
        criticalHeight (k - a) ∧
      twoSteps (blockWord v k (P.oddCount - k)) =
        criticalHeight (P.oddCount - k) + 1 ∧
      RecordBlock v a (r + s) ∧
      ∃ Du : RecordDecomposition u a,
        ∃ Dv : RecordDecomposition v a,
          Du.lengths = [r, s] ∧
          Dv.lengths = [r + s] ∧
          Du.lengths ≠ Dv.lengths

/--
terminal two-plateau target には anchor `a` から見た proper admissible contact が存在しない。
従って P19 terminal absorption が発動する。
-/
theorem terminalTwoPlateauTarget_no_admissible
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (hFu : FirstCrossing u.word)
    {a r s x k : ℕ}
    (T : AdjacentTerminalRecordPair P u a r s)
    (D : DefectSplit (r + s) x)
    (hak : a < k)
    (hkp : k < P.oddCount)
    (hk : k = a + x)
    (hTerminalDepth : P.twoDepth = criticalHeight P.oddCount + 1) :
    ¬ ∃ m : ℕ,
      AdmissibleRecordContact
        (terminalTwoPlateauTarget
          u a k hak hkp T.anchorRoof hTerminalDepth)
        a m := by
  intro hExists
  rcases hExists with ⟨m, hAd⟩
  let v : FiberPoint P.oddCount P.twoDepth :=
    terminalTwoPlateauTarget
      u a k hak hkp T.anchorRoof hTerminalDepth
  change AdmissibleRecordContact v a m at hAd
  have hmA : a < m := hAd.1
  have hmP : m < P.oddCount := hAd.2.1
  have hRoofM : RoofContact v m := hAd.2.2.2.1
  have hCarryM : criticalCarry a (m - a) = 1 := hAd.2.2.2.2
  have hSides :=
    T.defectSideCarries_zero_of_primitiveReduced
      P hPrimitive hReduced u hFu D
  have hAXZero : criticalCarry a x = 0 := hSides.1
  have hHeight :
      v.height m = m + terminalTwoPlateauExcess u a k m := by
    dsimp [v]
    exact terminalTwoPlateauTarget_height
      u a k hak hkp T.anchorRoof hTerminalDepth hmP
  have hRoofEq := hRoofM
  unfold RoofContact at hRoofEq
  have hAM : a + (m - a) = m :=
    Nat.add_sub_of_le (Nat.le_of_lt hmA)
  by_cases hmK : m < k
  · have hEx : terminalTwoPlateauExcess u a k m = criticalExcess a :=
      terminalTwoPlateauExcess_of_leftPlateau u a k m hmA hmK
    rw [hEx] at hHeight
    have hQEq : criticalExcess m = criticalExcess a := by
      unfold criticalExcess
      rw [hHeight] at hRoofEq
      have hmBase := index_le_criticalHeight m
      simp [criticalExcess] at hRoofEq
      omega
    have hQAdd := criticalExcess_add_eq a (m - a)
    rw [hCarryM, hAM] at hQAdd
    omega
  · have hKm : k ≤ m := by omega
    have hEx : terminalTwoPlateauExcess u a k m = criticalExcess k :=
      terminalTwoPlateauExcess_of_rightPlateau u a k m hak hKm
    rw [hEx] at hHeight
    have hQEq : criticalExcess m = criticalExcess k := by
      unfold criticalExcess
      rw [hHeight] at hRoofEq
      have hmBase := index_le_criticalHeight m
      have hmEx : criticalHeight m - m = criticalExcess k := by
        omega
      simpa [criticalExcess] using hmEx
    have hQK := criticalExcess_add_eq a x
    rw [hAXZero] at hQK
    simp only [Nat.add_zero] at hQK
    rw [← hk] at hQK
    have hKM : x ≤ m - a := by
      rw [hk] at hKm
      omega
    have hQMono : criticalExcess x ≤ criticalExcess (m - a) :=
      criticalExcess_mono hKM
    have hQM := criticalExcess_add_eq a (m - a)
    rw [hCarryM, hAM] at hQM
    omega

/--
## 主定理 1: Terminal Flexible Pair Merge

terminal adjacent pair と defect split から actual terminal two-plateau target を構成し、
最後の二 RecordBlocks `[r,s]` を一つの terminal RecordBlock `[r+s]` に merge する。
-/
theorem exists_terminalFlexiblePairMerge
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (hFu : FirstCrossing u.word)
    {a r s x : ℕ}
    (T : AdjacentTerminalRecordPair P u a r s)
    (D : DefectSplit (r + s) x) :
    TerminalAdjacentActualMerge P u a r s := by
  classical
  let k : ℕ := a + x
  have hak : a < k := by
    dsimp [k]
    exact Nat.lt_add_of_pos_right D.1
  have hkp : k < P.oddCount := by
    dsimp [k]
    rw [← T.anchor_add_outerLength_eq_terminal]
    exact Nat.add_lt_add_left D.2.1 a
  have hTerminalDepth :
      P.twoDepth = criticalHeight P.oddCount + 1 :=
    twoDepth_eq_criticalHeight_add_one_of_primitiveReduced
      P hPrimitive hReduced u hFu (by omega)
  have hRoofA : RoofContact u a := T.anchorRoof
  let v : FiberPoint P.oddCount P.twoDepth :=
    terminalTwoPlateauTarget
      u a k hak hkp hRoofA hTerminalDepth
  have hRep : BlockReplacement u v a P.oddCount := by
    dsimp [v]
    exact terminalTwoPlateauTarget_blockReplacement
      u a k hak hkp hRoofA hTerminalDepth
  have hRoofK : RoofContact v k := by
    dsimp [v]
    exact terminalTwoPlateauTarget_roof_cut
      u a k hak hkp hRoofA hTerminalDepth
  have hFv : FirstCrossing v.word := by
    dsimp [v]
    exact terminalTwoPlateauTarget_firstCrossing
      u a k hak hkp hRoofA hTerminalDepth hFu
  have hR : RealizedTerminalCutTransfer u v a r s k := {
    leftSource := T.leftSource
    rightSource := T.rightSource
    outerTerminal := T.outerTerminal
    replacement := hRep
    newCutInside := ⟨hak, hkp⟩
    newCutRoof := hRoofK
  }
  have hSides :=
    T.defectSideCarries_zero_of_primitiveReduced
      P hPrimitive hReduced u hFu D
  have hAXZero : criticalCarry a x = 0 := hSides.1
  have hRightZero0 :
      criticalCarry (a + x) ((r + s) - x) = 0 := hSides.2
  have hKA : k - a = x := by
    dsimp [k]
    exact Nat.add_sub_self_left a x
  have hIndex : a + (r + s) = P.oddCount :=
    T.anchor_add_outerLength_eq_terminal
  have hPK : P.oddCount - k = (r + s) - x := by
    dsimp [k]
    rw [← hIndex]
    omega
  have hLocal : criticalCarry (k - a) (P.oddCount - k) = 0 := by
    rw [hKA, hPK]
    exact D.2.2
  have hLeftZero : criticalCarry a (k - a) = 0 := by
    rw [hKA]
    exact hAXZero
  have hRightZero : criticalCarry k (P.oddCount - k) = 0 := by
    dsimp [k]
    rw [hPK]
    exact hRightZero0
  have hTargetAnchorRoof : RoofContact v a := hR.targetAnchorRoof
  have hLeftDepth :
      twoSteps (blockWord v a (k - a)) =
        criticalHeight (k - a) := by
    have hHeight := height_add_eq_add_blockDepth v a (k - a)
    have hAK : a + (k - a) = k :=
      Nat.add_sub_of_le (Nat.le_of_lt hak)
    have hCrit := criticalHeight_add_eq a (k - a)
    unfold RoofContact at hTargetAnchorRoof hRoofK
    rw [hAK, hTargetAnchorRoof, hRoofK] at hHeight
    rw [hAK, hLeftZero] at hCrit
    simp only [Nat.add_zero] at hCrit
    omega
  have hRightDepth :
      twoSteps (blockWord v k (P.oddCount - k)) =
        criticalHeight (P.oddCount - k) + 1 := by
    have hHeight := height_add_eq_add_blockDepth v k (P.oddCount - k)
    have hKP : k + (P.oddCount - k) = P.oddCount :=
      Nat.add_sub_of_le (Nat.le_of_lt hkp)
    have hCrit := criticalHeight_add_eq k (P.oddCount - k)
    unfold RoofContact at hRoofK
    rw [hKP, v.height_terminal, hRoofK] at hHeight
    rw [hKP, hRightZero] at hCrit
    simp only [Nat.add_zero] at hCrit
    omega
  have hNo : ¬ ∃ m : ℕ, AdmissibleRecordContact v a m := by
    dsimp [v]
    exact terminalTwoPlateauTarget_no_admissible
      P hPrimitive hReduced u hFu T D
      hak hkp (by rfl) hTerminalDepth
  have hAnchorLt : a < P.oddCount := T.anchor_lt_terminal
  have Bmerge0 :
      RecordBlock v a (P.oddCount - a) :=
    terminalRecordBlock_of_no_admissible
      P hPrimitive hReduced v hFv
      T.anchor_pos hAnchorLt hTargetAnchorRoof hNo
  have hOuterLen : r + s = P.oddCount - a :=
    T.outerLength_eq_terminal_sub_anchor
  have Bmerge : RecordBlock v a (r + s) := by
    rw [hOuterLen]
    exact Bmerge0
  let Du : RecordDecomposition u a := {
    lengths := [r, s]
    chain :=
      RecordChain.cons T.leftSource T.leftInterior
        (RecordChain.last T.rightSource T.outerTerminal)
    whole_firstCrossing := hFu
  }
  let Dv : RecordDecomposition v a := {
    lengths := [r + s]
    chain := RecordChain.last Bmerge hIndex
    whole_firstCrossing := hFv
  }
  have hDu : Du.lengths = [r, s] := rfl
  have hDv : Dv.lengths = [r + s] := rfl
  have hNe : Du.lengths ≠ Dv.lengths := by
    rw [hDu, hDv]
    simp
  exact
    ⟨v, k, hR, hFv, hLocal, hLeftZero, hRightZero,
      hLeftDepth, hRightDepth, Bmerge,
      Du, Dv, hDu, hDv, hNe⟩

/--
`p>3` の canonical phase 領域では P25 が defect split を自動供給するので、
terminal actual merge も自動的に存在する。
-/
theorem exists_automaticTerminalAdjacentPairMerge
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (hFu : FirstCrossing u.word)
    {a r s : ℕ}
    (T : AdjacentTerminalRecordPair P u a r s)
    (hA : CriticalPhaseAtMostOne a)
    (hpGt : 3 < P.oddCount) :
    TerminalAdjacentActualMerge P u a r s := by
  obtain ⟨x, D⟩ :=
    T.exists_defectSplit_of_phaseAtMostOne_of_gt_three
      P hPrimitive hReduced u hFu hA hpGt
  exact exists_terminalFlexiblePairMerge
    P hPrimitive hReduced u hFu T D

/-- P24 interior branch の result predicate。 -/
def InteriorAdjacentActualFlexibility
    (P : Word.ContractingExponentPair)
    (u : FiberPoint P.oddCount P.twoDepth)
    (a r s : ℕ) : Prop :=
  ∃ v : FiberPoint P.oddCount P.twoDepth,
    ∃ k : ℕ,
      RealizedAdjacentCutTransfer u v a r s k ∧
      FirstCrossing v.word ∧
      criticalCarry
          (k - a)
          (((a + r) + s) - k) = 0 ∧
      ActualOneBitDefectAtCut v a ((a + r) + s) k ∧
      ∃ Du : RecordDecomposition u a,
        ∃ Dv : RecordDecomposition v a,
          Du.lengths ≠ Dv.lengths

/-- P24 automatic interior theorem を result predicate に包装する。 -/
theorem interiorAdjacentActualFlexibility_of_phaseAtMostOne
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (hFu : FirstCrossing u.word)
    {a r s : ℕ}
    (A : AdjacentInteriorRecordPair P u a r s)
    (hA : CriticalPhaseAtMostOne a) :
    InteriorAdjacentActualFlexibility P u a r s := by
  exact exists_automaticInteriorAdjacentPairPerturbation
    P hPrimitive hReduced u hFu A hA

/--
## 主定理 2: Canonical Adjacent-Pair Flexibility

`p>3` の primitive + StripReduced FirstCrossing fiber で、anchor phase が cut 1 以下にある
任意の genuine adjacent pair は actual fixed-chord deformation を持つ。

* outer endpoint が interior なら P24/P23 により canonical skeleton が変化する。
* outer endpoint が terminal なら本ファイルにより `[r,s] -> [r+s]` の exact merge が起こる。
-/
theorem canonicalAdjacentPairFlexibility_of_phaseAtMostOne
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (hFu : FirstCrossing u.word)
    {a r s : ℕ}
    (hA : CriticalPhaseAtMostOne a)
    (hpGt : 3 < P.oddCount)
    (hPair :
      AdjacentInteriorRecordPair P u a r s ∨
        AdjacentTerminalRecordPair P u a r s) :
    InteriorAdjacentActualFlexibility P u a r s ∨
      TerminalAdjacentActualMerge P u a r s := by
  rcases hPair with hInterior | hTerminal
  · exact Or.inl
      (interiorAdjacentActualFlexibility_of_phaseAtMostOne
        P hPrimitive hReduced u hFu hInterior hA)
  · exact Or.inr
      (exists_automaticTerminalAdjacentPairMerge
        P hPrimitive hReduced u hFu hTerminal hA hpGt)

end RecordFerrers
end Collatz2
