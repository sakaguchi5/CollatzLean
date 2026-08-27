import CollatzLean.Collatz2.RecordFerrers.Perturbation.P22DefectSplitBestLower
import CollatzLean.Collatz2.RecordFerrers.Lattice.FirstCrossingLattice

/-!
# Record–Ferrers 摂動理論 23: flexible adjacent pair の actual perturbation

P22 の flexible branch

  DefectSplit (r+s) x

を、P21 が要求する actual fixed-chord deformation へ実現する。

source に genuine adjacent interior RecordBlocks

  a -- r -- (a+r) -- s -- c

があり、`x` が `r+s` の defect split なら

  k := a + x

を新しい middle cut とする。target Ferrers excess profile は outer interval `(a,c)` の中だけ
二段の plateau

  criticalExcess a
  criticalExcess k

へ置き換える。critical excess 自体が nondecreasing なのでこの profile は Ferrers shape であり、
`c` が source roof であることから fixed rectangle 内にも収まる。
さらに各 plateau は critical roof 以下なので target は FirstCrossing のまま。

この target は source と `(a,c)` の外で完全に一致するため actual `BlockReplacement` になり、
`k` は target roof contact になる。従って P21 の `RealizedAdjacentCutTransfer` が得られ、
P22 の local carry zero は actual one-bit depth defect へ戻る。

最後に canonical resegmentation を比較する。defect split は source の old middle length `r` とは
一致できない。`x < r` で left carry が 1 なら、`k` 以前の first admissible contact から
`r` より短い genuine target RecordBlock が得られる。それ以外では old middle endpoint
`a+r` 自体を target roof から strict に落とせる。どちらの場合も target の first
RecordBlock length は `r` ではない。

P20 の source/target decomposition existence と canonicality を合わせ、canonical length skeleton が
実際に変化するところまで閉じる。
-/

namespace Collatz2
namespace RecordFerrers

open Word

/--
source の genuine adjacent interior RecordBlock pair。
anchor を positive として保持し、P20 の decomposition existence へ直接接続できる形にする。
-/
structure AdjacentInteriorRecordPair
    (P : Word.ContractingExponentPair)
    (u : FiberPoint P.oddCount P.twoDepth)
    (a r s : ℕ) : Prop where
  anchor_pos : 0 < a
  leftSource : RecordBlock u a r
  rightSource : RecordBlock u (a + r) s
  outerInterior : (a + r) + s < P.oddCount

namespace AdjacentInteriorRecordPair

/-- 左 source block も interior。 -/
theorem leftInterior
    {P : Word.ContractingExponentPair}
    {u : FiberPoint P.oddCount P.twoDepth}
    {a r s : ℕ}
    (A : AdjacentInteriorRecordPair P u a r s) :
    a + r < P.oddCount := by
  have hle : a + r ≤ (a + r) + s := Nat.le_add_right _ _
  exact lt_of_le_of_lt hle A.outerInterior

/-- anchor は proper。 -/
theorem anchor_lt_terminal
    {P : Word.ContractingExponentPair}
    {u : FiberPoint P.oddCount P.twoDepth}
    {a r s : ℕ}
    (A : AdjacentInteriorRecordPair P u a r s) :
    a < P.oddCount := by
  have hLen := A.leftSource.length_pos
  have hLeft := A.leftInterior
  omega

/-- source anchor は roof contact。 -/
theorem anchorRoof
    {P : Word.ContractingExponentPair}
    {u : FiberPoint P.oddCount P.twoDepth}
    {a r s : ℕ}
    (A : AdjacentInteriorRecordPair P u a r s) :
    RoofContact u a := by
  unfold RoofContact
  exact A.leftSource.start_roof

/-- source outer endpoint `c=(a+r)+s` は interior roof。 -/
theorem outerRoof
    {P : Word.ContractingExponentPair}
    {u : FiberPoint P.oddCount P.twoDepth}
    {a r s : ℕ}
    (A : AdjacentInteriorRecordPair P u a r s) :
    RoofContact u ((a + r) + s) := by
  unfold RoofContact
  exact A.rightSource.next_roof_if_interior A.outerInterior

/-- source の old middle carry `criticalCarry a r` は 1。 -/
theorem anchorLeftCarry_one
    {P : Word.ContractingExponentPair}
    {u : FiberPoint P.oddCount P.twoDepth}
    {a r s : ℕ}
    (A : AdjacentInteriorRecordPair P u a r s) :
    criticalCarry a r = 1 :=
  A.leftSource.criticalCarry_eq_one_of_interior A.leftInterior

/--
source の adjacent interior pair 自身の local carry `criticalCarry r s` も必ず 1。
critical carry cocycle と 0/1 bound だけから従う。
-/
theorem sourceLocalCarry_one
    {P : Word.ContractingExponentPair}
    {u : FiberPoint P.oddCount P.twoDepth}
    {a r s : ℕ}
    (A : AdjacentInteriorRecordPair P u a r s) :
    criticalCarry r s = 1 := by
  have hLeft : criticalCarry a r = 1 := A.anchorLeftCarry_one
  have hRight : criticalCarry (a + r) s = 1 :=
    A.rightSource.criticalCarry_eq_one_of_interior A.outerInterior
  have hCoc := criticalCarry_cocycle a r s
  rw [hLeft, hRight] at hCoc
  have hRS := criticalCarry_le_one r s
  have hOuter := criticalCarry_le_one a (r + s)
  omega

/--
defect split は source の old middle split `x=r` とは一致しない。
old split では local carry が 1 だからである。
-/
theorem defectSplit_ne_oldMiddle
    {P : Word.ContractingExponentPair}
    {u : FiberPoint P.oddCount P.twoDepth}
    {a r s x : ℕ}
    (A : AdjacentInteriorRecordPair P u a r s)
    (D : DefectSplit (r + s) x) :
    x ≠ r := by
  intro hx
  subst x
  have hLocal : criticalCarry r ((r + s) - r) = 0 := D.2.2
  have hSub : (r + s) - r = s := by omega
  rw [hSub, A.sourceLocalCarry_one] at hLocal
  omega

end AdjacentInteriorRecordPair

/-- roof contact を Ferrers excess equality として読む。 -/
theorem excessAt_eq_criticalExcess_of_roof
    {p H : ℕ}
    {u : FiberPoint p H}
    {k : ℕ}
    (hRoof : RoofContact u k) :
    u.excessAt k = criticalExcess k := by
  unfold RoofContact at hRoof
  unfold FiberPoint.excessAt criticalExcess
  rw [hRoof]

/-- critical excess の exact additive carry formula。 -/
theorem criticalExcess_add_eq
    (a b : ℕ) :
    criticalExcess (a + b) =
      criticalExcess a + criticalExcess b + criticalCarry a b := by
  have ha := index_le_criticalHeight a
  have hb := index_le_criticalHeight b
  have hab := index_le_criticalHeight (a + b)
  have hAdd := criticalHeight_add_eq a b
  unfold criticalExcess
  omega

/--
source Ferrers excess を `(a,c)` 内だけ二段 plateau に置き換えた natural-index profile。
-/
def twoPlateauExcess
    {p H : ℕ}
    (u : FiberPoint p H)
    (a k c j : ℕ) : ℕ :=
  if j ≤ a then
    u.excessAt j
  else if j < k then
    criticalExcess a
  else if j < c then
    criticalExcess k
  else
    u.excessAt j

@[simp] theorem twoPlateauExcess_of_le_anchor
    {p H : ℕ}
    (u : FiberPoint p H)
    (a k c j : ℕ)
    (hj : j ≤ a) :
    twoPlateauExcess u a k c j = u.excessAt j := by
  simp [twoPlateauExcess, hj]

@[simp] theorem twoPlateauExcess_of_leftPlateau
    {p H : ℕ}
    (u : FiberPoint p H)
    (a k c j : ℕ)
    (haj : a < j)
    (hjk : j < k) :
    twoPlateauExcess u a k c j = criticalExcess a := by
  simp [twoPlateauExcess, not_le.mpr haj, hjk]

@[simp] theorem twoPlateauExcess_of_rightPlateau
    {p H : ℕ}
    (u : FiberPoint p H)
    (a k c j : ℕ)
    (hak : a < k)
    (hkj : k ≤ j)
    (hjc : j < c) :
    twoPlateauExcess u a k c j = criticalExcess k := by
  have haj : a < j := lt_of_lt_of_le hak hkj
  simp [twoPlateauExcess, not_le.mpr haj,
    not_lt.mpr hkj, hjc]

@[simp] theorem twoPlateauExcess_of_outer_right
    {p H : ℕ}
    (u : FiberPoint p H)
    (a k c j : ℕ)
    (hak : a < k)
    (hkc : k < c)
    (hcj : c ≤ j) :
    twoPlateauExcess u a k c j = u.excessAt j := by
  have haj : a < j := by omega
  have hkj : k ≤ j := by omega
  simp [twoPlateauExcess, not_le.mpr haj,
    not_lt.mpr hkj, not_lt.mpr hcj]

/--
二段 plateau profile は nondecreasing。
両 outer endpoints が source roof であることだけを使う。
-/
theorem twoPlateauExcess_mono
    {p H : ℕ}
    (u : FiberPoint p H)
    {a k c i j : ℕ}
    (hak : a < k)
    (hkc : k < c)
    (hcp : c < p)
    (hRoofA : RoofContact u a)
    (hRoofC : RoofContact u c)
    (hij : i ≤ j)
    (hjp : j < p) :
    twoPlateauExcess u a k c i ≤
      twoPlateauExcess u a k c j := by
  have hap : a < p := by omega
  have hRoofAEx : u.excessAt a = criticalExcess a :=
    excessAt_eq_criticalExcess_of_roof hRoofA
  have hRoofCEx : u.excessAt c = criticalExcess c :=
    excessAt_eq_criticalExcess_of_roof hRoofC
  by_cases hjA : j ≤ a
  · have hiA : i ≤ a := le_trans hij hjA
    rw [twoPlateauExcess_of_le_anchor u a k c i hiA,
        twoPlateauExcess_of_le_anchor u a k c j hjA]
    exact u.excess_mono hij (Nat.le_of_lt hjp)
  · have hAj : a < j := by omega
    by_cases hiA : i ≤ a
    · rw [twoPlateauExcess_of_le_anchor u a k c i hiA]
      by_cases hjK : j < k
      · rw [twoPlateauExcess_of_leftPlateau u a k c j hAj hjK]
        have hMono := u.excess_mono hiA (Nat.le_of_lt hap)
        rw [hRoofAEx] at hMono
        exact hMono
      · have hKj : k ≤ j := by omega
        by_cases hjC : j < c
        · rw [twoPlateauExcess_of_rightPlateau
              u a k c j hak hKj hjC]
          have hMono := u.excess_mono hiA (Nat.le_of_lt hap)
          rw [hRoofAEx] at hMono
          exact hMono.trans
            (criticalExcess_mono (Nat.le_of_lt hak))
        · have hCj : c ≤ j := by omega
          rw [twoPlateauExcess_of_outer_right
              u a k c j hak hkc hCj]
          exact u.excess_mono hij (Nat.le_of_lt hjp)
    · have hAi : a < i := by omega
      by_cases hiK : i < k
      · rw [twoPlateauExcess_of_leftPlateau u a k c i hAi hiK]
        by_cases hjK : j < k
        · rw [twoPlateauExcess_of_leftPlateau u a k c j hAj hjK]
        · have hKj : k ≤ j := by omega
          by_cases hjC : j < c
          · rw [twoPlateauExcess_of_rightPlateau
                u a k c j hak hKj hjC]
            exact criticalExcess_mono (Nat.le_of_lt hak)
          · have hCj : c ≤ j := by omega
            rw [twoPlateauExcess_of_outer_right
                u a k c j hak hkc hCj]
            have hMono :=
              u.excess_mono (by omega : a ≤ j) (Nat.le_of_lt hjp)
            rw [hRoofAEx] at hMono
            exact hMono
      · have hKi : k ≤ i := by omega
        by_cases hiC : i < c
        · rw [twoPlateauExcess_of_rightPlateau
              u a k c i hak hKi hiC]
          by_cases hjC : j < c
          · have hKj : k ≤ j := le_trans hKi hij
            rw [twoPlateauExcess_of_rightPlateau
                u a k c j hak hKj hjC]
          · have hCj : c ≤ j := by omega
            rw [twoPlateauExcess_of_outer_right
                u a k c j hak hkc hCj]
            have hKCEx :=
              criticalExcess_mono (Nat.le_of_lt hkc)
            have hCJ :=
              u.excess_mono hCj (Nat.le_of_lt hjp)
            rw [hRoofCEx] at hCJ
            exact hKCEx.trans hCJ
        · have hCi : c ≤ i := by omega
          have hCj : c ≤ j := le_trans hCi hij
          rw [twoPlateauExcess_of_outer_right
                u a k c i hak hkc hCi,
              twoPlateauExcess_of_outer_right
                u a k c j hak hkc hCj]
          exact u.excess_mono hij (Nat.le_of_lt hjp)

/-- two-plateau natural profile を exact Ferrers shape にする。 -/
def twoPlateauShape
    {p H : ℕ}
    (u : FiberPoint p H)
    (a k c : ℕ)
    (hak : a < k)
    (hkc : k < c)
    (hcp : c < p)
    (hRoofA : RoofContact u a)
    (hRoofC : RoofContact u c) : FerrersShape p :=
  { column := fun i => twoPlateauExcess u a k c i.1
    mono := by
      intro i j hij
      have hijNat : i.1 ≤ j.1 := hij
      exact twoPlateauExcess_mono u
        hak hkc hcp hRoofA hRoofC hijNat j.isLt }

/--
two-plateau shape は source と同じ fixed rectangle `(p,H)` 内に入る。
-/
def twoPlateauFiberShape
    {p H : ℕ}
    (u : FiberPoint p H)
    (a k c : ℕ)
    (hak : a < k)
    (hkc : k < c)
    (hcp : c < p)
    (hRoofA : RoofContact u a)
    (hRoofC : RoofContact u c) : FiberShape p H := by
  have hp : 0 < p := by omega
  have hpH : p ≤ H := by
    have h := FiberPoint.oddSteps_le_twoSteps_of_valid u.valid
    rw [u.oddSteps_eq, u.twoSteps_eq] at h
    exact h
  have hRoofCEx : u.excessAt c = criticalExcess c :=
    excessAt_eq_criticalExcess_of_roof hRoofC
  have hCBound : criticalExcess c ≤ H - p := by
    rw [← hRoofCEx]
    exact u.excess_le_rectangleHeight (Nat.le_of_lt hcp)
  refine {
    shape := twoPlateauShape u a k c hak hkc hcp hRoofA hRoofC
    p_pos := hp
    p_le_H := hpH
    first_zero := ?_
    bounded := ?_
  }
  · change twoPlateauExcess u a k c 0 = 0
    rw [twoPlateauExcess_of_le_anchor u a k c 0 (Nat.zero_le _)]
    exact u.excessAt_zero
  · intro i
    change twoPlateauExcess u a k c i.1 ≤ H - p
    by_cases hiA : i.1 ≤ a
    · rw [twoPlateauExcess_of_le_anchor u a k c i.1 hiA]
      exact u.excess_le_rectangleHeight (Nat.le_of_lt i.isLt)
    · have hAi : a < i.1 := by omega
      by_cases hiK : i.1 < k
      · rw [twoPlateauExcess_of_leftPlateau
            u a k c i.1 hAi hiK]
        exact
          (criticalExcess_mono
            (Nat.le_of_lt (lt_trans hak hkc))).trans hCBound
      · have hKi : k ≤ i.1 := by omega
        by_cases hiC : i.1 < c
        · rw [twoPlateauExcess_of_rightPlateau
              u a k c i.1 hak hKi hiC]
          exact
            (criticalExcess_mono (Nat.le_of_lt hkc)).trans hCBound
        · have hCi : c ≤ i.1 := by omega
          rw [twoPlateauExcess_of_outer_right
              u a k c i.1 hak hkc hCi]
          exact u.excess_le_rectangleHeight (Nat.le_of_lt i.isLt)

@[simp] theorem twoPlateauFiberShape_shape
    {p H : ℕ}
    (u : FiberPoint p H)
    (a k c : ℕ)
    (hak : a < k)
    (hkc : k < c)
    (hcp : c < p)
    (hRoofA : RoofContact u a)
    (hRoofC : RoofContact u c) :
    (twoPlateauFiberShape u a k c
      hak hkc hcp hRoofA hRoofC).shape =
      twoPlateauShape u a k c
        hak hkc hcp hRoofA hRoofC := rfl

/-- exact FiberShape decoder による actual two-plateau target。 -/
def twoPlateauTarget
    {p H : ℕ}
    (u : FiberPoint p H)
    (a k c : ℕ)
    (hak : a < k)
    (hkc : k < c)
    (hcp : c < p)
    (hRoofA : RoofContact u a)
    (hRoofC : RoofContact u c) : FiberPoint p H :=
  (twoPlateauFiberShape u a k c
    hak hkc hcp hRoofA hRoofC).toFiberPoint

/-- target proper height の closed form。 -/
theorem twoPlateauTarget_height
    {p H : ℕ}
    (u : FiberPoint p H)
    (a k c : ℕ)
    (hak : a < k)
    (hkc : k < c)
    (hcp : c < p)
    (hRoofA : RoofContact u a)
    (hRoofC : RoofContact u c)
    {j : ℕ}
    (hjp : j < p) :
    (twoPlateauTarget u a k c
      hak hkc hcp hRoofA hRoofC).height j =
      j + twoPlateauExcess u a k c j := by
  have hPrefix :=
    (twoPlateauFiberShape u a k c
      hak hkc hcp hRoofA hRoofC).prefixTwoDepth_toWord hjp
  have hAt :
      (twoPlateauFiberShape u a k c
        hak hkc hcp hRoofA hRoofC).shape.atNat j =
        twoPlateauExcess u a k c j := by
    rw [twoPlateauFiberShape_shape]
    simp [twoPlateauShape, FerrersShape.atNat, hjp]
  rw [hAt] at hPrefix
  change
    prefixTwoDepth
        (twoPlateauFiberShape u a k c
          hak hkc hcp hRoofA hRoofC).toWord j =
      j + twoPlateauExcess u a k c j
  exact hPrefix

/-- 新しい middle cut `k` は target roof に exact に接触する。 -/
theorem twoPlateauTarget_roof_cut
    {p H : ℕ}
    (u : FiberPoint p H)
    (a k c : ℕ)
    (hak : a < k)
    (hkc : k < c)
    (hcp : c < p)
    (hRoofA : RoofContact u a)
    (hRoofC : RoofContact u c) :
    RoofContact
      (twoPlateauTarget u a k c
        hak hkc hcp hRoofA hRoofC) k := by
  have hkp : k < p := lt_trans hkc hcp
  have hHeight :=
    twoPlateauTarget_height u a k c
      hak hkc hcp hRoofA hRoofC hkp
  have hEx :
      twoPlateauExcess u a k c k = criticalExcess k := by
    exact twoPlateauExcess_of_rightPlateau
      u a k c k hak le_rfl hkc
  rw [hEx] at hHeight
  unfold RoofContact
  rw [hHeight]
  unfold criticalExcess
  have hBase := index_le_criticalHeight k
  omega

/-- two-plateau target は outer interval の外で source height と完全に一致する。 -/
theorem twoPlateauTarget_height_eq_source_of_outside
    {p H : ℕ}
    (u : FiberPoint p H)
    (a k c : ℕ)
    (hak : a < k)
    (hkc : k < c)
    (hcp : c < p)
    (hRoofA : RoofContact u a)
    (hRoofC : RoofContact u c)
    {j : ℕ}
    (hjp : j ≤ p)
    (hOutside : j ≤ a ∨ c ≤ j) :
    (twoPlateauTarget u a k c
      hak hkc hcp hRoofA hRoofC).height j =
      u.height j := by
  by_cases hjLt : j < p
  · have hHeight :=
      twoPlateauTarget_height u a k c
        hak hkc hcp hRoofA hRoofC hjLt
    have hEx :
        twoPlateauExcess u a k c j = u.excessAt j := by
      rcases hOutside with hJA | hCJ
      · exact twoPlateauExcess_of_le_anchor u a k c j hJA
      · exact twoPlateauExcess_of_outer_right
          u a k c j hak hkc hCJ
    rw [hEx] at hHeight
    have hSource :=
      u.height_eq_index_add_excess (Nat.le_of_lt hjLt)
    exact hHeight.trans hSource.symm
  · have hjEq : j = p := by omega
    subst j
    simp

/-- actual compact-support BlockReplacement。 -/
theorem twoPlateauTarget_blockReplacement
    {p H : ℕ}
    (u : FiberPoint p H)
    (a k c : ℕ)
    (hak : a < k)
    (hkc : k < c)
    (hcp : c < p)
    (hRoofA : RoofContact u a)
    (hRoofC : RoofContact u c) :
    BlockReplacement u
      (twoPlateauTarget u a k c
        hak hkc hcp hRoofA hRoofC)
      a c := by
  refine {
    start_lt_stop := lt_trans hak hkc
    stop_le_terminal := Nat.le_of_lt hcp
    outside := ?_
  }
  intro j hjp hOutside
  have hEq :=
    twoPlateauTarget_height_eq_source_of_outside
      u a k c hak hkc hcp hRoofA hRoofC hjp hOutside
  unfold profileDisplacement
  rw [hEq]
  ring

/-- two-plateau Ferrers shape は critical roof の下側にある。 -/
theorem twoPlateauShape_isCriticalSubshape
    {p H : ℕ}
    (u : FiberPoint p H)
    (a k c : ℕ)
    (hak : a < k)
    (hkc : k < c)
    (hcp : c < p)
    (hRoofA : RoofContact u a)
    (hRoofC : RoofContact u c)
    (hFu : FirstCrossing u.word) :
    IsCriticalSubshape
      (twoPlateauShape u a k c
        hak hkc hcp hRoofA hRoofC) := by
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
  change twoPlateauExcess u a k c i.1 ≤ criticalExcess i.1
  by_cases hiA : i.1 ≤ a
  · rw [twoPlateauExcess_of_le_anchor u a k c i.1 hiA]
    exact hSourceI
  · have hAi : a < i.1 := by omega
    by_cases hiK : i.1 < k
    · rw [twoPlateauExcess_of_leftPlateau
          u a k c i.1 hAi hiK]
      exact criticalExcess_mono (Nat.le_of_lt hAi)
    · have hKi : k ≤ i.1 := by omega
      by_cases hiC : i.1 < c
      · rw [twoPlateauExcess_of_rightPlateau
            u a k c i.1 hak hKi hiC]
        exact criticalExcess_mono hKi
      · have hCi : c ≤ i.1 := by omega
        rw [twoPlateauExcess_of_outer_right
            u a k c i.1 hak hkc hCi]
        exact hSourceI

/-- two-plateau actual target は FirstCrossing を保つ。 -/
theorem twoPlateauTarget_firstCrossing
    {p H : ℕ}
    (u : FiberPoint p H)
    (a k c : ℕ)
    (hak : a < k)
    (hkc : k < c)
    (hcp : c < p)
    (hRoofA : RoofContact u a)
    (hRoofC : RoofContact u c)
    (hFu : FirstCrossing u.word) :
    FirstCrossing
      (twoPlateauTarget u a k c
        hak hkc hcp hRoofA hRoofC).word := by
  have hContract : ContractingChord p H := by
    have hPow :=
      (contracting_iff_threePow_lt_twoPow).1 hFu.terminalContracting
    simpa [ContractingChord, u.oddSteps_eq, u.twoSteps_eq] using hPow
  unfold twoPlateauTarget
  apply
    ((twoPlateauFiberShape u a k c
      hak hkc hcp hRoofA hRoofC).firstCrossing_toFiberPoint_iff
        hContract).2
  rw [twoPlateauFiberShape_shape]
  exact twoPlateauShape_isCriticalSubshape
    u a k c hak hkc hcp hRoofA hRoofC hFu

/--
actual one-bit defect の depth-level statement を独立 predicate にする。
P21 の `defect_actualDepthDichotomy` と同じ内容。
-/
def ActualOneBitDefectAtCut
    {p H : ℕ}
    (v : FiberPoint p H)
    (a c k : ℕ) : Prop :=
  (twoSteps (blockWord v a (k - a)) =
      criticalHeight (k - a) ∧
    twoSteps (blockWord v k (c - k)) =
      criticalHeight (c - k) + 1) ∨
  (twoSteps (blockWord v a (k - a)) =
      criticalHeight (k - a) + 1 ∧
    twoSteps (blockWord v k (c - k)) =
      criticalHeight (c - k))

/-- P21 local carry defect を上の actual predicate へ包装する。 -/
theorem RealizedAdjacentCutTransfer.actualOneBitDefectAtCut_of_localCarry_zero
    {p H a r s k : ℕ}
    {u v : FiberPoint p H}
    (R : RealizedAdjacentCutTransfer u v a r s k)
    (hLocal :
      criticalCarry
        (k - a)
        (((a + r) + s) - k) = 0) :
    ActualOneBitDefectAtCut v a ((a + r) + s) k := by
  simpa [ActualOneBitDefectAtCut] using
    R.defect_actualDepthDichotomy hLocal

namespace RecordChain

/-- nonempty record chain の first block を取り出す。 -/
theorem exists_head_block
    {p H : ℕ}
    {v : FiberPoint p H}
    {anchor : ℕ}
    {lengths : List ℕ}
    (C : RecordChain v anchor lengths) :
    ∃ len rest,
      lengths = len :: rest ∧
      RecordBlock v anchor len := by
  cases C with
  | last B hTerminal =>
      exact ⟨_, [], rfl, B⟩
  | cons B hInterior T =>
      exact ⟨_, _, rfl, B⟩

end RecordChain

namespace DefectSplit

/--
defect split `x` を anchor `a` だけ平行移動すると、
新しい cut `a+x` は adjacent pair の outer interval の真内部にある。
-/
theorem shiftedCut_inside
    {a r s x : ℕ}
    (D : DefectSplit (r + s) x) :
    a < a + x ∧
      a + x < (a + r) + s := by
  constructor
  · exact Nat.lt_add_of_pos_right D.1
  · calc
      a + x < a + (r + s) :=
        Nat.add_lt_add_left D.2.1 a
      _ = (a + r) + s :=
        (Nat.add_assoc a r s).symm

end DefectSplit


/--
同じ anchor から見て、

* `x ≤ r`
* `a -> x` の carry は 0
* `a -> r` の carry は 1

なら、`a+x` の critical excess は old middle `a+r` より strict に小さい。
-/
theorem criticalExcess_add_lt_add_of_carry_zero_one
    {a x r : ℕ}
    (hxr : x ≤ r)
    (hX : criticalCarry a x = 0)
    (hR : criticalCarry a r = 1) :
    criticalExcess (a + x) <
      criticalExcess (a + r) := by
  have hXEq := criticalExcess_add_eq a x
  have hREq := criticalExcess_add_eq a r
  rw [hX] at hXEq
  simp only [Nat.add_zero] at hXEq
  rw [hR] at hREq
  rw [hXEq, hREq]
  have hXR :
      criticalExcess x ≤ criticalExcess r :=
    criticalExcess_mono hxr
  have hXR' :
      criticalExcess x < criticalExcess r + 1 :=
    Nat.lt_succ_of_le hXR
  calc
    criticalExcess a + criticalExcess x
        <
      criticalExcess a + (criticalExcess r + 1) :=
        Nat.add_lt_add_left hXR' _
    _ =
      criticalExcess a + criticalExcess r + 1 :=
        (Nat.add_assoc _ _ _).symm


/--
carry 1 があるなら、その block 終端では
critical excess が anchor より strict に増える。
-/
theorem criticalExcess_lt_add_of_carry_one
    {a r : ℕ}
    (hCarry : criticalCarry a r = 1) :
    criticalExcess a <
      criticalExcess (a + r) := by
  have hEq := criticalExcess_add_eq a r
  rw [hCarry] at hEq
  rw [hEq]
  calc
    criticalExcess a
        <
      criticalExcess a + (criticalExcess r + 1) :=
        Nat.lt_add_of_pos_right (Nat.zero_lt_succ _)
    _ =
      criticalExcess a + criticalExcess r + 1 :=
        (Nat.add_assoc _ _ _).symm


/--
two-plateau target のある位置で plateau excess が
critical excess より strict に小さければ、
actual target height も critical roof より strict に低い。
-/
theorem twoPlateauTarget_height_lt_criticalHeight_of_excess_lt
    {p H : ℕ}
    (u : FiberPoint p H)
    (a k c : ℕ)
    (hak : a < k)
    (hkc : k < c)
    (hcp : c < p)
    (hRoofA : RoofContact u a)
    (hRoofC : RoofContact u c)
    {j : ℕ}
    (hjp : j < p)
    (hExLt :
      twoPlateauExcess u a k c j <
        criticalExcess j) :
    (twoPlateauTarget u a k c
        hak hkc hcp hRoofA hRoofC).height j <
      criticalHeight j := by
  calc
    (twoPlateauTarget u a k c
        hak hkc hcp hRoofA hRoofC).height j
        =
      j + twoPlateauExcess u a k c j :=
        twoPlateauTarget_height
          u a k c hak hkc hcp hRoofA hRoofC hjp
    _ <
      j + criticalExcess j :=
        Nat.add_lt_add_left hExLt j
    _ =
      criticalHeight j := by
        unfold criticalExcess
        exact Nat.add_sub_of_le
          (index_le_criticalHeight j)


namespace RecordBlock

/--
block 終端が terminal より手前なのに、その actual height が
critical roof より strict に低ければ、その block は RecordBlock ではない。
-/
theorem not_of_endpoint_below_criticalHeight
    {p H a r : ℕ}
    {v : FiberPoint p H}
    (hInterior : a + r < p)
    (hBelow :
      v.height (a + r) <
        criticalHeight (a + r)) :
    ¬ RecordBlock v a r := by
  intro B
  have hRoof :=
    B.next_roof_if_interior hInterior
  exact (Nat.ne_of_lt hBelow) hRoof

end RecordBlock


namespace RecordDecomposition

/--
source decomposition の first block length が `r` で、
target には length `r` の first RecordBlock が存在できないなら、
二つの canonical length skeleton は一致しない。
-/
theorem lengths_ne_of_source_head_forbidden
    {p H a r : ℕ}
    {u v : FiberPoint p H}
    (Du : RecordDecomposition u a)
    (Dv : RecordDecomposition v a)
    (Bu0 : RecordBlock u a r)
    (hNoV : ¬ RecordBlock v a r) :
    Du.lengths ≠ Dv.lengths := by
  intro hEq
  obtain ⟨ru, restu, hDuList, Bu⟩ :=
    Du.chain.exists_head_block
  obtain ⟨rv, restv, hDvList, Bv⟩ :=
    Dv.chain.exists_head_block
  have hRu : ru = r :=
    Bu.length_unique Bu0
  have hLists :
      rv :: restv = ru :: restu := by
    calc
      rv :: restv = Dv.lengths := hDvList.symm
      _ = Du.lengths := hEq.symm
      _ = ru :: restu := hDuList
  have hRvRu : rv = ru := by
    have hHead :=
      congrArg List.head? hLists
    simpa using hHead
  have hRv : rv = r :=
    hRvRu.trans hRu
  have Br : RecordBlock v a r := by
    rw [← hRv]
    exact Bv
  exact hNoV Br

end RecordDecomposition


/--
## 主定理 2: Flexible Adjacent Pair Perturbation

primitive + StripReduced fixed chord 上で、source に genuine adjacent interior RecordBlocks があり、
outer length `r+s` に defect split `x` が存在するとする。

すると actual target `v` と new cut `k` が存在し、

* source -> target は actual `BlockReplacement`
* `k` は actual roof cut を持つ `RealizedAdjacentCutTransfer`
* target は FirstCrossing
* local carry zero は actual one-bit depth defect として実現
* source/target はともに anchor `a` から canonical RecordDecomposition を持つ
* その canonical length skeleton は異なる

が同時に成立する。
-/
theorem exists_flexibleAdjacentPairPerturbation
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (hFu : FirstCrossing u.word)
    {a r s x : ℕ}
    (A : AdjacentInteriorRecordPair P u a r s)
    (D : DefectSplit (r + s) x) :
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
            Du.lengths ≠ Dv.lengths := by
  classical
  let k := a + x
  let c := (a + r) + s
  have hkDef : k = a + x := by
    rfl
  have hcDef : c = (a + r) + s := by
    rfl
  have hCutInside :
      a < a + x ∧
        a + x < (a + r) + s :=
    DefectSplit.shiftedCut_inside D
  have hak : a < k := by
    simpa [k] using hCutInside.1
  have hkc : k < c := by
    simpa [k, c] using hCutInside.2
  have hcp : c < P.oddCount := by
    simpa [c] using A.outerInterior
  have hRoofA : RoofContact u a := A.anchorRoof
  have hRoofC : RoofContact u c := by
    simpa [c] using A.outerRoof
  let v : FiberPoint P.oddCount P.twoDepth :=
    twoPlateauTarget u a k c hak hkc hcp hRoofA hRoofC
  have hRep : BlockReplacement u v a c := by
    dsimp [v]
    exact twoPlateauTarget_blockReplacement
      u a k c hak hkc hcp hRoofA hRoofC
  have hRoofK : RoofContact v k := by
    dsimp [v]
    exact twoPlateauTarget_roof_cut
      u a k c hak hkc hcp hRoofA hRoofC
  have hFv : FirstCrossing v.word := by
    dsimp [v]
    exact twoPlateauTarget_firstCrossing
      u a k c hak hkc hcp hRoofA hRoofC hFu
  have hR : RealizedAdjacentCutTransfer u v a r s k := by
    refine {
      leftSource := A.leftSource
      rightSource := A.rightSource
      outerInterior := A.outerInterior
      replacement := ?_
      newCutInside := ⟨hak, ?_⟩
      newCutRoof := hRoofK
    }
    · simpa [c] using hRep
    · simpa [c] using hkc
  have hKA : k - a = x := by
    rw [hkDef]
    exact Nat.add_sub_self_left a x
  have hCK :
      ((a + r) + s) - k =
        (r + s) - x := by
    rw [hkDef]
    rw [Nat.add_assoc]
    exact Nat.add_sub_add_left a (r + s) x
  have hLocal :
      criticalCarry
        (k - a)
        (((a + r) + s) - k) = 0 := by
    rw [hKA, hCK]
    exact D.2.2
  have hActual :
      ActualOneBitDefectAtCut v a ((a + r) + s) k :=
    hR.actualOneBitDefectAtCut_of_localCarry_zero hLocal
  have hxNeR : x ≠ r :=
    A.defectSplit_ne_oldMiddle D
  have hSourceAnchorCarry :
      criticalCarry a r = 1 :=
    A.anchorLeftCarry_one
  have hNoTargetLeft : ¬ RecordBlock v a r := by
    rcases lt_or_gt_of_ne hxNeR with hxLtR | hrLtX
    · -- x < r
      by_cases hAXOne : criticalCarry a x = 1
      · -- 新 cut 自身が admissible。
        -- first admissible contact は k 以下なので、
        -- source length r より短い target RecordBlock が現れる。
        have hAdK :
            AdmissibleRecordContact v a k := by
          apply (hR.leftAdmissible_iff_carry_one).2
          rw [hKA]
          exact hAXOne
        have hExists :
            ∃ j : ℕ,
              AdmissibleRecordContact v a j :=
          ⟨k, hAdK⟩
        let m : ℕ := Nat.find hExists
        have hmAd :
            AdmissibleRecordContact v a m :=
          Nat.find_spec hExists
        let F :
            FirstAdmissibleRecordContact v a m :=
          { candidate := hmAd
            least := by
              intro j hj
              exact Nat.find_min' hExists hj }
        have hmLeK : m ≤ k :=
          F.least k hAdK
        have Bm :
            RecordBlock v a (m - a) :=
          F.toRecordBlock
            hPrimitive hReduced hFv
        have hLenLt : m - a < r := by
          calc
            m - a ≤ k - a :=
              Nat.sub_le_sub_right hmLeK a
            _ = x := hKA
            _ < r := hxLtR
        intro Br
        have hEq :=
          Bm.length_unique Br
        exact (Nat.ne_of_lt hLenLt) hEq
      · -- x < r だが anchor -> x carry は 0。
        -- right plateau の高さで old middle が roof より下に落ちる。
        have hAXZero :
            criticalCarry a x = 0 := by
          rcases
              criticalCarry_eq_zero_or_one a x with
            hZero | hOne
          · exact hZero
          · exact False.elim (hAXOne hOne)
        have hMidP :
            a + r < P.oddCount :=
          A.leftInterior
        have hKLeMid :
            k ≤ a + r := by
          rw [hkDef]
          exact Nat.add_le_add_left
            (Nat.le_of_lt hxLtR) a
        have hMidLtC :
            a + r < c := by
          dsimp [c]
          exact
            Nat.lt_add_of_pos_right
              A.rightSource.length_pos
        have hExMid :
            twoPlateauExcess
                u a k c (a + r) =
              criticalExcess k :=
          twoPlateauExcess_of_rightPlateau
            u a k c (a + r)
            hak hKLeMid hMidLtC
        have hQLt :
            criticalExcess k <
              criticalExcess (a + r) := by
          rw [hkDef]
          exact
            criticalExcess_add_lt_add_of_carry_zero_one
              (Nat.le_of_lt hxLtR)
              hAXZero
              hSourceAnchorCarry
        have hPlateauLt :
            twoPlateauExcess
                u a k c (a + r) <
              criticalExcess (a + r) := by
          rw [hExMid]
          exact hQLt
        have hHeightLt :
            v.height (a + r) <
              criticalHeight (a + r) := by
          dsimp [v]
          exact
            twoPlateauTarget_height_lt_criticalHeight_of_excess_lt
              u a k c
              hak hkc hcp hRoofA hRoofC
              hMidP hPlateauLt
        exact
          RecordBlock.not_of_endpoint_below_criticalHeight
            A.leftInterior hHeightLt
    · -- r < x
      -- old middle は left plateau 内部に入り、
      -- anchor excess のままなので roof より下に落ちる。
      have hMidP :
          a + r < P.oddCount :=
        A.leftInterior
      have hAMid :
          a < a + r :=
        Nat.lt_add_of_pos_right
          A.leftSource.length_pos
      have hMidLtK :
          a + r < k := by
        rw [hkDef]
        exact Nat.add_lt_add_left hrLtX a
      have hExMid :
          twoPlateauExcess
              u a k c (a + r) =
            criticalExcess a :=
        twoPlateauExcess_of_leftPlateau
          u a k c (a + r)
          hAMid hMidLtK
      have hQLt :
          criticalExcess a <
            criticalExcess (a + r) :=
        criticalExcess_lt_add_of_carry_one
          hSourceAnchorCarry
      have hPlateauLt :
          twoPlateauExcess
              u a k c (a + r) <
            criticalExcess (a + r) := by
        rw [hExMid]
        exact hQLt
      have hHeightLt :
          v.height (a + r) <
            criticalHeight (a + r) := by
        dsimp [v]
        exact
          twoPlateauTarget_height_lt_criticalHeight_of_excess_lt
            u a k c
            hak hkc hcp hRoofA hRoofC
            hMidP hPlateauLt
      exact
        RecordBlock.not_of_endpoint_below_criticalHeight
          A.leftInterior hHeightLt
  obtain ⟨Du⟩ :=
    exists_recordDecomposition_from_positive_roof_of_primitiveReduced
      P hPrimitive hReduced u hFu
      A.anchor_pos A.anchor_lt_terminal A.anchorRoof
  obtain ⟨Dv⟩ :=
    exists_recordDecomposition_from_positive_roof_of_primitiveReduced
      P hPrimitive hReduced v hFv
      A.anchor_pos A.anchor_lt_terminal hR.targetAnchorRoof
  have hLengthsNe : Du.lengths ≠ Dv.lengths := by
    intro hEq
    obtain ⟨ru, restu, hDuList, Bu⟩ := Du.chain.exists_head_block
    obtain ⟨rv, restv, hDvList, Bv⟩ := Dv.chain.exists_head_block
    have hRu : ru = r := Bu.length_unique A.leftSource
    have hLists : rv :: restv = ru :: restu := by
      calc
        rv :: restv = Dv.lengths := hDvList.symm
        _ = Du.lengths := hEq.symm
        _ = ru :: restu := hDuList
    have hRvRu : rv = ru := by
      have hHead := congrArg List.head? hLists
      simpa using hHead
    have hRv : rv = r := hRvRu.trans hRu
    have Br : RecordBlock v a r := by
      rw [← hRv]
      exact Bv
    exact hNoTargetLeft Br
  refine ⟨v, k, hR, hFv, hLocal, hActual, Du, Dv, hLengthsNe⟩

end RecordFerrers
end Collatz2
