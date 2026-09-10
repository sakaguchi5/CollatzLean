import CollatzLean.Collatz3.Experimental2.OstrowskiCanonicalCorridor
import CollatzLean.Collatz3.Bridge.Experimental2OstrowskiSturmianRecord

set_option linter.style.longLine false

/-!
# Collatz3 Bridge: canonical Ostrowski / sharp corridor / RecordFerrers

`OstrowskiCanonicalArithmetic` と `OstrowskiCanonicalCorridor` で証明した generic theory を
critical slope `log₂3` と inverse slope `log₃2` に接続する。

regular continued fraction の最初の `0/1` convergent を除いた列では、
`log₃2` の convergent `(P_n,Q_n)` は `log₂3` 側では

* shifted index 偶数: lower Farey corridor,
* shifted index 奇数: upper Farey corridor

として交互に現れる。

このファイルでは continued fraction engine 自体を再実装せず、
その出力が満たす最小 certificate `BeattyRegularOstrowskiSystem` を置く。
certificate 以降はすべて導出定理として構成し、従来必要だった
`ExactInverseCorridorChain` の外部仮定は消える。
また endpoint correction は system 固有のデータではなく、shifted index の parity だけで決まるため、
`BeattyRegularOstrowskiSystem` の外側に独立した算術関数として置く。

最終的に正整数 `N` について

`beattyInverseHeight N = Σ c_n P_n + (j mod 2)`

を得る。ここで `c_n` は canonical greedy Ostrowski digits、`j` は最小非零 digit。
従って lower endpoint (`j` 偶数) では補正 `0`、upper endpoint (`j` 奇数) では `+1`。
同じ式を admissible record cut / deterministic `initialRecordCuts` / RecordFerrers へ移す。
-/

namespace Collatz3
open Experimental2
open ExactOstrowskiCorridorSystem
namespace Bridge

/--
shifted convergent index に付随する endpoint correction。

この補正値は Ostrowski system の個別データには依存せず、
shifted index の parity bit `n % 2` だけで決まる。
偶数 index では `0`、奇数 index では `1` となる。
-/
def endpointCorrection (n : ℕ) : ℕ :=
  n % 2

/-- endpoint correction は常に `0` または `1` なので、特に `1` 以下である。 -/
theorem endpointCorrection_le_one
    (n : ℕ) :
    endpointCorrection n ≤ 1 := by
  unfold endpointCorrection
  have h := Nat.mod_lt n (by omega : 0 < 2)
  omega

/-- shifted index が偶数なら endpoint correction は `0`。 -/
theorem endpointCorrection_eq_zero
    {n : ℕ}
    (hn : n % 2 = 0) :
    endpointCorrection n = 0 := by
  simpa [endpointCorrection] using hn

/-- shifted index が奇数なら endpoint correction は `1`。 -/
theorem endpointCorrection_eq_one
    {n : ℕ}
    (hn : n % 2 = 1) :
    endpointCorrection n = 1 := by
  simpa [endpointCorrection] using hn

/--
`log₃2` の shifted regular convergent 列に必要な最小 certificate。

`conv` は同じ partial quotient で進む自然数 `(P,Q)` 再帰を保存する。
`lowerBracket` と `upperBracket` は shifted index の parity が
lower / upper Farey orientation のどちらに対応するかだけを記録する。
endpoint correction 自体は system に依存しないため、この structure には保存しない。
-/
structure BeattyRegularOstrowskiSystem where
  conv : UnitOstrowskiConvergentSystem
  lowerBracket : ∀ n, n % 2 = 0 →
    IsLowerFareyBracket (Real.logb 2 3)
      (conv.P n) (conv.Q n) (conv.P (n + 1)) (conv.Q (n + 1))
  upperBracket : ∀ n, n % 2 = 1 →
    IsUpperFareyBracket (Real.logb 2 3)
      (conv.P n) (conv.Q n) (conv.P (n + 1)) (conv.Q (n + 1))

namespace BeattyRegularOstrowskiSystem

/-- convergent system から Ostrowski weight system の部分だけを取り出す。 -/
abbrev weights (D : BeattyRegularOstrowskiSystem) : UnitOstrowskiWeightSystem :=
  D.conv.toUnitOstrowskiWeightSystem

/--
lower Farey bracket に対する Beatty inverse の鋭い端点公式。
generic な sharp theorem を用いるため `P < Pn` の仮定は不要であり、
最初の `(P,Q)=(1,1)` と次段の `P=1` が重なる境界の場合もこの定理が覆う。
-/
theorem beattyInverseHeight_currentQ_eq_currentP_of_lowerFarey_sharp
    {P Q Pn Qn : ℕ}
    (B : IsLowerFareyBracket (Real.logb 2 3) P Q Pn Qn) :
    beattyInverseHeight Q = P := by
  simpa [beattyInverseHeight] using
    (beattyIndex_isLowerMechanical_logb_two_three.inverse_currentQ_eq_currentP_of_lowerFarey_sharp
        one_le_logb_two_three B)

/-- lower Farey bracket の including-zero 版の鋭い平行移動公式も、`P < Pn` の仮定なしで成り立つ。 -/
theorem beattyInverseHeight_add_currentQ_eq_add_currentP_of_lowerFarey_sharp_including_zero_no_lt
    {P Q Pn Qn k : ℕ}
    (B : IsLowerFareyBracket (Real.logb 2 3) P Q Pn Qn)
    (hk : k < Qn) :
    beattyInverseHeight (Q + k) = P + beattyInverseHeight k := by
  have hMono : Monotone Critical.beattyIndex := by
    intro a b hab
    exact beattyIndex_mono_via_upper hab
  simpa [beattyInverseHeight] using
    (beattyIndex_isLowerMechanical_logb_two_three.inverse_add_currentQ_eq_add_currentP_of_lowerFarey_sharp_including_zero_no_lt
        one_le_logb_two_three hMono B hk)

/-- lower Farey bracket の境界で生じる一段差は、`P < Pn` の仮定なしで正確に `1` となる。 -/
theorem beattyInverseStep_currentQ_eq_one_of_lowerFarey_sharp_no_lt
    {P Q Pn Qn : ℕ}
    (B : IsLowerFareyBracket (Real.logb 2 3) P Q Pn Qn)
    (hOneLt : 1 < Qn) :
    beattyInverseHeight (Q + 1) - beattyInverseHeight Q = 1 := by
  have hMono : Monotone Critical.beattyIndex := by
    intro a b hab
    exact beattyIndex_mono_via_upper hab
  simpa [beattyInverseHeight, IsLowerMechanicalRoof.inverseStep] using
    (beattyIndex_isLowerMechanical_logb_two_three.inverseStep_currentQ_eq_one_of_lowerFarey_sharp_no_lt
        one_le_logb_two_three hMono B hOneLt)

/-- shifted index が奇数なら正の index なので、対応する `P` は次段へ真に増加する。 -/
theorem p_lt_next_of_odd
    (D : BeattyRegularOstrowskiSystem)
    {n : ℕ}
    (hn : n % 2 = 1) :
    D.conv.P n < D.conv.P (n + 1) := by
  have hnPos : 0 < n := by omega
  exact D.conv.p_lt_succ_of_pos_index hnPos

/--
regular convergent の certificate から、`beattyInverseHeight` 用の exact Ostrowski corridor system を構成する。

正の residual に対する平行移動は sharp corridor theorem から導き、
端点値は shifted index の parity に応じて lower/upper Farey theorem から導く。
補正関数そのものは system 非依存の `endpointCorrection` を使う。
-/
noncomputable def exactCorridorSystem
    (D : BeattyRegularOstrowskiSystem) :
    ExactOstrowskiCorridorSystem beattyInverseHeight D.weights where
  P := D.conv.P
  ε := endpointCorrection
  epsilon_le_one := endpointCorrection_le_one
  translate := by
    intro n k hkPos hkRange
    have hmod : n % 2 = 0 ∨ n % 2 = 1 := by
      have hlt := Nat.mod_lt n (by omega : 0 < 2)
      omega
    rcases hmod with hEven | hOdd
    · exact beattyInverseHeight_add_currentQ_eq_add_currentP_of_lowerFarey_sharp
        (D.lowerBracket n hEven) hkPos hkRange
    · exact beattyInverseHeight_add_currentQ_eq_add_currentP_of_upperFarey_sharp
        (D.upperBracket n hOdd) (D.p_lt_next_of_odd hOdd) hkPos hkRange
  endpoint := by
    intro n
    have hmod : n % 2 = 0 ∨ n % 2 = 1 := by
      have hlt := Nat.mod_lt n (by omega : 0 < 2)
      omega
    rcases hmod with hEven | hOdd
    · have hEnd := beattyInverseHeight_currentQ_eq_currentP_of_lowerFarey_sharp
        (D.lowerBracket n hEven)
      simpa [endpointCorrection, hEven] using hEnd
    · have hEnd := beattyInverseHeight_currentQ_eq_currentP_add_one_of_upperFarey
        (D.upperBracket n hOdd) (D.p_lt_next_of_odd hOdd)
      simpa [endpointCorrection, hOdd] using hEnd

/--
任意の正整数 `N` に対する canonical Ostrowski digits から、Beatty inverse の exact corridor chain を
外部の chain certificate を仮定せずに自動生成できる。
-/
theorem canonicalDigits_generate_exactChain
    (D : BeattyRegularOstrowskiSystem)
    (N : ℕ)
    (hN : 0 < N) :
    let d := canonicalOstrowskiDigits D.weights N
    let j := canonicalOstrowskiMinIndex D.weights N hN
    ∃ xs : List (ℕ × ℕ),
      ExactInverseCorridorChain beattyInverseHeight xs (D.weights.Q j) ∧
      corridorQSum xs + D.weights.Q j = N ∧
      corridorPSum xs + D.conv.P j =
        ostrowskiPrefixSum D.conv.P d (N + 1) := by
  dsimp
  let j := canonicalOstrowskiMinIndex D.weights N hN
  have hj : j < N + 1 := canonicalOstrowskiMinIndex_lt D.weights N hN
  have hJPos : 0 < canonicalOstrowskiDigits D.weights N j :=
    canonicalOstrowskiMinIndex_digit_pos D.weights N hN
  have hBelow : ∀ i < j, canonicalOstrowskiDigits D.weights N i = 0 := by
    intro i hi
    exact canonicalOstrowskiDigits_eq_zero_below_min D.weights N hN hi
  obtain ⟨xs, Cxs, hQ, hP⟩ :=
    (D.exactCorridorSystem.exists_exactChain_of_boundedDigits
      (canonicalOstrowskiDigits_bounded D.weights N)
      hj hJPos hBelow)
  refine ⟨xs, Cxs, ?_, ?_⟩
  · rw [hQ, canonicalOstrowskiDigits_reconstruct D.weights N]
  · simpa [ExactOstrowskiCorridorSystem.pPrefix, exactCorridorSystem] using hP

/--
正整数 `N` に対する canonical Ostrowski 展開から、Beatty inverse height を正確に復元する公式。

補正は最小非零 digit の parity bit 一個だけで決まり、途中の corridor orientation は
高さの値に追加の補正を蓄積しない。
-/
theorem beattyCanonicalOstrowski_height_formula
    (D : BeattyRegularOstrowskiSystem)
    (N : ℕ)
    (hN : 0 < N) :
    beattyInverseHeight N =
      ostrowskiPrefixSum D.conv.P
          (canonicalOstrowskiDigits D.weights N) (N + 1) +
        (canonicalOstrowskiMinIndex D.weights N hN) % 2 := by
  have h := D.exactCorridorSystem.canonicalOstrowski_height_formula N hN
  simpa [ExactOstrowskiCorridorSystem.pPrefix,
    exactCorridorSystem, endpointCorrection] using h

/-- 最小非零 digit の index が偶数、すなわち lower endpoint 側なら補正項は `0` になる。 -/
theorem beattyCanonicalOstrowski_height_formula_lower
    (D : BeattyRegularOstrowskiSystem)
    (N : ℕ)
    (hN : 0 < N)
    (hEven : canonicalOstrowskiMinIndex D.weights N hN % 2 = 0) :
    beattyInverseHeight N =
      ostrowskiPrefixSum D.conv.P
        (canonicalOstrowskiDigits D.weights N) (N + 1) := by
  rw [D.beattyCanonicalOstrowski_height_formula N hN, hEven]
  simp

/-- 最小非零 digit の index が奇数、すなわち upper endpoint 側なら補正項は正確に `+1` になる。 -/
theorem beattyCanonicalOstrowski_height_formula_upper
    (D : BeattyRegularOstrowskiSystem)
    (N : ℕ)
    (hN : 0 < N)
    (hOdd : canonicalOstrowskiMinIndex D.weights N hN % 2 = 1) :
    beattyInverseHeight N =
      ostrowskiPrefixSum D.conv.P
          (canonicalOstrowskiDigits D.weights N) (N + 1) + 1 := by
  rw [D.beattyCanonicalOstrowski_height_formula N hN, hOdd]

/-- 同じ canonical Ostrowski 公式を `ceil(N log₃2)` の形で書き直した Sturmian ceiling 版。 -/
theorem sturmianCanonicalOstrowski_ceiling_formula
    (D : BeattyRegularOstrowskiSystem)
    (N : ℕ)
    (hN : 0 < N) :
    ⌈(N : ℝ) * Real.logb 3 2⌉₊ =
      ostrowskiPrefixSum D.conv.P
          (canonicalOstrowskiDigits D.weights N) (N + 1) +
        (canonicalOstrowskiMinIndex D.weights N hN) % 2 := by
  calc
    ⌈(N : ℝ) * Real.logb 3 2⌉₊ = beattyInverseHeight N :=
      (beattyInverseHeight_eq_natCeil_mul_logb_three_two N).symm
    _ = _ := D.beattyCanonicalOstrowski_height_formula N hN

/-- admissible な strict record cut では、その位置の profile height は正である。 -/
theorem admissibleRecordCut_profileHeight_pos
    {m : ℕ}
    {h : Critical.Profile m}
    (A : Critical.Admissible h)
    {a : ℕ}
    (R : Ferrers.IsRecordCutAfter h Critical.initialRoofAnchor a) :
    0 < Critical.profileHeight h a := by
  have hContact := admissibleRecordCut_eq_exactInverseBoundary A R
  have haPos : 0 < a := by
    have ha := R.1
    simp [Critical.initialRoofAnchor] at ha
    omega
  by_contra hNot
  have hZero : Critical.profileHeight h a = 0 := Nat.eq_zero_of_not_pos hNot
  rw [hZero] at hContact
  simp at hContact
  omega

/-- deterministic な `initialRecordCuts` に属する cut でも、その profile height は正である。 -/
theorem admissibleInitialRecordCut_profileHeight_pos
    {m : ℕ}
    {h : Critical.Profile m}
    (A : Critical.Admissible h)
    {a : ℕ}
    (ha : a ∈ Ferrers.initialRecordCuts h) :
    0 < Critical.profileHeight h a := by
  have hContact := admissibleInitialRecordCut_eq_exactInverseBoundary A ha
  have haAnchor := Ferrers.initialRecordCut_gt_anchor ha
  have haPos : 0 < a := by
    simp [Critical.initialRoofAnchor] at haAnchor
    omega
  by_contra hNot
  have hZero : Critical.profileHeight h a = 0 := Nat.eq_zero_of_not_pos hNot
  rw [hZero] at hContact
  simp at hContact
  omega

/--
admissible な strict record cut の高さを canonical Ostrowski 表現へ展開すると、
その横座標は `P` による重み付き和と最小非零 digit の parity から正確に復元できる。
-/
theorem admissibleRecordCut_coordinate_eq_canonicalOstrowski
    (D : BeattyRegularOstrowskiSystem)
    {m : ℕ}
    {h : Critical.Profile m}
    (A : Critical.Admissible h)
    {a : ℕ}
    (R : Ferrers.IsRecordCutAfter h Critical.initialRoofAnchor a) :
    let N := Critical.profileHeight h a
    a = ostrowskiPrefixSum D.conv.P
        (canonicalOstrowskiDigits D.weights N) (N + 1) +
      canonicalOstrowskiMinIndex D.weights N
        (admissibleRecordCut_profileHeight_pos A R) % 2 := by
  dsimp
  have hContact := admissibleRecordCut_eq_exactInverseBoundary A R
  have hNPos := admissibleRecordCut_profileHeight_pos A R
  have hFormula :=
    D.beattyCanonicalOstrowski_height_formula
      (Critical.profileHeight h a) hNPos
  rw [hFormula] at hContact
  exact hContact.symm

/-- deterministic な `initialRecordCuts` に属する cut に対する canonical Ostrowski 座標公式。 -/
theorem admissibleInitialRecordCut_coordinate_eq_canonicalOstrowski
    (D : BeattyRegularOstrowskiSystem)
    {m : ℕ}
    {h : Critical.Profile m}
    (A : Critical.Admissible h)
    {a : ℕ}
    (ha : a ∈ Ferrers.initialRecordCuts h) :
    let N := Critical.profileHeight h a
    a = ostrowskiPrefixSum D.conv.P
        (canonicalOstrowskiDigits D.weights N) (N + 1) +
      canonicalOstrowskiMinIndex D.weights N
        (admissibleInitialRecordCut_profileHeight_pos A ha) % 2 := by
  dsimp
  have hContact := admissibleInitialRecordCut_eq_exactInverseBoundary A ha
  have hNPos := admissibleInitialRecordCut_profileHeight_pos A ha
  have hFormula :=
    D.beattyCanonicalOstrowski_height_formula
      (Critical.profileHeight h a) hNPos
  rw [hFormula] at hContact
  exact hContact.symm

/-- RecordFerrers 版は admissible な initial-record cut の座標定理から直接従う薄い wrapper。 -/
theorem recordFerrers_initialRecordCut_coordinate_eq_canonicalOstrowski
    (D : BeattyRegularOstrowskiSystem)
    {m : ℕ}
    (RF : Ferrers.RecordFerrers m)
    {a : ℕ}
    (ha : a ∈ Ferrers.initialRecordCuts RF.profile.1) :
    let N := Critical.profileHeight RF.profile.1 a
    a = ostrowskiPrefixSum D.conv.P
        (canonicalOstrowskiDigits D.weights N) (N + 1) +
      canonicalOstrowskiMinIndex D.weights N
        (admissibleInitialRecordCut_profileHeight_pos RF.profile.2 ha) % 2 := by
  exact D.admissibleInitialRecordCut_coordinate_eq_canonicalOstrowski
    RF.profile.2 ha

end BeattyRegularOstrowskiSystem

end Bridge
end Collatz3
