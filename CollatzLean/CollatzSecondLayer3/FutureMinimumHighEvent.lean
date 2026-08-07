import CollatzLean.CollatzSecondLayer3.ConstantTerminalObstruction
import CollatzLean.CollatzSecondLayer3.UnboundedConstantReduction
import CollatzLean.CollatzSecondLayer3.ContractingWindowBounds
import CollatzLean.CollatzOrbitCore.PeriodicExponent

/-!
# future-minimum上のhigh-exponent eventとT=0 Constant terminal

非有界odd-only軌道のfuture-minimumでは開始指数はexactに1である。
一方、指数が1より大きい位置はcofinalに現れる。

future-minimumから十分遠いhigh-exponent位置までのwindowを見ると、
初期first-carryはcaptureでもsynchronizedでもあり得ずdeferredとなる。
さらにwindow長がfuture-minimum値より大きければcanonical modulusが開始値を越えるため、
deep lower replay枝は不可能で、window自体がSpecial C3になる。

従ってhigh-exponent位置を十分遠くから選べば、全項でfirst-deferred terminalTimeが0の
Constant terminal Special C3 familyを構成できる。
-/

namespace CollatzSecondLayer3

open CollatzSupport
open CollatzCore
open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

/-- 指数が1より真に大きい位置。 -/
def HighExponentAt (O : OddOrbit) (n : ℕ) : Prop :=
  1 < O.exponent n

/--
非有界軌道のfuture-minimumでは次指数はexactに1。
指数が2以上なら次値は開始値以下になり、future-minimum性と合わせて値再訪になる。
-/
theorem futureMinimum_exponent_eq_one_of_unbounded
    (O : OddOrbit)
    (hU : O.Unbounded)
    {anchor : ℕ}
    (hmin : O.FutureMinimumAt anchor) :
    O.exponent anchor = 1 := by
  have hePos := O.exponent_pos anchor
  by_contra hne
  have heTwo : 2 ≤ O.exponent anchor := by omega
  have hpow : 4 ≤ 2 ^ O.exponent anchor := by
    simpa using
      (Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) heTwo)
  have hstep := O.step anchor
  have hstartPos := O.value_pos anchor
  have hscaled :
      4 * O.value (anchor + 1) ≤ 4 * O.value anchor := by
    calc
      4 * O.value (anchor + 1)
          ≤ 2 ^ O.exponent anchor * O.value (anchor + 1) :=
        Nat.mul_le_mul_right _ hpow
      _ = 3 * O.value anchor + 1 := hstep
      _ ≤ 4 * O.value anchor := by omega
  have hnextLe : O.value (anchor + 1) ≤ O.value anchor :=
    Nat.le_of_mul_le_mul_left hscaled (by omega)
  have hstartLe : O.value anchor ≤ O.value (anchor + 1) :=
    hmin (anchor + 1) (by omega)
  have heq : O.value anchor = O.value (anchor + 1) :=
    Nat.le_antisymm hstartLe hnextLe
  exact
    (O.value_ne_of_lt_of_unbounded hU (by omega : anchor < anchor + 1)) heq

/-- 指数>1の位置は任意に遠くに存在する。 -/
theorem highExponent_cofinally
    (O : OddOrbit) :
    Cofinally (fun n => HighExponentAt O n) := by
  intro N
  by_contra hnone
  push Not at hnone
  have hconstant : ∀ n : ℕ, N ≤ n → O.exponent n = 1 := by
    intro n hn
    have hpos := O.exponent_pos n
    have hnotHigh := hnone n hn
    unfold HighExponentAt at hnotHigh
    omega
  have hperiod : ∀ t : ℕ,
      O.exponent (N + t + 1) = O.exponent (N + t) := by
    intro t
    rw [hconstant (N + t + 1) (by omega)]
    rw [hconstant (N + t) (by omega)]
  have hword : O.segmentWord N 1 = [1] := by
    simp [hconstant N le_rfl]
  have hexpanding : Expanding (O.segmentWord N 1) := by
    rw [hword]
    norm_num [Expanding, oddSteps, twoSteps]
  exact O.no_expanding_periodic_exponent_tail
    (q := 1) hperiod hexpanding

/-- 固定anchorから測った正offsetのhigh-exponent位置もcofinalに存在する。 -/
theorem highOffset_cofinally
    (O : OddOrbit)
    (anchor : ℕ) :
    Cofinally (fun q => 0 < q ∧ HighExponentAt O (anchor + q)) := by
  intro N
  obtain ⟨n, hn, hhigh⟩ :=
    highExponent_cofinally O (anchor + max N 1)
  let q := n - anchor
  have hanchor : anchor ≤ n := by omega
  have hqN : N ≤ q := by
    dsimp [q]
    omega
  have hqPos : 0 < q := by
    dsimp [q]
    omega
  have hindex : anchor + q = n := by
    dsimp [q]
    omega
  refine ⟨q, hqN, hqPos, ?_⟩
  rw [hindex]
  exact hhigh

namespace FutureMinimumAllLengthTerminalData

/-- `n < 2^(n+1)`。canonical modulusの粗い下界に使う。 -/
private theorem nat_lt_twoPow_succ_highEvent (n : ℕ) :
    n < 2 ^ (n + 1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [pow_succ]
      have hpowPos : 0 < 2 ^ (n + 1) :=
        Nat.pow_pos (by omega)
      omega

/--
future-minimumからhigh-exponent位置までのwindowは開始時点でdeferred。
開始指数は1であり、captureなら終端指数<1、syncなら終端指数=1となるため、
high-exponent終端とは両立しない。
-/
noncomputable def highEvent_initialDeferred
    {O : OddOrbit}
    (hU : O.Unbounded)
    {anchor q : ℕ}
    (hmin : O.FutureMinimumAt anchor)
    (hq : 0 < q)
    (hhigh : HighExponentAt O (anchor + q)) :
    O.DeferredWindowAt anchor q := by
  let D := futureMinimumWindowDifference O hU anchor q hmin hq
  have hstartExp : O.exponent anchor = 1 :=
    futureMinimum_exponent_eq_one_of_unbounded O hU hmin
  cases O.windowCarryOutcome D with
  | captured C =>
      have hend := C.upperExponent_lt_lowerExponent
      have hend' : O.exponent (anchor + q) < 1 := by
        simpa [hstartExp] using hend
      unfold HighExponentAt at hhigh
      exact False.elim (by omega)
  | synchronized S =>
      have hend := S.upperExponent_eq_lower
      have hend' : O.exponent (anchor + q) = 1 := by
        simpa [hstartExp] using hend
      unfold HighExponentAt at hhigh
      exact False.elim (by omega)
  | deferred E =>
      exact E

/--
window長がfuture-minimum値より大きければ、開始値はwindow residue modulus未満。
-/
theorem futureMinimum_startValue_lt_residueModulus
    {O : OddOrbit}
    {anchor q : ℕ}
    (hlarge : O.value anchor < q) :
    O.value anchor < residueModulus (O.segmentWord anchor q) := by
  have hvalid : Valid (O.segmentWord anchor q) :=
    (O.runs_segment anchor q).valid
  have hsteps : q ≤ twoSteps (O.segmentWord anchor q) := by
    have h := oddSteps_le_twoSteps hvalid
    simpa [oddSteps] using h
  have hqpow : q < 2 ^ (q + 1) :=
    nat_lt_twoPow_succ_highEvent q
  have hpow :
      2 ^ (q + 1) ≤
        2 ^ (twoSteps (O.segmentWord anchor q) + 1) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  unfold residueModulus
  exact lt_of_lt_of_le (lt_trans hlarge hqpow) hpow

noncomputable def futureMinimum_highEvent_specialC3
    {O : OddOrbit}
    (hU : O.Unbounded)
    {anchor q : ℕ}
    (hmin : O.FutureMinimumAt anchor)
    (hq : 0 < q)
    (hlarge : O.value anchor < q)
    (hhigh : HighExponentAt O (anchor + q)) :
    SpecialC3At O anchor q := by
  let E := highEvent_initialDeferred hU hmin hq hhigh
  have hSpecial :
      Nonempty (SpecialC3At O anchor q) := by
    rcases deferredWindow_generic_dichotomy E hq with hDeep | hSpecial
    · rcases hDeep with ⟨D⟩
      have hlt := futureMinimum_startValue_lt_residueModulus hlarge
      have hle := deep_residueModulus_le_startValue D
      exact False.elim ((Nat.not_le_of_gt hlt) hle)
    · exact hSpecial
  exact Classical.choice hSpecial

end FutureMinimumAllLengthTerminalData


/--
初期windowが既にdeferredなら、任意のfinite first-deferred normalizationのterminalTimeは0。
-/
theorem terminalTime_eq_zero_of_initialDeferred
    {O : OddOrbit} {start q : ℕ}
    {D₀ : O.WindowDifferenceData start q}
    (F : O.FiniteCaptureNormalizationData D₀)
    (E : O.DeferredWindowAt start q) :
    F.terminalTime = 0 := by
  by_contra hne
  have hpos : 0 < F.terminalTime := Nat.pos_of_ne_zero hne
  rcases F.before 0 hpos with ⟨C | S⟩
  · let C₀ : O.CapturedWindowAt start q := by
      simpa using C
    have hdepth :=
      OddOrbit.WindowDifferenceData.depth_unique
        C₀.toWindowDifferenceData E.toWindowDifferenceData
    have hcap := C₀.captured
    have hdef := E.deferred
    omega
  · let S₀ : O.SynchronizedWindowAt start q := by
      simpa using S
    have hdepth :=
      OddOrbit.WindowDifferenceData.depth_unique
        S₀.toWindowDifferenceData E.toWindowDifferenceData
    have hsync := S₀.synchronized
    have hdef := E.deferred
    omega


/--
一つのfuture-minimumから、十分遠いhigh-exponent位置を狭義増加に選んだtower。
各長さは開始値そのものより大きくしてあるため、対応windowは自動的にSpecial C3になる。
-/
structure FutureMinimumHighEventTowerData (O : OddOrbit) where
  unbounded : O.Unbounded
  anchor : ℕ
  futureMinimum : O.FutureMinimumAt anchor
  length : ℕ → ℕ
  length_strict : StrictMono length
  anchorValue_lt_length : ∀ n : ℕ, O.value anchor < length n
  high : ∀ n : ℕ, HighExponentAt O (anchor + length n)

namespace FutureMinimumHighEventTowerData

/-- 任意の非有界軌道とfuture-minimumからhigh-event towerを構成する。 -/
noncomputable def ofFutureMinimum
    (O : OddOrbit)
    (hU : O.Unbounded)
    (anchor : ℕ)
    (hmin : O.FutureMinimumAt anchor) :
    FutureMinimumHighEventTowerData O := by
  let P : ℕ → Prop :=
    fun q => 0 < q ∧ HighExponentAt O (anchor + q)
  have hP : Cofinally P := highOffset_cofinally O anchor
  let raw : ℕ → ℕ := Cofinally.select P hP
  let s : ℕ → ℕ :=
    fun n => raw (O.value anchor + 1 + n)
  refine
    { unbounded := hU
      anchor := anchor
      futureMinimum := hmin
      length := s
      length_strict := ?_
      anchorValue_lt_length := ?_
      high := ?_ }
  · intro a b hab
    dsimp [s]
    exact
      (Cofinally.select_strict P hP)
        (by omega)
  · intro n
    have hge :=
      Cofinally.select_ge P hP (O.value anchor + 1 + n)
    dsimp [s, raw]
    omega
  · intro n
    have hs :=
      Cofinally.select_spec P hP (O.value anchor + 1 + n)
    dsimp [s, raw]
    exact hs.2

/-- 非有界軌道から標準future-minimumを用いてhigh-event towerを作る。 -/
noncomputable def ofUnbounded
    (O : OddOrbit)
    (hU : O.Unbounded) :
    FutureMinimumHighEventTowerData O := by
  let anchor := O.tailMinIndex 0
  have hmin : O.FutureMinimumAt anchor := by
    simpa [anchor] using O.futureMinimumAt_tailMinIndex 0
  exact ofFutureMinimum O hU anchor hmin

/-- high-event towerの各lengthは正。 -/
theorem length_pos
    {O : OddOrbit}
    (H : FutureMinimumHighEventTowerData O)
    (n : ℕ) :
    0 < H.length n := by
  have h := H.anchorValue_lt_length n
  have hp := O.value_pos H.anchor
  omega

/-- high-event towerを同じanchorのall-length first-deferred系へ戻す。 -/
noncomputable def allLengthData
    {O : OddOrbit}
    (H : FutureMinimumHighEventTowerData O) :
    FutureMinimumAllLengthTerminalData O :=
  { unbounded := H.unbounded
    anchor := H.anchor
    futureMinimum := H.futureMinimum }

/-- `length=n+1`列挙へ対応するall-length添字。 -/
def allLengthIndex
    {O : OddOrbit}
    (H : FutureMinimumHighEventTowerData O)
    (n : ℕ) : ℕ :=
  H.length n - 1

/-- all-length添字も狭義増加。 -/
theorem allLengthIndex_strict
    {O : OddOrbit}
    (H : FutureMinimumHighEventTowerData O) :
    StrictMono H.allLengthIndex := by
  intro a b hab
  have hlt := H.length_strict hab
  have ha := H.length_pos a
  have hb := H.length_pos b
  unfold allLengthIndex
  omega

/-- all-length側で復元したwindow長は元high-event lengthに一致。 -/
theorem allLength_length_eq
    {O : OddOrbit}
    (H : FutureMinimumHighEventTowerData O)
    (n : ℕ) :
    H.allLengthData.length (H.allLengthIndex n) = H.length n := by
  unfold FutureMinimumAllLengthTerminalData.length allLengthIndex
  have hp := H.length_pos n
  omega

/-- high-event tower各項の初期windowはdeferred。 -/
noncomputable def initialDeferred
    {O : OddOrbit}
    (H : FutureMinimumHighEventTowerData O)
    (n : ℕ) :
    O.DeferredWindowAt H.anchor (H.length n) :=
  FutureMinimumAllLengthTerminalData.highEvent_initialDeferred
    H.unbounded H.futureMinimum (H.length_pos n) (H.high n)

/-- high-event tower各項はSpecial C3。 -/
noncomputable def specialC3
    {O : OddOrbit}
    (H : FutureMinimumHighEventTowerData O)
    (n : ℕ) :
    SpecialC3At O H.anchor (H.length n) :=
  FutureMinimumAllLengthTerminalData.futureMinimum_highEvent_specialC3
    H.unbounded H.futureMinimum (H.length_pos n)
    (H.anchorValue_lt_length n) (H.high n)

/-- high-event tower各項のall-length first-deferred terminalTimeはexactに0。 -/
theorem terminalTime_eq_zero
    {O : OddOrbit}
    (H : FutureMinimumHighEventTowerData O)
    (n : ℕ) :
    H.allLengthData.terminalTime (H.allLengthIndex n) = 0 := by
  let A := H.allLengthData
  let j := H.allLengthIndex n
  have hlen : A.length j = H.length n := by
    simpa [A, j] using H.allLength_length_eq n
  have E : O.DeferredWindowAt A.anchor (A.length j) := by
    rw [hlen]
    exact H.initialDeferred n
  change (A.normalization j).terminalTime = 0
  exact terminalTime_eq_zero_of_initialDeferred (A.normalization j) E

/--
high-event towerからterminalTime=0のConstant terminal Special C3 familyを直接構成する。
-/
noncomputable def zeroTerminalFamily
    {O : OddOrbit}
    (H : FutureMinimumHighEventTowerData O) :
    FutureMinimumAllLengthTerminalData.ConstantTerminalSpecialC3FamilyData
      H.allLengthData := by
  refine
    { terminal := 0
      select := H.allLengthIndex
      select_strict := H.allLengthIndex_strict
      terminal_eq := ?_
      special := ?_ }
  · intro n
    exact H.terminalTime_eq_zero n
  · intro n
    let A := H.allLengthData
    let j := H.allLengthIndex n
    have hlen : A.length j = H.length n := by
      simpa [A, j] using H.allLength_length_eq n
    have hstart : A.terminalStart j = H.anchor := by
      change A.anchor + A.terminalTime j = H.anchor
      have hzero : A.terminalTime j = 0 := by
        simpa [A, j] using H.terminalTime_eq_zero n
      rw [hzero]
      simp [A]
      rfl
    refine ⟨?_⟩
    change SpecialC3At O (A.terminalStart j) (A.length j)
    rw [hstart, hlen]
    exact H.specialC3 n

end FutureMinimumHighEventTowerData


/--
任意の非有界軌道は、あるall-length系上にterminalTime=0のConstant Special C3 familyを持つ。
これがConstant terminalをT=0枝へ縮約する直接定理。
-/
theorem zeroTerminalConstantFamily_of_unbounded
    (O : OddOrbit)
    (hU : O.Unbounded) :
    ∃ A : FutureMinimumAllLengthTerminalData O,
      ∃ F : FutureMinimumAllLengthTerminalData.ConstantTerminalSpecialC3FamilyData A,
        F.terminal = 0 := by
  let H := FutureMinimumHighEventTowerData.ofUnbounded O hU
  let A := H.allLengthData
  let F := H.zeroTerminalFamily
  exact ⟨A, F, rfl⟩

/-- 非有界軌道上のfuture-minimum high-event towerが存在すること。 -/
def HasFutureMinimumHighEventTower : Prop :=
  ∃ O : OddOrbit, Nonempty (FutureMinimumHighEventTowerData O)

/-- 任意の非有界odd-only軌道はhigh-event towerを生成する。 -/
theorem hasFutureMinimumHighEventTower_of_unbounded
    (hU : HasUnboundedOddOrbit) :
    HasFutureMinimumHighEventTower := by
  rcases hU with ⟨O, hO⟩
  exact ⟨O, ⟨FutureMinimumHighEventTowerData.ofUnbounded O hO⟩⟩

/-- high-event towerを排除すれば非有界odd-only軌道は存在しない。 -/
theorem no_unbounded_odd_orbit_of_highEvent_exclusion
    (hHigh : ¬ HasFutureMinimumHighEventTower) :
    ¬ HasUnboundedOddOrbit := by
  intro hU
  exact hHigh (hasFutureMinimumHighEventTower_of_unbounded hU)

/-- Constant terminal排除原理はhigh-event towerを排除する。 -/
theorem no_highEventTower_of_constantTerminal_exclusion
    (hConstant : ConstantTerminalExclusionPrinciple) :
    ¬ HasFutureMinimumHighEventTower := by
  rintro ⟨O, ⟨H⟩⟩
  let A := H.allLengthData
  have hNo := hConstant O A
  exact hNo ⟨H.zeroTerminalFamily⟩

end CollatzSecondLayer3
