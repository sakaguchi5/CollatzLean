import CollatzLean.CollatzSecondLayer.InfiniteBranches

/-!
# 深さ非有界な修正後Special C3部分列

Special C3はcanonical境界、negative predecessor shadow、deferred prepared carryを
保存する。ordered元差分と同期由来もsnapshotへ残し、carry深さとsuffix長の
定量接続を有限項ごとに証明する。
-/

namespace CollatzSecondLayer

open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

/-- 一つの修正後Special C3項だけを保存する有限snapshot。 -/
structure SpecialC3Data where
  orbit : OddOrbit
  sourceCylinder : CanonicalC3Witness
  terminalPair : TerminalPairData
  sourceRelation :
    terminalPair.A ++ terminalPair.R = sourceCylinder.word
  sourceStart : terminalPair.X = sourceCylinder.start
  sourceFinish : terminalPair.YAR = sourceCylinder.finish
  carry : CarryComparison
  carryOrigin : CarryOrigin orbit terminalPair carry
  deferredCarry : DeferredCarry carry
  replay :
    CanonicalReplayCoordinate
      terminalPair.R terminalPair.YA terminalPair.YAR
  canonicalBoundary : replay.quotient = 0
  negativePredecessorShadow :
    predecessorShadow terminalPair.R < 0

namespace SpecialC3Data

/-- snapshotが保存するprepared carry。 -/
def prepared (D : SpecialC3Data) :
    PreparedCarryData D.orbit D.terminalPair :=
  D.carryOrigin.prepared

/-- 保存されたcarryはprepared carryから構成されたもの。 -/
theorem carry_eq_prepared (D : SpecialC3Data) :
    D.carry = D.prepared.toCarryComparison :=
  D.carryOrigin.carry_eq

/-- Special C3 snapshotが持つconnection方程式。 -/
theorem connectionEquation (D : SpecialC3Data) :
    (D.terminalPair.YAR : ℤ) -
        predecessorShadow D.terminalPair.R =
      2 * (3 : ℤ) ^ oddSteps D.terminalPair.R := by
  have h := D.replay.connectionEquation
  rw [D.canonicalBoundary] at h
  simpa using h

/-- negative predecessor shadowの大きさをexactに表す。 -/
theorem negativeShadowExact (D : SpecialC3Data) :
    - predecessorShadow D.terminalPair.R =
      2 * (3 : ℤ) ^ oddSteps D.terminalPair.R -
        (D.terminalPair.YAR : ℤ) := by
  have h := D.connectionEquation
  linear_combination h

/-- Special C3では実終点は`2*3^q`より小さい。 -/
theorem finish_lt_two_mul_threePow (D : SpecialC3Data) :
    (D.terminalPair.YAR : ℤ) <
      2 * (3 : ℤ) ^ oddSteps D.terminalPair.R := by
  have h := D.connectionEquation
  have hneg := D.negativePredecessorShadow
  omega

/-- canonical境界ではsuffix開始値はcanonical最小非負代表そのもの。 -/
theorem suffixStart_eq_canonicalStart (D : SpecialC3Data) :
    D.terminalPair.YA = canonicalStart D.terminalPair.R :=
  D.replay.start_eq_canonical_of_quotient_eq_zero D.canonicalBoundary

/-- terminal center差は自動的に非零。 -/
theorem changingCenter (D : SpecialC3Data) :
    center D.terminalPair.A ≠ center D.terminalPair.R :=
  D.terminalPair.center_ne

/-- `3^q ≤ 2^(2q)`という初等的指数比較。 -/
lemma threePow_le_twoPow_twice (q : ℕ) :
    3 ^ q ≤ 2 ^ (2 * q) := by
  induction q with
  | zero =>
      simp
  | succ q ih =>
      rw [pow_succ]
      rw [show 2 * (q + 1) = 2 * q + 2 by omega, pow_add]
      norm_num
      gcongr
      norm_num

/--
Special C3の元terminal差深さはsuffixのodd-step長の2倍以下。
-/
theorem originalDepth_le_twice_suffixLength (D : SpecialC3Data) :
    D.prepared.ordered.depth ≤ 2 * oddSteps D.terminalPair.R := by
  let q := oddSteps D.terminalPair.R
  have hYApos : 0 < D.terminalPair.YA := by
    have hodd :=
      D.terminalPair.runA.end_odd_of_ne_nil D.terminalPair.A_nonempty
    rcases hodd with ⟨k, hk⟩
    omega
  have hpowDiff :
      2 ^ D.prepared.ordered.depth ≤
        D.terminalPair.YAR - D.terminalPair.YA :=
    D.prepared.ordered.twoPow_le_difference
  have hYAle :
      D.terminalPair.YA ≤ D.terminalPair.YAR := by
    exact Nat.le_of_lt D.prepared.ordered.value_lt
  have hdiffFinish :
      D.terminalPair.YAR - D.terminalPair.YA <
        D.terminalPair.YAR := by
    exact Nat.sub_lt_self hYApos hYAle
  have hfinishNat :
      D.terminalPair.YAR < 2 * 3 ^ q := by
    exact_mod_cast D.finish_lt_two_mul_threePow
  have hthree : 3 ^ q ≤ 2 ^ (2 * q) :=
    threePow_le_twoPow_twice q
  have htwoThree :
      2 * 3 ^ q ≤ 2 ^ (2 * q + 1) := by
    calc
      2 * 3 ^ q ≤ 2 * 2 ^ (2 * q) :=
        Nat.mul_le_mul_left 2 hthree
      _ = 2 ^ (2 * q + 1) := by
        rw [pow_succ]
        ring
  have hpowLt :
      2 ^ D.prepared.ordered.depth < 2 ^ (2 * q + 1) := by
    exact lt_of_le_of_lt hpowDiff
      (lt_of_lt_of_le
        (lt_trans hdiffFinish hfinishNat)
        htwoThree)
  by_contra hnot
  have hexp : 2 * q + 1 ≤ D.prepared.ordered.depth := by omega
  have hmono :
      2 ^ (2 * q + 1) ≤ 2 ^ D.prepared.ordered.depth :=
    Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) hexp
  omega

/-- prepared carry深さもsuffix長の2倍以下。 -/
theorem preparedDepth_le_twice_suffixLength (D : SpecialC3Data) :
    D.carry.d ≤ 2 * oddSteps D.terminalPair.R := by
  rw [D.carry_eq_prepared]
  change D.prepared.remainingDepth ≤ 2 * oddSteps D.terminalPair.R
  exact D.prepared.remainingDepth_le_original.trans
    D.originalDepth_le_twice_suffixLength

/-- 同期prefix長とprepared深さの合計もsuffix長の2倍以下。 -/
theorem syncLength_add_preparedDepth_le_twice_suffixLength
    (D : SpecialC3Data) :
    D.prepared.boundary.word.length + D.carry.d ≤
      2 * oddSteps D.terminalPair.R := by
  rw [D.carry_eq_prepared]
  change
    D.prepared.boundary.word.length + D.prepared.remainingDepth ≤
      2 * oddSteps D.terminalPair.R
  exact D.prepared.syncLength_add_remainingDepth_le_original.trans
    D.originalDepth_le_twice_suffixLength

end SpecialC3Data

namespace SpecialC3At

/-- 無限解析列中の修正後Special C3項から有限snapshotを切り出す。 -/
noncomputable def snapshot
    {O : OddOrbit}
    {S : C3CylinderSequence O}
    {E : InfiniteTerminalExtraction S}
    {n : ℕ}
    {P : TerminalAnalysisPacket E n}
    (H : SpecialC3At P) : SpecialC3Data where
  orbit := O
  sourceCylinder := P.sourceCylinder
  terminalPair := P.criticalPair
  sourceRelation := P.sourceRelation
  sourceStart := P.sourceStart
  sourceFinish := P.sourceFinish
  carry := P.carry
  carryOrigin := P.carryOrigin
  deferredCarry := H.deferredCarry
  replay := P.replayCoordinate
  canonicalBoundary := H.canonicalBoundary
  negativePredecessorShadow := H.negativePredecessorShadow

end SpecialC3At

/--
修正後Special C3項が一つの無限解析列から狭義単調な部分列として抽出され、
そのprepared first-carry深さが無限大へ進むこと。
-/
structure ArbitrarilyDeepSpecialC3Data
    {O : OddOrbit}
    {S : C3CylinderSequence O}
    {E : InfiniteTerminalExtraction S}
    (A : InfiniteTerminalAnalysis E) where
  select : Subsequence
  special : ∀ n : ℕ,
    SpecialC3At (A.packet (select.index n))
  depths_tend_to_infinity :
    ∀ M : ℕ, ∃ J : ℕ, ∀ j : ℕ, J ≤ j →
      M < (A.packet (select.index j)).carry.d

/-- 深さが任意に大きい修正後Special C3部分列が存在すること。 -/
def HasArbitrarilyDeepSpecialC3 : Prop :=
  ∃ O : OddOrbit,
  ∃ S : C3CylinderSequence O,
  ∃ E : InfiniteTerminalExtraction S,
  ∃ A : InfiniteTerminalAnalysis E,
    Nonempty (ArbitrarilyDeepSpecialC3Data A)

/--
第三bridge。

ordered terminal差分と下側軌道埋込みを各項で構成し、alternative exit候補が
無限部分列上で持続するか、深さ非有界な修正後Special C3部分列へ送る。
未解決の強いterminal抽出とbounded-depth rigidityをここへ集約する。
-/
def InfiniteTerminalAnalysisPrinciple : Prop :=
  ∀ O : OddOrbit,
  ∀ S : C3CylinderSequence O,
  ∀ E : InfiniteTerminalExtraction S,
    ∃ A : InfiniteTerminalAnalysis E,
      Nonempty (PersistentAlternativeExitData A) ∨
      Nonempty (ArbitrarilyDeepSpecialC3Data A)

/--
第三bridge前半：各terminal pairからordered完全差分を構成し、
解析packetを作れること。軌道埋込みと同期境界は自動導出される。
-/
def TerminalPacketConstructionPrinciple : Prop :=
  ∀ O : OddOrbit,
  ∀ S : C3CylinderSequence O,
  ∀ E : InfiniteTerminalExtraction S,
  ∀ n : ℕ,
    Nonempty (TerminalAnalysisPacket E n)

/--
第三bridge後半：構成済みpacket列から、持続的alternativeまたは深さ非有界
Special C3部分列を抽出できること。
-/
def InfiniteOutcomeExtractionPrinciple : Prop :=
  ∀ O : OddOrbit,
  ∀ S : C3CylinderSequence O,
  ∀ E : InfiniteTerminalExtraction S,
  ∀ A : InfiniteTerminalAnalysis E,
    Nonempty (PersistentAlternativeExitData A) ∨
    Nonempty (ArbitrarilyDeepSpecialC3Data A)

/-- packet構成と無限outcome抽出から第三bridge全体を組み立てる。 -/
theorem infiniteTerminalAnalysisPrinciple_of_parts
    (hPacket : TerminalPacketConstructionPrinciple)
    (hOutcome : InfiniteOutcomeExtractionPrinciple) :
    InfiniteTerminalAnalysisPrinciple := by
  intro O S E
  let A : InfiniteTerminalAnalysis E :=
    { packet := fun n => Classical.choice (hPacket O S E n) }
  exact ⟨A, hOutcome O S E A⟩

/-- C3排除側が最終的に証明すべき命題。 -/
def AsymptoticSpecialC3ExclusionPrinciple : Prop :=
  ¬ HasArbitrarilyDeepSpecialC3

end CollatzSecondLayer
