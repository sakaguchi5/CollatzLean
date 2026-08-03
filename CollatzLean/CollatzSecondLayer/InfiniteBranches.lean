import CollatzLean.CollatzSecondLayer.PreparedCarry
import CollatzLean.CollatzFirstLayer.DownwardReplay
import CollatzLean.CollatzFirstLayer.DepthCoefficient

/-!
# prepared carryとcanonical replayによる無限terminal解析

packetはordered terminal差分と下側値の軌道埋込みだけを保存する。
最小同期境界、上下同期run、prepared carry比較はそこから自動構成する。
positive replay枝はアフィン等式だけでなくactual `Runs`まで保存する。
-/

namespace CollatzSecondLayer

open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

/-- first-carry三分岐を適用できる有限整数データ。 -/
structure RawCarryComparison where
  x : ℕ
  y : ℕ
  d : ℕ
  e : ℕ
  a : ℕ
  u : ℕ
  difference : y = x + 2 ^ d * u
  difference_odd : Odd u
  lower_factorization : 3 * x + 1 = 2 ^ e * a
  lower_odd : Odd a

/-- raw carry比較の完全な三分岐。 -/
noncomputable def RawCarryComparison.outcome
    (C : RawCarryComparison) :
    FirstCarryOutcome C.x C.y C.d C.e C.a C.u :=
  first_carry_trichotomy
    C.difference C.difference_odd
    C.lower_factorization C.lower_odd

/-- 同期prefixを消費して`d ≤ e`へ到達したcarry比較。 -/
structure CarryComparison extends RawCarryComparison where
  depth_le : d ≤ e

/-- prepared carryからfirst-carry二分岐へ渡す比較を構成する。 -/
def PreparedCarryData.toCarryComparison
    {O : OddOrbit} {T : TerminalPairData}
    (P : PreparedCarryData O T) : CarryComparison where
  x := P.boundary.lowerFinish
  y := P.upperFinish
  d := P.remainingDepth
  e := P.boundary.nextExponent
  a := P.boundary.nextOddPart
  u := 3 ^ oddSteps P.boundary.word * P.ordered.oddPart
  difference := by
    simpa [PreparedCarryData.remainingDepth, Nat.mul_assoc] using
      P.upperDifference
  difference_odd := P.upperDifferenceOdd
  lower_factorization := P.boundary.lowerNextFactorization
  lower_odd := P.boundary.lowerNextOdd
  depth_le := P.boundary.remaining_le_next

/-- carry比較がterminal pairから同期構成されたことを完全に保存する。 -/
structure CarryOrigin
    (O : OddOrbit)
    (T : TerminalPairData)
    (C : CarryComparison) : Type where
  prepared : PreparedCarryData O T
  carry_eq : C = prepared.toCarryComparison

/-- first-carryが差の深さで捕捉される枝。 -/
structure CapturedCarry (C : CarryComparison) : Type where
  depth_lt : C.d < C.e
  oddPart : ℕ
  exactFactor :
    ExactTwoFactor (3 * C.y + 1) C.d oddPart

/-- 深さが等しく、carryが少なくとも1ビット持ち越される枝。 -/
structure DeferredCarry (C : CarryComparison) : Type where
  depth_eq : C.d = C.e
  quotient : ℕ
  extraFactor :
    3 * C.y + 1 = 2 ^ (C.d + 1) * quotient

/-- first-carry二分岐をデータ付きで得る。 -/
theorem carryComparison_split_nonempty
    (C : CarryComparison) :
    Nonempty (CapturedCarry C ⊕ DeferredCarry C) := by
  rcases first_carry_split
      C.depth_le
      C.difference
      C.difference_odd
      C.lower_factorization
      C.lower_odd with h | h
  · rcases h with ⟨hlt, b, hb⟩
    exact ⟨Sum.inl ⟨hlt, b, hb⟩⟩
  · rcases h with ⟨heq, q, hq⟩
    exact ⟨Sum.inr ⟨heq, q, hq⟩⟩

/-- first-carry分岐を古典選択で一つ取り出す。 -/
noncomputable def carryComparison_split
    (C : CarryComparison) :
    CapturedCarry C ⊕ DeferredCarry C :=
  Classical.choice (carryComparison_split_nonempty C)

/-- 無限列から選ぶ狭義単調な部分列添字。 -/
structure Subsequence where
  index : ℕ → ℕ
  index_strict : StrictMono index

/--
無限terminal抽出の第`n`項に付随する解析packet。
難しい抽出側が与えるのはordered完全差分だけであり、
軌道埋込み、同期prefix、prepared carryはsource cylinderから自動構成される。
-/
structure TerminalAnalysisPacket
    {O : OddOrbit}
    {S : C3CylinderSequence O}
    (E : InfiniteTerminalExtraction S)
    (n : ℕ) where
  ordered : OrderedDifferenceData (E.pair n)

namespace TerminalAnalysisPacket

/-- packetの元cylinder有限snapshot。 -/
def sourceCylinder
    {O : OddOrbit}
    {S : C3CylinderSequence O}
    {E : InfiniteTerminalExtraction S}
    {n : ℕ}
    (_P : TerminalAnalysisPacket E n) : CanonicalC3Witness :=
  (S.cylinder (E.sourceIndex n)).snapshot

/-- packetのterminal pair。 -/
def criticalPair
    {O : OddOrbit}
    {S : C3CylinderSequence O}
    {E : InfiniteTerminalExtraction S}
    {n : ℕ}
    (_P : TerminalAnalysisPacket E n) : TerminalPairData :=
  E.pair n

/-- terminal pair全体の語は元cylinder語である。 -/
theorem sourceRelation
    {O : OddOrbit}
    {S : C3CylinderSequence O}
    {E : InfiniteTerminalExtraction S}
    {n : ℕ}
    (P : TerminalAnalysisPacket E n) :
    P.criticalPair.A ++ P.criticalPair.R =
      P.sourceCylinder.word :=
  E.sourceRelation n

/-- terminal pair開始値は元cylinder開始値である。 -/
theorem sourceStart
    {O : OddOrbit}
    {S : C3CylinderSequence O}
    {E : InfiniteTerminalExtraction S}
    {n : ℕ}
    (P : TerminalAnalysisPacket E n) :
    P.criticalPair.X = P.sourceCylinder.start :=
  E.sourceStart n

/-- terminal pair終点は元cylinder終点である。 -/
theorem sourceFinish
    {O : OddOrbit}
    {S : C3CylinderSequence O}
    {E : InfiniteTerminalExtraction S}
    {n : ℕ}
    (P : TerminalAnalysisPacket E n) :
    P.criticalPair.YAR = P.sourceCylinder.finish :=
  E.sourceFinish n

/-- source cylinderから下側値`YA`の実軌道位置を自動取得する。 -/
def lowerOrbit
    {O : OddOrbit}
    {S : C3CylinderSequence O}
    {E : InfiniteTerminalExtraction S}
    {n : ℕ}
    (_P : TerminalAnalysisPacket E n) :
    TerminalLowerOrbitEmbedding O (E.pair n) :=
  terminalLowerOrbitEmbeddingOfExtraction E n

/-- ordered差分から最小同期境界を通じてprepared carryを構成する。 -/
noncomputable def prepared
    {O : OddOrbit}
    {S : C3CylinderSequence O}
    {E : InfiniteTerminalExtraction S}
    {n : ℕ}
    (P : TerminalAnalysisPacket E n) :
    PreparedCarryData O P.criticalPair :=
  PreparedCarryData.ofOrbit P.ordered P.lowerOrbit

/-- packetのprepared first-carry比較。 -/
noncomputable def carry
    {O : OddOrbit}
    {S : C3CylinderSequence O}
    {E : InfiniteTerminalExtraction S}
    {n : ℕ}
    (P : TerminalAnalysisPacket E n) : CarryComparison :=
  P.prepared.toCarryComparison

/-- carry比較のterminal由来。 -/
noncomputable def carryOrigin
    {O : OddOrbit}
    {S : C3CylinderSequence O}
    {E : InfiniteTerminalExtraction S}
    {n : ℕ}
    (P : TerminalAnalysisPacket E n) :
    CarryOrigin O P.criticalPair P.carry :=
  ⟨P.prepared, rfl⟩

/-- suffix実行からcanonical replay座標を自動構成する。 -/
def replayCoordinate
    {O : OddOrbit}
    {S : C3CylinderSequence O}
    {E : InfiniteTerminalExtraction S}
    {n : ℕ}
    (P : TerminalAnalysisPacket E n) :
    CanonicalReplayCoordinate
      P.criticalPair.R P.criticalPair.YA P.criticalPair.YAR :=
  canonicalReplayCoordinate_of_runs
    P.criticalPair.runR P.criticalPair.R_nonempty

/-- packetのsuffix開始値がcanonical代表から何回replayされたか。 -/
def replayQuotient
    {O : OddOrbit}
    {S : C3CylinderSequence O}
    {E : InfiniteTerminalExtraction S}
    {n : ℕ}
    (P : TerminalAnalysisPacket E n) : ℕ :=
  P.replayCoordinate.quotient

/-- packetに対するconnection方程式。 -/
theorem connectionEquation
    {O : OddOrbit}
    {S : C3CylinderSequence O}
    {E : InfiniteTerminalExtraction S}
    {n : ℕ}
    (P : TerminalAnalysisPacket E n) :
    (P.criticalPair.YAR : ℤ) -
        predecessorShadow P.criticalPair.R =
      2 * (3 : ℤ) ^ oddSteps P.criticalPair.R *
        ((P.replayQuotient : ℤ) + 1) :=
  P.replayCoordinate.connectionEquation

end TerminalAnalysisPacket

/-- 特殊C3へ残る前に現れる有限alternative exit候補。 -/
inductive AlternativeExitAt
    {O : OddOrbit}
    {S : C3CylinderSequence O}
    {E : InfiniteTerminalExtraction S}
    {n : ℕ}
    (P : TerminalAnalysisPacket E n) : Type
  | captureSuccess (h : CapturedCarry P.carry)
  | lowerNaturalReplay
      (h : LowerNaturalRunReplayData
        P.criticalPair.R P.criticalPair.YA P.criticalPair.YAR)
  | positivePredecessorShadow
      (h : 0 < predecessorShadow P.criticalPair.R)

/--
特殊C3へ残る有限項。

* prepared carryはdeferred
* suffix開始値はcanonical代表そのもの（replay quotient 0）
* 一つ下の合同代表に対応するshadowは負
-/
structure SpecialC3At
    {O : OddOrbit}
    {S : C3CylinderSequence O}
    {E : InfiniteTerminalExtraction S}
    {n : ℕ}
    (P : TerminalAnalysisPacket E n) : Type where
  deferredCarry : DeferredCarry P.carry
  canonicalBoundary : P.replayQuotient = 0
  negativePredecessorShadow :
    predecessorShadow P.criticalPair.R < 0

/-- canonical最小非負代表の終点は常に正。 -/
theorem canonicalEndpoint_positive
    (w : ExpWord) :
    0 < canonicalEnd w :=
  canonicalEnd_pos w

/-- canonical終点そのものをnegative shadowにする枝は不可能。 -/
theorem negativeCanonicalEndpoint_impossible
    (w : ExpWord) :
    ¬ ((canonicalEnd w : ℤ) < 0) := by
  exact not_lt_of_ge (by omega)

/-- predecessor shadowはzeroになれない。 -/
theorem predecessorShadow_zero_impossible
    (w : ExpWord) :
    predecessorShadow w ≠ 0 :=
  predecessorShadow_ne_zero w

/-- terminal pairの二つのcenterは常に異なる。 -/
theorem commonCenter_impossible
    {O : OddOrbit}
    {S : C3CylinderSequence O}
    {E : InfiniteTerminalExtraction S}
    {n : ℕ}
    (P : TerminalAnalysisPacket E n) :
    center P.criticalPair.A ≠ center P.criticalPair.R :=
  P.criticalPair.center_ne

/-- 各有限packetはalternative exit候補か修正後Special C3項へ落ちる。 -/
theorem analysisOutcome_nonempty
    {O : OddOrbit}
    {S : C3CylinderSequence O}
    {E : InfiniteTerminalExtraction S}
    {n : ℕ}
    (P : TerminalAnalysisPacket E n) :
    Nonempty (AlternativeExitAt P ⊕ SpecialC3At P) := by
  rcases carryComparison_split P.carry with hcap | hdefer
  · exact ⟨Sum.inl (AlternativeExitAt.captureSuccess hcap)⟩
  · by_cases hq : P.replayQuotient = 0
    · rcases lt_trichotomy
          (predecessorShadow P.criticalPair.R) 0 with
        hneg | hzero | hpos
      · exact ⟨Sum.inr ⟨hdefer, hq, hneg⟩⟩
      · exact False.elim
          ((predecessorShadow_zero_impossible P.criticalPair.R) hzero)
      · exact ⟨Sum.inl
          (AlternativeExitAt.positivePredecessorShadow hpos)⟩
    · have hqpos : 0 < P.replayQuotient :=
        Nat.pos_of_ne_zero hq
      exact ⟨Sum.inl
        (AlternativeExitAt.lowerNaturalReplay
          (P.replayCoordinate.lowerNaturalRunReplay
            P.criticalPair.runR hqpos))⟩

/-- 無限terminal部分列の全項へpacketを付与する。 -/
structure InfiniteTerminalAnalysis
    {O : OddOrbit}
    {S : C3CylinderSequence O}
    (E : InfiniteTerminalExtraction S) where
  packet : ∀ n : ℕ, TerminalAnalysisPacket E n

/-- capture成功が無限部分列上で持続する。 -/
structure InfiniteCapturedCarry
    {O : OddOrbit}
    {S : C3CylinderSequence O}
    {E : InfiniteTerminalExtraction S}
    (A : InfiniteTerminalAnalysis E) where
  select : Subsequence
  evidence : ∀ n : ℕ,
    CapturedCarry (A.packet (select.index n)).carry

/-- 一段下のactual natural runが無限部分列上で残る。 -/
structure InfiniteLowerNaturalReplay
    {O : OddOrbit}
    {S : C3CylinderSequence O}
    {E : InfiniteTerminalExtraction S}
    (A : InfiniteTerminalAnalysis E) where
  select : Subsequence
  evidence : ∀ n : ℕ,
    LowerNaturalRunReplayData
      (A.packet (select.index n)).criticalPair.R
      (A.packet (select.index n)).criticalPair.YA
      (A.packet (select.index n)).criticalPair.YAR

/-- predecessor shadowが正となる枝が無限に持続する。 -/
structure InfinitePositivePredecessorShadow
    {O : OddOrbit}
    {S : C3CylinderSequence O}
    {E : InfiniteTerminalExtraction S}
    (A : InfiniteTerminalAnalysis E) where
  select : Subsequence
  evidence : ∀ n : ℕ,
    0 < predecessorShadow
      (A.packet (select.index n)).criticalPair.R

/-- 修正後Special C3へ残らない第三の例外。 -/
inductive PersistentAlternativeExitData
    {O : OddOrbit}
    {S : C3CylinderSequence O}
    {E : InfiniteTerminalExtraction S}
    (A : InfiniteTerminalAnalysis E) : Type
  | captured (D : InfiniteCapturedCarry A)
  | lowerReplay (D : InfiniteLowerNaturalReplay A)
  | positivePredecessor (D : InfinitePositivePredecessorShadow A)

/-- 第三の例外：alternative exit候補が無限部分列上で持続する。 -/
def HasPersistentAlternativeExit : Prop :=
  ∃ O : OddOrbit,
  ∃ S : C3CylinderSequence O,
  ∃ E : InfiniteTerminalExtraction S,
  ∃ A : InfiniteTerminalAnalysis E,
    Nonempty (PersistentAlternativeExitData A)

end CollatzSecondLayer
