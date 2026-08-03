import CollatzLean.CollatzSecondLayer.InfiniteTerminal
import CollatzLean.CollatzFirstLayer.DepthCoefficient

/-!
# 無限terminal解析と部分列分岐

terminal pairを一つだけ選ぶのではなく、無限terminal部分列の各項へ
first-carry・integer shadow・center解析packetを付与する。

その後、閉じる出口が無限部分列上で持続するか、特殊C3項の深さが
無限大へ進む部分列を抽出する。深さ発散は後者だけに要求する。
-/

namespace CollatzSecondLayer

open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

/-- 自然数に限定しない有限語のアフィン実現式。 -/
def RealizesInt (w : ExpWord) (x y : ℤ) : Prop :=
  (2 : ℤ) ^ twoSteps w * y =
    (3 : ℤ) ^ oddSteps w * x + affineConstInt w

/-- canonical開始値に対応する整数shadow。 -/
structure CanonicalShadowData (w : ExpWord) where
  shadow : ℤ
  realizes : RealizesInt w (canonicalStart w : ℤ) shadow

/-- first-carry二分岐を適用できる有限整数データ。 -/
structure CarryComparison where
  x : ℕ
  y : ℕ
  d : ℕ
  e : ℕ
  a : ℕ
  u : ℕ
  depth_le : d ≤ e
  difference : y = x + 2 ^ d * u
  difference_odd : Odd u
  lower_factorization : 3 * x + 1 = 2 ^ e * a
  lower_odd : Odd a

/-- carry比較がterminal pairの二つの実終点から作られたこと。 -/
structure CarryOrigin
    (T : TerminalPairData) (C : CarryComparison) : Prop where
  lowerValue : C.x = T.YA
  upperValue : C.y = T.YAR

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
元terminal pairとの由来は型引数と`CarryOrigin`で固定される。
-/
structure TerminalAnalysisPacket
    {O : OddOrbit}
    {S : C3CylinderSequence O}
    (E : InfiniteTerminalExtraction S)
    (n : ℕ) where
  carry : CarryComparison
  carryOrigin : CarryOrigin (E.pair n) carry
  shadow : CanonicalShadowData (E.pair n).R

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

end TerminalAnalysisPacket

/-- 特殊C3へ残る前に閉じる有限出口。zero/common-centerは下で不可能と証明する。 -/
inductive ClosedExitAt
    {O : OddOrbit}
    {S : C3CylinderSequence O}
    {E : InfiniteTerminalExtraction S}
    {n : ℕ}
    (P : TerminalAnalysisPacket E n) : Type
  | captureSuccess (h : CapturedCarry P.carry)
  | positiveShadow (h : 0 < P.shadow.shadow)

/-- deferred carry・negative shadow・changing centerが同時に残る有限項。 -/
structure SpecialC3At
    {O : OddOrbit}
    {S : C3CylinderSequence O}
    {E : InfiniteTerminalExtraction S}
    {n : ℕ}
    (P : TerminalAnalysisPacket E n) : Type where
  deferredCarry : DeferredCarry P.carry
  negativeShadow : P.shadow.shadow < 0
  changingCenter :
    center P.criticalPair.A ≠ center P.criticalPair.R

/-- determinant非零なterminal suffixは空語ではない。 -/
lemma terminalPair_R_ne_nil (T : TerminalPairData) : T.R ≠ [] := by
  intro hnil
  apply T.detR_ne
  simp [hnil, determinant, oddSteps, twoSteps]

/-- 非空語のaffine定数は正。 -/
lemma affineConst_pos_of_ne_nil
    {w : ExpWord} (hne : w ≠ []) : 0 < affineConst w := by
  cases w with
  | nil => exact False.elim (hne rfl)
  | cons e w =>
      simp [affineConst]

/-- 整数版affine定数は、自然数版affine定数の整数キャストに一致する。 -/
@[simp]
lemma affineConstInt_eq_cast_affineConst
    (w : ExpWord) :
    affineConstInt w = (affineConst w : ℤ) := by
  induction w with
  | nil =>
      simp [affineConstInt, affineConst]
  | cons e w ih =>
      simp [affineConstInt, affineConst]

/--
非空語では、canonical開始値に対する整数affine式の右辺は正である。
-/
lemma canonical_affine_rhs_pos
    {w : ExpWord}
    (hne : w ≠ []) :
    0 <
      (3 : ℤ) ^ oddSteps w * (canonicalStart w : ℤ) +
        affineConstInt w := by
  have hBnat : 0 < affineConst w :=
    affineConst_pos_of_ne_nil hne
  have hB : 0 < affineConstInt w := by
    rw [affineConstInt_eq_cast_affineConst]
    exact_mod_cast hBnat
  have hpow_nonneg :
      0 ≤ (3 : ℤ) ^ oddSteps w := by
    exact pow_nonneg (by norm_num) _
  have hstart_nonneg :
      0 ≤ (canonicalStart w : ℤ) := by
    omega
  have hmul_nonneg :
      0 ≤
        (3 : ℤ) ^ oddSteps w *
          (canonicalStart w : ℤ) :=
    mul_nonneg hpow_nonneg hstart_nonneg
  exact add_pos_of_nonneg_of_pos hmul_nonneg hB

/-- canonical integer shadowはzeroになれない。 -/
theorem zeroShadow_impossible
    {O : OddOrbit}
    {S : C3CylinderSequence O}
    {E : InfiniteTerminalExtraction S}
    {n : ℕ}
    (P : TerminalAnalysisPacket E n) :
    P.shadow.shadow ≠ 0 := by
  intro hzero
  have hreal := P.shadow.realizes
  unfold RealizesInt at hreal
  rw [hzero, mul_zero] at hreal
  have hpos :
      0 <
        (3 : ℤ) ^ oddSteps P.criticalPair.R *
            (canonicalStart P.criticalPair.R : ℤ) +
          affineConstInt P.criticalPair.R :=
    canonical_affine_rhs_pos
      (terminalPair_R_ne_nil P.criticalPair)
  have hzero_rhs :
      (3 : ℤ) ^ oddSteps P.criticalPair.R *
            (canonicalStart P.criticalPair.R : ℤ) +
          affineConstInt P.criticalPair.R = 0 :=
    hreal.symm
  exact (ne_of_gt hpos) hzero_rhs

/-- terminal pairの二つのcenterは一致しない。 -/
theorem commonCenter_impossible
    {O : OddOrbit}
    {S : C3CylinderSequence O}
    {E : InfiniteTerminalExtraction S}
    {n : ℕ}
    (P : TerminalAnalysisPacket E n) :
    center P.criticalPair.A ≠ center P.criticalPair.R := by
  intro hcenter
  rcases P.criticalPair.centerDifference with ⟨kappa, hkappaOdd, hdiff⟩
  have hkappa : kappa ≠ 0 := by
    intro hk
    subst kappa
    rcases hkappaOdd with ⟨z, hz⟩
    omega
  have hkappaQ : (kappa : ℚ) ≠ 0 := by exact_mod_cast hkappa
  have htwo : (2 : ℚ) ^ P.criticalPair.lambdaA ≠ 0 := by
    norm_num
  have hdetA : (determinant P.criticalPair.A : ℚ) ≠ 0 := by
    exact_mod_cast P.criticalPair.detA_ne
  have hdetR : (determinant P.criticalPair.R : ℚ) ≠ 0 := by
    exact_mod_cast P.criticalPair.detR_ne
  have hquot :
      (((2 : ℚ) ^ P.criticalPair.lambdaA) * (kappa : ℚ)) /
          ((determinant P.criticalPair.A : ℚ) *
            (determinant P.criticalPair.R : ℚ)) ≠ 0 := by
    exact div_ne_zero (mul_ne_zero htwo hkappaQ) (mul_ne_zero hdetA hdetR)
  apply hquot
  rw [← hdiff, hcenter, sub_self]

/-- 各有限packetは閉じる出口か特殊C3項のどちらかへ落ちる。 -/
theorem analysisOutcome_nonempty
    {O : OddOrbit}
    {S : C3CylinderSequence O}
    {E : InfiniteTerminalExtraction S}
    {n : ℕ}
    (P : TerminalAnalysisPacket E n) :
    Nonempty (ClosedExitAt P ⊕ SpecialC3At P) := by
  rcases carryComparison_split P.carry with hcap | hdefer
  · exact ⟨Sum.inl (ClosedExitAt.captureSuccess hcap)⟩
  · rcases lt_trichotomy P.shadow.shadow 0 with hneg | hzero | hpos
    · exact ⟨Sum.inr ⟨hdefer, hneg, commonCenter_impossible P⟩⟩
    · exact False.elim ((zeroShadow_impossible P) hzero)
    · exact ⟨Sum.inl (ClosedExitAt.positiveShadow hpos)⟩

/--
無限terminal部分列の全項へpacketを付与する。
深さ非有界性は、特殊C3部分列を選んだ段階で保持する。
-/
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

/-- positive shadowが無限部分列上で持続する。 -/
structure InfinitePositiveShadow
    {O : OddOrbit}
    {S : C3CylinderSequence O}
    {E : InfiniteTerminalExtraction S}
    (A : InfiniteTerminalAnalysis E) where
  select : Subsequence
  evidence : ∀ n : ℕ,
    0 < (A.packet (select.index n)).shadow.shadow

/-- 特殊C3へ残らない第三の例外を、無限部分列として分類する。 -/
inductive PersistentAlternativeExitData
    {O : OddOrbit}
    {S : C3CylinderSequence O}
    {E : InfiniteTerminalExtraction S}
    (A : InfiniteTerminalAnalysis E) : Type
  | captured (D : InfiniteCapturedCarry A)
  | positive (D : InfinitePositiveShadow A)

/-- 第三の例外：閉じるはずの出口が無限部分列上で持続する。 -/
def HasPersistentAlternativeExit : Prop :=
  ∃ O : OddOrbit,
  ∃ S : C3CylinderSequence O,
  ∃ E : InfiniteTerminalExtraction S,
  ∃ A : InfiniteTerminalAnalysis E,
    Nonempty (PersistentAlternativeExitData A)

end CollatzSecondLayer
