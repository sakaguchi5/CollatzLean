import CollatzLean.Collatz2.CSTMicro.MultiCorner.CriticalizationBoundaryDigitZMod3
import CollatzLean.Collatz2.CSTMicro.MultiCorner.LeftOfCriticalizationBridge

/-!
# left exposed corner から criticalization boundary digit への exact bridge

`criticalizationStart = s`、その canonical integer state を `Z_s` とする。
任意の `a < s` に対して

  R_a := 2^(β(s)-β(a)) Z_s - Φ(a,s)

を left residual と定義する。

critical interval の最後の一セルだけを mod 3 で残すと

  Φ(a,s) ≡ 2^(β(s-1)-β(a))       (mod 3)

なので、既存の boundary identity と合わせて

  U ≡ -2^β(a) R_a                 (mod 3)

が得られる。

従って `U` が 3-adic unit であることから、`a < s` の全ての left residual も
3 で割れない。これは `a=s-1` だけの one-step failure を、criticalization より
左の任意 cut まで exact に transport した形である。

最後に `LeftOfCriticalizationBridge` の exposed provenance とこの arithmetic residue を
一つの theorem packet にまとめる。provenance の `localDefect / glueCarry` のどちらが
boundary digit `1 / 2` のどちらを強制するか、という最終対応そのものは現行 API からは
まだ導かず、未証明の対応を仮定しない。
-/

namespace Collatz2
namespace CSTMicro

open ExternalArithmetic

namespace ExternalArithmetic
namespace PureBProfileObstruction

/--
criticalization start state を任意の左 cut `a` まで critical recurrence で戻した raw residual。
整数可解性は仮定せず、整数式そのものとして定義する。
-/
noncomputable def criticalizationLeftResidual
    (P : PureBProfileObstruction)
    (a : ℕ) : ℤ :=
  (2 : ℤ) ^
      (beattyIndex P.criticalizationStart - beattyIndex a) *
      P.criticalizationStartStateInt -
    criticalIntervalPhiZ a P.criticalizationStart

/--
任意の interval `[a,s)` は terminal raw tail を exact に輸送する。

  T_a = 2^(β(s)-β(a)) T_s - 3^(m-s) Φ(a,s).
-/
theorem terminalRawTail_interval_raw
    (P : PureBProfileObstruction)
    {a s : ℕ}
    (has : a ≤ s)
    (hsm : s ≤ P.m) :
    P.terminalRawTail a =
      (2 : ℤ) ^ (beattyIndex s - beattyIndex a) *
          P.terminalRawTail s -
        (3 : ℤ) ^ (P.m - s) * criticalIntervalPhiZ a s := by
  have hPhi :=
    criticalIntervalPhiZ_concat
      (a := a) (c := s) (b := P.m) has hsm
  have hBetaAS : beattyIndex a ≤ beattyIndex s := by
    by_cases hEq : a = s
    · subst s
      exact le_rfl
    · exact le_of_lt (beattyIndex_strictMono (by omega))
  have hBetaSM : beattyIndex s ≤ beattyIndex P.m := by
    by_cases hEq : s = P.m
    · subst s
      exact le_rfl
    · exact le_of_lt (beattyIndex_strictMono (by omega))
  have hBetaSplit :
      beattyIndex P.m - beattyIndex a =
        (beattyIndex s - beattyIndex a) +
          (beattyIndex P.m - beattyIndex s) := by
    omega
  unfold terminalRawTail
  rw [hBetaSplit, pow_add, hPhi]
  ring

/-- raw tail at `a` は `3^(m-s)` と left residual の積になる。 -/
theorem terminalRawTail_eq_threePow_mul_criticalizationLeftResidual
    (P : PureBProfileObstruction)
    {a : ℕ}
    (ha : a ≤ P.criticalizationStart) :
    P.terminalRawTail a =
      (3 : ℤ) ^ (P.m - P.criticalizationStart) *
        P.criticalizationLeftResidual a := by
  have hsLe : P.criticalizationStart ≤ P.m :=
    P.criticalizationStart_spec.1
  have hRaw :=
    P.terminalRawTail_interval_raw ha hsLe
  have hState :=
    P.terminalRawTail_criticalizationStart_eq_threePow_mul_state
  rw [hState] at hRaw
  unfold criticalizationLeftResidual
  calc
    P.terminalRawTail a =
        (2 : ℤ) ^
            (beattyIndex P.criticalizationStart - beattyIndex a) *
            ((3 : ℤ) ^ (P.m - P.criticalizationStart) *
              P.criticalizationStartStateInt) -
          (3 : ℤ) ^ (P.m - P.criticalizationStart) *
            criticalIntervalPhiZ a P.criticalizationStart := hRaw
    _ =
        (3 : ℤ) ^ (P.m - P.criticalizationStart) *
          ((2 : ℤ) ^
              (beattyIndex P.criticalizationStart - beattyIndex a) *
              P.criticalizationStartStateInt -
            criticalIntervalPhiZ a P.criticalizationStart) := by
              ring

/--
`a < s` のとき critical interval の mod 3 class は最後の一セルだけで決まる。
-/
theorem three_dvd_criticalIntervalPhiZ_sub_lastCell
    (P : PureBProfileObstruction)
    {a : ℕ}
    (ha : a < P.criticalizationStart) :
    (3 : ℤ) ∣
      criticalIntervalPhiZ a P.criticalizationStart -
        (2 : ℤ) ^
          (beattyIndex (P.criticalizationStart - 1) - beattyIndex a) := by
  have haPrev : a ≤ P.criticalizationStart - 1 := by
    omega
  have hPrevLe :
      P.criticalizationStart - 1 ≤ P.criticalizationStart := by
    omega
  have hPhi :=
    criticalIntervalPhiZ_concat
      (a := a)
      (c := P.criticalizationStart - 1)
      (b := P.criticalizationStart)
      haPrev hPrevLe
  have hStartPos : 0 < P.criticalizationStart := by omega
  have hSucc :
      P.criticalizationStart - 1 + 1 = P.criticalizationStart := by
    omega
  have hCell :=
    criticalIntervalPhiZ_step_eq_one_stage8
      (P.criticalizationStart - 1)
  rw [hSucc] at hCell
  have hDist :
      P.criticalizationStart - (P.criticalizationStart - 1) = 1 := by
    omega
  rw [hDist, hCell] at hPhi
  norm_num at hPhi
  refine ⟨criticalIntervalPhiZ a (P.criticalizationStart - 1), ?_⟩
  rw [hPhi]
  ring

end PureBProfileObstruction
end ExternalArithmetic

namespace MultiCorner

/--
任意の `a < criticalizationStart` で boundary unit と left residual は

  U ≡ -2^β(a) R_a  (mod 3)

を満たす。これが left cut から boundary digit への exact residue transport。
-/
theorem criticalizationUnit_mod_three_eq_neg_leftResidual
    (P : PureBProfileObstruction)
    (hStart : 0 < P.criticalizationStart)
    {a : ℕ}
    (ha : a < P.criticalizationStart) :
    (3 : ℤ) ∣
      criticalizationUnit P hStart +
        (2 : ℤ) ^ beattyIndex a * P.criticalizationLeftResidual a := by
  have hUnit :=
    criticalizationUnit_mod_three_eq_pred_failure P hStart
  have hPhi :=
    P.three_dvd_criticalIntervalPhiZ_sub_lastCell ha
  have hBetaAPrev :
      beattyIndex a ≤ beattyIndex (P.criticalizationStart - 1) := by
    by_cases hEq : a = P.criticalizationStart - 1
    · rw [hEq]
    · exact le_of_lt (beattyIndex_strictMono (by omega))
  have hBetaAS :
      beattyIndex a ≤ beattyIndex P.criticalizationStart := by
    exact le_of_lt (beattyIndex_strictMono ha)
  have hBetaPrevS :
      beattyIndex (P.criticalizationStart - 1) ≤
        beattyIndex P.criticalizationStart := by
    exact le_of_lt (beattyIndex_strictMono (by omega))
  have hPowAPrev :
      (2 : ℤ) ^ beattyIndex a *
          (2 : ℤ) ^
            (beattyIndex (P.criticalizationStart - 1) - beattyIndex a) =
        (2 : ℤ) ^ beattyIndex (P.criticalizationStart - 1) := by
    rw [← pow_add]
    congr 1
    omega
  have hPowAS :
      (2 : ℤ) ^ beattyIndex a *
          (2 : ℤ) ^
            (beattyIndex P.criticalizationStart - beattyIndex a) =
        (2 : ℤ) ^ beattyIndex P.criticalizationStart := by
    rw [← pow_add]
    congr 1
    omega
  have hPowPrevS :
      (2 : ℤ) ^ beattyIndex (P.criticalizationStart - 1) *
          (2 : ℤ) ^
            (beattyIndex P.criticalizationStart -
              beattyIndex (P.criticalizationStart - 1)) =
        (2 : ℤ) ^ beattyIndex P.criticalizationStart := by
    rw [← pow_add]
    congr 1
    omega
  have hPhiScaled :
      (3 : ℤ) ∣
        (2 : ℤ) ^ beattyIndex a *
          (criticalIntervalPhiZ a P.criticalizationStart -
            (2 : ℤ) ^
              (beattyIndex (P.criticalizationStart - 1) - beattyIndex a)) :=
    dvd_mul_of_dvd_right hPhi _
  have hCorrection :
      (3 : ℤ) ∣
        (2 : ℤ) ^ beattyIndex (P.criticalizationStart - 1) -
          (2 : ℤ) ^ beattyIndex a *
            criticalIntervalPhiZ a P.criticalizationStart := by
    rcases hPhiScaled with ⟨u, hu⟩
    refine ⟨-u, ?_⟩
    calc
      (2 : ℤ) ^ beattyIndex (P.criticalizationStart - 1) -
          (2 : ℤ) ^ beattyIndex a *
            criticalIntervalPhiZ a P.criticalizationStart
          =
        - ((2 : ℤ) ^ beattyIndex a *
          (criticalIntervalPhiZ a P.criticalizationStart -
            (2 : ℤ) ^
              (beattyIndex (P.criticalizationStart - 1) - beattyIndex a))) := by
            rw [← hPowAPrev]
            ring
      _ = - (3 * u) := by rw [hu]
      _ = 3 * (-u) := by ring
  rcases hUnit with ⟨u, hu⟩
  rcases hCorrection with ⟨v, hv⟩
  refine ⟨u + v, ?_⟩
  unfold ExternalArithmetic.PureBProfileObstruction.criticalizationLeftResidual
  calc
    criticalizationUnit P hStart +
        (2 : ℤ) ^ beattyIndex a *
          ((2 : ℤ) ^
              (beattyIndex P.criticalizationStart - beattyIndex a) *
              P.criticalizationStartStateInt -
            criticalIntervalPhiZ a P.criticalizationStart)
        =
      criticalizationUnit P hStart +
        ((2 : ℤ) ^ beattyIndex a *
          (2 : ℤ) ^
            (beattyIndex P.criticalizationStart - beattyIndex a)) *
          P.criticalizationStartStateInt -
        (2 : ℤ) ^ beattyIndex a *
          criticalIntervalPhiZ a P.criticalizationStart := by
            ring
    _ =
      criticalizationUnit P hStart +
        (2 : ℤ) ^ beattyIndex P.criticalizationStart *
          P.criticalizationStartStateInt -
        (2 : ℤ) ^ beattyIndex a *
          criticalIntervalPhiZ a P.criticalizationStart := by
            rw [hPowAS]
    _ =
      criticalizationUnit P hStart +
        ((2 : ℤ) ^ beattyIndex (P.criticalizationStart - 1) *
          (2 : ℤ) ^
            (beattyIndex P.criticalizationStart -
              beattyIndex (P.criticalizationStart - 1))) *
          P.criticalizationStartStateInt -
        (2 : ℤ) ^ beattyIndex a *
          criticalIntervalPhiZ a P.criticalizationStart := by
            rw [hPowPrevS]
    _ =
      (criticalizationUnit P hStart -
        (2 : ℤ) ^ beattyIndex (P.criticalizationStart - 1) *
          (1 -
            (2 : ℤ) ^
                (beattyIndex P.criticalizationStart -
                  beattyIndex (P.criticalizationStart - 1)) *
              P.criticalizationStartStateInt)) +
      ((2 : ℤ) ^ beattyIndex (P.criticalizationStart - 1) -
        (2 : ℤ) ^ beattyIndex a *
          criticalIntervalPhiZ a P.criticalizationStart) := by
            ring
    _ = 3 * u + 3 * v := by rw [hu, hv]
    _ = 3 * (u + v) := by ring

/--
上の整数合同式を `ZMod 3` へ移す。
任意の left cut の residual が boundary digit を完全に決める。
-/
theorem criticalizationBoundaryDigit_eq_neg_leftResidual
    (P : PureBProfileObstruction)
    (hStart : 0 < P.criticalizationStart)
    {a : ℕ}
    (ha : a < P.criticalizationStart) :
    criticalizationBoundaryDigit P hStart =
      ((- (2 : ℤ) ^ beattyIndex a * P.criticalizationLeftResidual a : ℤ) :
        ZMod 3) := by
  unfold criticalizationBoundaryDigit
  apply zmodThree_eq_of_sub_dvd
  have h := criticalizationUnit_mod_three_eq_neg_leftResidual P hStart ha
  convert h using 1
  ring

/--
boundary unit が非零なので、criticalization より左の全 residual も 3 で割れない。
-/
theorem criticalizationLeftResidual_not_three_dvd
    (P : PureBProfileObstruction)
    (hStart : 0 < P.criticalizationStart)
    {a : ℕ}
    (ha : a < P.criticalizationStart) :
    ¬ (3 : ℤ) ∣ P.criticalizationLeftResidual a := by
  intro hResidual
  have hProduct :
      (3 : ℤ) ∣
        (2 : ℤ) ^ beattyIndex a * P.criticalizationLeftResidual a :=
    dvd_mul_of_dvd_right hResidual _
  have hSum :=
    criticalizationUnit_mod_three_eq_neg_leftResidual P hStart ha
  have hUnit : (3 : ℤ) ∣ criticalizationUnit P hStart := by
    have hDiff := dvd_sub hSum hProduct
    simpa using hDiff
  exact criticalizationUnit_not_three_dvd P hStart hUnit

/--
従って left residual は、必要な全 `3^(s-a)` depth を持つこともできない。
これは minimality だけから得る結論より強い `3 ∤ R_a` を利用した wrapper。
-/
theorem criticalizationLeftResidual_not_full_threePow
    (P : PureBProfileObstruction)
    (hStart : 0 < P.criticalizationStart)
    {a : ℕ}
    (ha : a < P.criticalizationStart) :
    ¬ (3 : ℤ) ^ (P.criticalizationStart - a) ∣
      P.criticalizationLeftResidual a := by
  intro hDeep
  have hDepthPos : 0 < P.criticalizationStart - a := by omega
  let d := P.criticalizationStart - a - 1
  have hDepth : P.criticalizationStart - a = d + 1 := by
    dsimp [d]
    omega
  have hThreePow :
      (3 : ℤ) ∣ (3 : ℤ) ^ (P.criticalizationStart - a) := by
    refine ⟨(3 : ℤ) ^ d, ?_⟩
    rw [hDepth, pow_succ]
    ring
  have hThreeResidual :
      (3 : ℤ) ∣ P.criticalizationLeftResidual a :=
    hThreePow.trans hDeep
  exact criticalizationLeftResidual_not_three_dvd P hStart ha hThreeResidual

/-- Left bridge が見る exposed cut における canonical residual。 -/
noncomputable def LeftOfCriticalizationBridge.leftResidual
    {P : PureBProfileObstruction}
    (B : LeftOfCriticalizationBridge P) : ℤ :=
  P.criticalizationLeftResidual B.left.index

namespace LeftOfCriticalizationBridge

/-- left exposed cut の residual は mod 3 で非零。 -/
theorem leftResidual_not_three_dvd
    {P : PureBProfileObstruction}
    (B : LeftOfCriticalizationBridge P) :
    ¬ (3 : ℤ) ∣ B.leftResidual := by
  exact
    criticalizationLeftResidual_not_three_dvd
      P B.hStart B.left.index_lt_criticalization

/--
left exposed cut の residual から global boundary digit を直接復号する。
-/
theorem boundaryDigit_eq_neg_twoPow_mul_leftResidual
    {P : PureBProfileObstruction}
    (B : LeftOfCriticalizationBridge P) :
    criticalizationBoundaryDigit P B.hStart =
      ((- (2 : ℤ) ^ beattyIndex B.left.index * B.leftResidual : ℤ) :
        ZMod 3) := by
  exact
    criticalizationBoundaryDigit_eq_neg_leftResidual
      P B.hStart B.left.index_lt_criticalization

/--
Left Case II の現行 API から仮定なしで同時に読める最終 packet。

* exposed provenance は local defect / glue carry のどちらかを持つ;
* boundary digit は 1 / 2 の二値;
* left residual は 3-adic unit;
* boundary digit はその residual から exact に復号できる。

ここから先で必要なのは provenance branch と residual の具体的な同定だけである。
-/
theorem source_boundaryDigit_and_leftResidual
    {P : PureBProfileObstruction}
    (B : LeftOfCriticalizationBridge P) :
    (0 < B.left.provenance.localDefect ∨
      B.left.provenance.glueCarry = 1) ∧
    (criticalizationBoundaryDigit P B.hStart = 1 ∨
      criticalizationBoundaryDigit P B.hStart = 2) ∧
    (¬ (3 : ℤ) ∣ B.leftResidual) ∧
    criticalizationBoundaryDigit P B.hStart =
      ((- (2 : ℤ) ^ beattyIndex B.left.index * B.leftResidual : ℤ) :
        ZMod 3) := by
  constructor
  · exact B.left.source
  constructor
  · exact criticalizationBoundaryDigit_eq_one_or_two P B.hStart
  constructor
  · exact B.leftResidual_not_three_dvd
  · exact B.boundaryDigit_eq_neg_twoPow_mul_leftResidual

end LeftOfCriticalizationBridge

end MultiCorner
end CSTMicro
end Collatz2
