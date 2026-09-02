import CollatzLean.Collatz2.CSTMicro.MultiCorner.LeftExposedCriticalizationDigitBridge
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.ChristoffelDefectValuation

/-!
# left exposed cut の normalized terminal residual

hard Case II では `a < s := criticalizationStart` である。
このとき `criticalizationLeftResidual a` を、実軌道の interval `[a,s)` の
通常の affine residual と同一視してはいけない。実際、通常の residual は
`3^(s-a)` を含む一方、既存定理により `criticalizationLeftResidual a` は
3 で割れない。

正しい exact bridge は terminal raw tail 側にある。既存の factorization

  T(a) = 3^(m-s) * R(a)

により、critical suffix が強制する `3^(m-s)` を terminal raw tail から
ちょうど除いた quotient は `R(a) = criticalizationLeftResidual a` そのものになる。
さらに `3 ∤ R(a)` なので `T(a)` の 3-adic order は exact に `m-s` で止まる。

したがって最初の非零 mod-3 digit は lossless に

  normalized terminal tail -> left residual -> criticalization boundary digit

と輸送される。
-/

namespace Collatz2
namespace CSTMicro

open ExternalArithmetic

namespace ExternalArithmetic
namespace PureBProfileObstruction

/--
`a ≤ criticalizationStart` なら terminal raw tail は critical suffix の
`3^(m-criticalizationStart)` で割れる。
-/
theorem threePow_criticalizationSuffix_dvd_terminalRawTail
    (P : PureBProfileObstruction)
    (a : ℕ)
    (ha : a ≤ P.criticalizationStart) :
    (3 : ℤ) ^ (P.m - P.criticalizationStart) ∣
      P.terminalRawTail a := by
  refine ⟨P.criticalizationLeftResidual a, ?_⟩
  exact P.terminalRawTail_eq_threePow_mul_criticalizationLeftResidual ha

/--
terminal raw tail から、critical suffix が強制する 3-power を除いた canonical quotient。

定義は divisibility witness の `Classical.choose` だが、次の定理でこの quotient が
既存の `criticalizationLeftResidual` と一意に一致することを示す。
-/
noncomputable def criticalizationNormalizedTerminalTail
    (P : PureBProfileObstruction)
    (a : ℕ)
    (ha : a ≤ P.criticalizationStart) : ℤ :=
  Classical.choose
    (P.threePow_criticalizationSuffix_dvd_terminalRawTail a ha)

/-- normalized terminal tail の defining factorization。 -/
theorem criticalizationNormalizedTerminalTail_spec
    (P : PureBProfileObstruction)
    (a : ℕ)
    (ha : a ≤ P.criticalizationStart) :
    P.terminalRawTail a =
      (3 : ℤ) ^ (P.m - P.criticalizationStart) *
        P.criticalizationNormalizedTerminalTail a ha := by
  exact Classical.choose_spec
    (P.threePow_criticalizationSuffix_dvd_terminalRawTail a ha)

/--
中心補題。
terminal raw tail から `3^(m-s)` を exact に除いた quotient は、
criticalization start state を左へ戻した residual `R_a` と一致する。
-/
theorem criticalizationNormalizedTerminalTail_eq_criticalizationLeftResidual
    (P : PureBProfileObstruction)
    (a : ℕ)
    (ha : a ≤ P.criticalizationStart) :
    P.criticalizationNormalizedTerminalTail a ha =
      P.criticalizationLeftResidual a := by
  have hQ := P.criticalizationNormalizedTerminalTail_spec a ha
  have hR :=
    P.terminalRawTail_eq_threePow_mul_criticalizationLeftResidual ha
  have hPowNe :
      (3 : ℤ) ^ (P.m - P.criticalizationStart) ≠ 0 := by
    exact pow_ne_zero _ (by norm_num)
  apply mul_left_cancel₀ hPowNe
  calc
    (3 : ℤ) ^ (P.m - P.criticalizationStart) *
          P.criticalizationNormalizedTerminalTail a ha =
        P.terminalRawTail a := hQ.symm
    _ =
        (3 : ℤ) ^ (P.m - P.criticalizationStart) *
          P.criticalizationLeftResidual a := hR

end PureBProfileObstruction
end ExternalArithmetic

namespace MultiCorner

/--
`3^r * u` で `u` が 3-adic unit なら、3-adic order は exact に `r`。
-/
private theorem exactThreeAdicOrder_threePow_mul_of_not_three_dvd
    (r : ℕ)
    (u : ℤ)
    (hu : ¬ (3 : ℤ) ∣ u) :
    ExactThreeAdicOrder ((3 : ℤ) ^ r * u) r := by
  constructor
  · refine ⟨u, rfl⟩
  · intro hDeep
    rcases hDeep with ⟨q, hq⟩
    have hPowNe : (3 : ℤ) ^ r ≠ 0 := by
      exact pow_ne_zero _ (by norm_num)
    have hEq :
        (3 : ℤ) ^ r * u =
          (3 : ℤ) ^ r * ((3 : ℤ) * q) := by
      calc
        (3 : ℤ) ^ r * u =
            (3 : ℤ) ^ (r + 1) * q := hq
        _ = (3 : ℤ) ^ r * ((3 : ℤ) * q) := by
          rw [pow_succ]
          ring
    have huEq : u = (3 : ℤ) * q :=
      mul_left_cancel₀ hPowNe hEq
    exact hu ⟨q, huEq⟩

/--
`a < criticalizationStart` では terminal raw tail の 3-adic order は
exact に `m-criticalizationStart`。

これは factorization の divisibility だけでなく、「次の 3 は割れない」まで含む。
-/
theorem terminalRawTail_exactThreeAdicOrder_of_leftCriticalization
    (P : PureBProfileObstruction)
    (hStart : 0 < P.criticalizationStart)
    {a : ℕ}
    (ha : a < P.criticalizationStart) :
    ExactThreeAdicOrder
      (P.terminalRawTail a)
      (P.m - P.criticalizationStart) := by
  have hFactor :=
    P.terminalRawTail_eq_threePow_mul_criticalizationLeftResidual
      (Nat.le_of_lt ha)
  have hUnit :=
    criticalizationLeftResidual_not_three_dvd P hStart ha
  rw [hFactor]
  exact
    exactThreeAdicOrder_threePow_mul_of_not_three_dvd
      (P.m - P.criticalizationStart)
      (P.criticalizationLeftResidual a)
      hUnit

/--
normalized terminal tail 自身も 3-adic unit。
従ってその `mod 3` class は 1 または 2 であり、消えない。
-/
theorem criticalizationNormalizedTerminalTail_not_three_dvd
    (P : PureBProfileObstruction)
    (hStart : 0 < P.criticalizationStart)
    {a : ℕ}
    (ha : a < P.criticalizationStart) :
    ¬ (3 : ℤ) ∣
      P.criticalizationNormalizedTerminalTail a (Nat.le_of_lt ha) := by
  rw [P.criticalizationNormalizedTerminalTail_eq_criticalizationLeftResidual
      a (Nat.le_of_lt ha)]
  exact criticalizationLeftResidual_not_three_dvd P hStart ha

/--
求めていた mod-3 bridge。

critical suffix の強制 3-power を terminal raw tail から除いた normalized residual の
最初の非零 digit が、そのまま criticalization boundary digit を決める：

  boundaryDigit = -2^β(a) * normalizedTail    in ZMod 3.
-/
theorem criticalizationBoundaryDigit_eq_neg_normalizedTerminalTail
    (P : PureBProfileObstruction)
    (hStart : 0 < P.criticalizationStart)
    {a : ℕ}
    (ha : a < P.criticalizationStart) :
    criticalizationBoundaryDigit P hStart =
      ((- (2 : ℤ) ^ beattyIndex a *
          P.criticalizationNormalizedTerminalTail a (Nat.le_of_lt ha) : ℤ) :
        ZMod 3) := by
  rw [P.criticalizationNormalizedTerminalTail_eq_criticalizationLeftResidual
      a (Nat.le_of_lt ha)]
  exact criticalizationBoundaryDigit_eq_neg_leftResidual P hStart ha

namespace LeftOfCriticalizationBridge

/--
Case II packet への直接 wrapper。
left exposed cut の normalized terminal tail が boundary digit を決める。
-/
theorem boundaryDigit_eq_left_normalizedTerminalTail
    {P : PureBProfileObstruction}
    (B : LeftOfCriticalizationBridge P) :
    criticalizationBoundaryDigit P B.hStart =
      ((- (2 : ℤ) ^ beattyIndex B.left.index *
          P.criticalizationNormalizedTerminalTail
            B.left.index
            (Nat.le_of_lt B.left.index_lt_criticalization) : ℤ) :
        ZMod 3) := by
  exact
    criticalizationBoundaryDigit_eq_neg_normalizedTerminalTail
      P B.hStart B.left.index_lt_criticalization

/--
Case II packet の left exposed cut で terminal raw tail の exact order を読む。
-/
theorem left_terminalRawTail_exactThreeAdicOrder
    {P : PureBProfileObstruction}
    (B : LeftOfCriticalizationBridge P) :
    ExactThreeAdicOrder
      (P.terminalRawTail B.left.index)
      (P.m - P.criticalizationStart) := by
  exact
    terminalRawTail_exactThreeAdicOrder_of_leftCriticalization
      P B.hStart B.left.index_lt_criticalization

end LeftOfCriticalizationBridge

end MultiCorner
end CSTMicro
end Collatz2
