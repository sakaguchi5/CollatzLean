import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBIntegralCriticalTail

/-!
# criticalization start の直前 residue

`criticalizationStart = s` は、critical backward recurrence が整数のまま
terminal まで通る最左の cut である。

このファイルでは `s` における canonical integer state `Z_s` を薄い wrapper として
取り出し、`s-1` から同じ recurrence を始めるために必要な mod 3 residue が
成立しないことを示す。

重要なのは、これは actual exponent word が `s` から critical になるという主張ではない。
あくまで arithmetic criticalization の最小性を one-step residue に読み替える補題である。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

namespace PureBProfileObstruction

/--
`criticalizationStart` で始まる integral critical tail の canonical integer state。

依存引数を後段から隠し、境界 residue を通常の整数式として扱うための wrapper。
-/
def criticalizationStartStateInt
    (P : PureBProfileObstruction) : ℤ :=
  P.integralCriticalTailStateInt
    P.criticalizationStart_spec
    P.criticalizationStart
    le_rfl
    P.criticalizationStart_spec.1

/--
`criticalizationStart = s` の raw tail は exact に

  terminalRawTail(s) = 3^(m-s) * Z_s

と書ける。
-/
theorem terminalRawTail_criticalizationStart_eq_threePow_mul_state
    (P : PureBProfileObstruction) :
    P.terminalRawTail P.criticalizationStart =
      (3 : ℤ) ^ (P.m - P.criticalizationStart) *
        P.criticalizationStartStateInt := by
  unfold criticalizationStartStateInt
  exact
    P.integralCriticalTailStateInt_spec
      P.criticalizationStart_spec
      le_rfl
      P.criticalizationStart_spec.1

/--
正の `criticalizationStart = s` では、critical shadow を一段左へ延長するために
必要な residue は成立しない。

  3 ∤ 2^(β(s)-β(s-1)) * Z_s - 1.

もし右辺が 3 で割れれば raw-tail の one-step identity により
`3^(m-s+1) ∣ terminalRawTail(s-1)` となり、`s` の最小性に反する。
-/
theorem criticalizationStart_pred_not_integral_residue
    (P : PureBProfileObstruction)
    (hStart : 0 < P.criticalizationStart) :
    ¬ (3 : ℤ) ∣
      (2 : ℤ) ^
          (beattyIndex P.criticalizationStart -
            beattyIndex (P.criticalizationStart - 1)) *
        P.criticalizationStartStateInt - 1 := by
  intro hThree
  have hsLe : P.criticalizationStart ≤ P.m :=
    P.criticalizationStart_spec.1
  have hPredLtM : P.criticalizationStart - 1 < P.m := by
    omega
  have hRaw :=
    P.terminalRawTail_step_raw
      (s := P.criticalizationStart - 1)
      hPredLtM
  have hSucc :
      P.criticalizationStart - 1 + 1 = P.criticalizationStart := by
    omega
  rw [hSucc] at hRaw
  have hState :=
    P.terminalRawTail_criticalizationStart_eq_threePow_mul_state
  have hRawFactored :
      P.terminalRawTail (P.criticalizationStart - 1) =
        (3 : ℤ) ^ (P.m - P.criticalizationStart) *
          ((2 : ℤ) ^
              (beattyIndex P.criticalizationStart -
                beattyIndex (P.criticalizationStart - 1)) *
            P.criticalizationStartStateInt - 1) := by
    calc
      P.terminalRawTail (P.criticalizationStart - 1)
          =
        (2 : ℤ) ^
            (beattyIndex P.criticalizationStart -
              beattyIndex (P.criticalizationStart - 1)) *
            P.terminalRawTail P.criticalizationStart -
          (3 : ℤ) ^ (P.m - P.criticalizationStart) := hRaw
      _ =
        (3 : ℤ) ^ (P.m - P.criticalizationStart) *
          ((2 : ℤ) ^
              (beattyIndex P.criticalizationStart -
                beattyIndex (P.criticalizationStart - 1)) *
            P.criticalizationStartStateInt - 1) := by
              rw [hState]
              ring
  rcases hThree with ⟨u, hu⟩
  have hExp :
      P.m - (P.criticalizationStart - 1) =
        (P.m - P.criticalizationStart) + 1 := by
    omega
  have hPredDvd :
      (3 : ℤ) ^ (P.m - (P.criticalizationStart - 1)) ∣
        P.terminalRawTail (P.criticalizationStart - 1) := by
    refine ⟨u, ?_⟩
    calc
      P.terminalRawTail (P.criticalizationStart - 1)
          =
        (3 : ℤ) ^ (P.m - P.criticalizationStart) *
          ((2 : ℤ) ^
              (beattyIndex P.criticalizationStart -
                beattyIndex (P.criticalizationStart - 1)) *
            P.criticalizationStartStateInt - 1) := hRawFactored
      _ =
        (3 : ℤ) ^ (P.m - P.criticalizationStart) * (3 * u) := by
          rw [hu]
      _ =
        (3 : ℤ) ^ ((P.m - P.criticalizationStart) + 1) * u := by
          rw [pow_succ]
          ring
      _ =
        (3 : ℤ) ^ (P.m - (P.criticalizationStart - 1)) * u := by
          rw [← hExp]
  have hPred :
      IsIntegralCriticalTail P (P.criticalizationStart - 1) :=
    ⟨by omega, hPredDvd⟩
  have hMin := P.criticalizationStart_minimal hPred
  omega

end PureBProfileObstruction

end ExternalArithmetic
end CSTMicro
end Collatz2
