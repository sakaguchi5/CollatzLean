import CollatzLean.Collatz4.Finite.FiniteReduction
import CollatzLean.Collatz4.Targets.M7.StructuralCompression
import CollatzLean.Collatz4.Targets.M7.Witness

set_option linter.style.nativeDecide false

/-!
# Collatz4.Targets.M7.StructuralResult

M=7 の新しい構造的 finite exclusion。

2179候補を直接すべて最終判定する代わりに、

1. 2179候補を97同期合流代表へ圧縮
2. 97代表を「純2冪58本」と「非2冪39本」に分離
3. 非2冪39本では終端2指数が
   `<= 10672` または `>= 11058`
4. 目標2指数 `10996` はその禁止帯内部

という形で目標状態を排除する。

従来の `FiniteCertificate` は独立した回帰検査として残す。
-/

namespace Collatz4.Targets.M7

open Collatz4.Dynamics
open Collatz4.Finite

/-- 先頭58代表を「純2冪代表」として97代表へ埋め込む。 -/
def powerRepresentativeEmbedding
    (r : Fin powerRepresentativeCount) :
    Fin compressionRepresentativeCount :=
  ⟨r.1, by
    have h := r.2
    simp [powerRepresentativeCount, compressionRepresentativeCount] at *
    omega⟩

/-- 後半39代表を97代表の index 58..96 へ埋め込む。 -/
def nonPowerRepresentativeEmbedding
    (r : Fin nonPowerRepresentativeCount) :
    Fin compressionRepresentativeCount :=
  ⟨r.1 + powerRepresentativeCount, by
    have h := r.2
    simp [nonPowerRepresentativeCount,
      powerRepresentativeCount, compressionRepresentativeCount] at *
    omega⟩

/--
最初の58代表は終端奇数部分が1、すなわち純粋な2の冪になる。
-/
theorem power_representative_certificate :
    ∀ r : Fin powerRepresentativeCount,
      (m7FinalStateCompression.representativeFinal
        (powerRepresentativeEmbedding r)).u = 1 := by
  native_decide

/--
後半39代表は終端奇数部分が1ではない。
従って `97 = 58 + 39` は純2冪 / 非2冪の実際の分割である。
-/
theorem nonPower_representative_certificate :
    ∀ r : Fin nonPowerRepresentativeCount,
      (m7FinalStateCompression.representativeFinal
        (nonPowerRepresentativeEmbedding r)).u ≠ 1 := by
  native_decide

/--
非2冪39代表の終端2指数には

`10673 .. 11057`

が一つも現れない。
-/
theorem nonPower_representative_gap_certificate :
    ∀ r : Fin nonPowerRepresentativeCount,
      let x := m7FinalStateCompression.representativeFinal
        (nonPowerRepresentativeEmbedding r)
      x.t ≤ 10672 ∨ 11058 ≤ x.t := by
  native_decide

/--
97代表のどれも M=7 の目標状態そのものにはならない。

前半58本は奇数部分 `u=1` で排除し、
後半39本は2指数禁止帯で排除する。
-/
theorem representative_final_ne_target
    (r : Fin compressionRepresentativeCount) :
    m7FinalStateCompression.representativeFinal r ≠ targetState := by
  by_cases hpower : r.1 < powerRepresentativeCount
  · let p : Fin powerRepresentativeCount := ⟨r.1, hpower⟩
    have hemb : powerRepresentativeEmbedding p = r := by
      apply Fin.ext
      rfl
    have hu := power_representative_certificate p
    rw [hemb] at hu
    intro htarget
    have hut := congrArg ForwardState.u htarget
    have hodd := one_lt_targetOdd
    simp [targetState] at hut
    omega
  · have hnon : powerRepresentativeCount ≤ r.1 := by omega
    let p : Fin nonPowerRepresentativeCount :=
      ⟨r.1 - powerRepresentativeCount, by
        have hr := r.2
        simp [nonPowerRepresentativeCount,
          powerRepresentativeCount, compressionRepresentativeCount] at *
        omega⟩
    have hemb : nonPowerRepresentativeEmbedding p = r := by
      apply Fin.ext
      dsimp [p, nonPowerRepresentativeEmbedding]
      omega
    have hgap := nonPower_representative_gap_certificate p
    rw [hemb] at hgap
    intro htarget
    have htt := congrArg ForwardState.t htarget
    simp [targetState, targetTwoExponent] at htt
    rcases hgap with hlo | hhi <;> omega

/--
新しい合流圧縮証明による M=7 forward candidate の非存在。

従来の2179候補直接 certificate を使わず、
97代表の `58 + 39` 分類だけから排除する。
-/
theorem no_m7_forward_candidate_via_compression :
    ¬ M7ForwardCandidate := by
  intro h
  rcases h with ⟨i, hi⟩
  let r := m7FinalStateCompression.representativeOf i
  have hrep :
      m7FinalStateCompression.representativeFinal r = targetState := by
    have hcompress := m7FinalStateCompression.final_eq_representative i
    exact hcompress.symm.trans hi
  exact representative_final_ne_target r hrep

/-- 構造的 finite exclusion から意味論的 `M7Witness` も排除できる。 -/
theorem no_m7_witness_via_compression :
    ¬ HasM7Witness := by
  exact Collatz4.Finite.no_witness_of_reduction
    hasM7Witness_reducesTo
    no_m7_forward_candidate_via_compression

end Collatz4.Targets.M7
