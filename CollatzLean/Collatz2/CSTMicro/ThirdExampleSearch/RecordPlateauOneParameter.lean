import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.RecordPlateauLocalMacro
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.PlateauPhiClosedForm
import Mathlib.Data.Int.GCD
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.LinearCombination

/-!
# 第3例探索 次段 3: plateau を一つの整数パラメータへ圧縮

長さ `r`、一定 Hensel gap `delta` の plateau では、閉形式を使うと

  3^r (Q_L - 2^delta) = 2^r (Q_R - 2^delta)

となる。
`2^r` と `3^r` は互いに素なので、一つの整数 `t` が存在して

  Q_L = 2^delta + 2^r t
  Q_R = 2^delta + 3^r t

と書ける。

したがって plateau 内部の全状態を保持する必要はなく、両端は一つの `t` だけで決まる。
-/

namespace Collatz2
namespace CSTMicro
namespace ThirdExampleSearch

/--
一括転送を中心化すると `2^delta` を固定点とする純粋な `3^r : 2^r` 比になる。
-/
theorem recordPlateau_centered_endpoint_eq
    (Q : ℕ → ℤ)
    (delta i r : ℕ)
    (hMacro :
      (3 : ℤ) ^ r * Q i =
        (2 : ℤ) ^ r * Q (i + r) +
          (2 : ℤ) ^ delta * plateauPhi r) :
    (3 : ℤ) ^ r * (Q i - (2 : ℤ) ^ delta) =
      (2 : ℤ) ^ r * (Q (i + r) - (2 : ℤ) ^ delta) := by
  rw [plateauPhi_eq_threePow_sub_twoPow] at hMacro
  linear_combination hMacro

/--
plateau の両端は一つの整数 `t` で exact にパラメータ化できる。
`2^r` と `3^r` の互いに素性まで内部で証明するため、追加の divisibility 仮定は不要。
-/
theorem recordPlateau_exists_oneParameter
    (Q : ℕ → ℤ)
    (delta i r : ℕ)
    (hMacro :
      (3 : ℤ) ^ r * Q i =
        (2 : ℤ) ^ r * Q (i + r) +
          (2 : ℤ) ^ delta * plateauPhi r) :
    ∃ t : ℤ,
      Q i = (2 : ℤ) ^ delta + (2 : ℤ) ^ r * t ∧
      Q (i + r) = (2 : ℤ) ^ delta + (3 : ℤ) ^ r * t := by
  have hCentered :=
    recordPlateau_centered_endpoint_eq Q delta i r hMacro
  have hBase : IsCoprime (2 : ℤ) 3 := by
    exact Int.isCoprime_iff_gcd_eq_one.mpr (by decide)
  have hCoprime :
      IsCoprime ((2 : ℤ) ^ r) ((3 : ℤ) ^ r) := by
    exact (hBase.pow_left (m := r)).pow_right (n := r)
  have hDivMul :
      (2 : ℤ) ^ r ∣
        (3 : ℤ) ^ r * (Q i - (2 : ℤ) ^ delta) := by
    refine ⟨Q (i + r) - (2 : ℤ) ^ delta, ?_⟩
    exact hCentered
  have hDiv :
      (2 : ℤ) ^ r ∣ Q i - (2 : ℤ) ^ delta :=
    hCoprime.dvd_of_dvd_mul_left hDivMul
  rcases hDiv with ⟨t, ht⟩
  have hTwoNe : (2 : ℤ) ^ r ≠ 0 := by
    exact pow_ne_zero _ (by norm_num)
  have hRightCentered :
      Q (i + r) - (2 : ℤ) ^ delta =
        (3 : ℤ) ^ r * t := by
    apply mul_left_cancel₀ hTwoNe
    calc
      (2 : ℤ) ^ r * (Q (i + r) - (2 : ℤ) ^ delta) =
          (3 : ℤ) ^ r * (Q i - (2 : ℤ) ^ delta) :=
        hCentered.symm
      _ = (3 : ℤ) ^ r * ((2 : ℤ) ^ r * t) := by
        rw [ht]
      _ = (2 : ℤ) ^ r * ((3 : ℤ) ^ r * t) := by
        ring
  refine ⟨t, ?_, ?_⟩
  · calc
      Q i = (Q i - (2 : ℤ) ^ delta) + (2 : ℤ) ^ delta := by ring
      _ = (2 : ℤ) ^ r * t + (2 : ℤ) ^ delta := by rw [ht]
      _ = (2 : ℤ) ^ delta + (2 : ℤ) ^ r * t := by ring
  · calc
      Q (i + r) =
          (Q (i + r) - (2 : ℤ) ^ delta) + (2 : ℤ) ^ delta := by ring
      _ = (3 : ℤ) ^ r * t + (2 : ℤ) ^ delta := by
        rw [hRightCentered]
      _ = (2 : ℤ) ^ delta + (3 : ℤ) ^ r * t := by ring

/--
局所 plateau recurrence から直接、一変数パラメータ化まで到達する探索用 wrapper。
-/
theorem recordPlateau_local_exists_oneParameter
    (Q : ℕ → ℤ)
    (delta i r : ℕ)
    (hStep : ∀ s : ℕ, s < r →
      3 * Q (i + s) =
        2 * Q (i + s + 1) + (2 : ℤ) ^ delta) :
    ∃ t : ℤ,
      Q i = (2 : ℤ) ^ delta + (2 : ℤ) ^ r * t ∧
      Q (i + r) = (2 : ℤ) ^ delta + (3 : ℤ) ^ r * t := by
  apply recordPlateau_exists_oneParameter Q delta i r
  exact recordPlateau_qOne_macro_local Q delta i r hStep

end ThirdExampleSearch
end CSTMicro
end Collatz2
