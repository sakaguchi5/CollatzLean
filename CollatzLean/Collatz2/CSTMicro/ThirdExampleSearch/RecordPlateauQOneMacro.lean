import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Tactic.Ring

/-!
# 第3例探索 4: Record plateau の Hensel 一括転送

局所 recurrence

  3 Q_i = 2 Q_(i+1) + 2^delta

を 1 step ずつ実行せず、長さ `r` の plateau 全体へまとめる。

補正項 `plateauPhi r` を

  Phi(0) = 0
  Phi(r+1) = 3 Phi(r) + 2^r

で定義すると

  3^r Q_i = 2^r Q_(i+r) + 2^delta Phi(r)

が exact に成り立つ。
-/

namespace Collatz2
namespace CSTMicro
namespace ThirdExampleSearch

/-- plateau 長 `r` に対する一括補正係数。 -/
def plateauPhi : ℕ → ℤ
  | 0 => 0
  | r + 1 => 3 * plateauPhi r + (2 : ℤ) ^ r

@[simp] theorem plateauPhi_zero : plateauPhi 0 = 0 := rfl

@[simp] theorem plateauPhi_succ (r : ℕ) :
    plateauPhi (r + 1) =
      3 * plateauPhi r + (2 : ℤ) ^ r := rfl

/--
同じ Hensel gap `delta` が続く plateau を `r` step まとめて飛ばす exact bridge。

この定理により、巨大 window の中央を 1 step ごとに走査する必要がなくなる。
-/
theorem recordPlateau_qOne_macro
    (Q : ℕ → ℤ)
    (delta i r : ℕ)
    (hStep : ∀ j : ℕ,
      3 * Q j = 2 * Q (j + 1) + (2 : ℤ) ^ delta) :
    (3 : ℤ) ^ r * Q i =
      (2 : ℤ) ^ r * Q (i + r) +
        (2 : ℤ) ^ delta * plateauPhi r := by
  induction r with
  | zero =>
      simp
  | succ r ih =>
      have hs := hStep (i + r)
      have hidx : i + (r + 1) = (i + r) + 1 := by omega
      calc
        (3 : ℤ) ^ (r + 1) * Q i =
            3 * ((3 : ℤ) ^ r * Q i) := by
              rw [pow_succ]
              ring
        _ = 3 *
            ((2 : ℤ) ^ r * Q (i + r) +
              (2 : ℤ) ^ delta * plateauPhi r) := by rw [ih]
        _ = (2 : ℤ) ^ r * (3 * Q (i + r)) +
              3 * (2 : ℤ) ^ delta * plateauPhi r := by ring
        _ = (2 : ℤ) ^ r *
              (2 * Q ((i + r) + 1) + (2 : ℤ) ^ delta) +
              3 * (2 : ℤ) ^ delta * plateauPhi r := by rw [hs]
        _ = (2 : ℤ) ^ (r + 1) * Q (i + (r + 1)) +
              (2 : ℤ) ^ delta * plateauPhi (r + 1) := by
                rw [hidx]
                simp only [plateauPhi_succ, pow_succ]
                ring

end ThirdExampleSearch
end CSTMicro
end Collatz2
