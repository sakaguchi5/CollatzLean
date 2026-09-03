import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.RecordPlateauQOneMacro

/-!
# 第3例探索 次段 1: Record plateau 一括転送の局所区間版

既存 `recordPlateau_qOne_macro` は recurrence を全 index に仮定していた。
探索器で必要なのは、実際に plateau が占める局所区間 `[i, i+r)` のみである。

このファイルでは仮定を

  ∀ s < r,
    3 Q_(i+s) = 2 Q_(i+s+1) + 2^delta

へ弱めても、同じ一括転送

  3^r Q_i = 2^r Q_(i+r) + 2^delta Phi(r)

が exact に成立することを示す。
-/

namespace Collatz2
namespace CSTMicro
namespace ThirdExampleSearch

/--
長さ `r` の plateau 内だけ recurrence が成立すれば十分である。
巨大な profile の外側に余計な条件を要求しない、探索向けの局所版。
-/
theorem recordPlateau_qOne_macro_local
    (Q : ℕ → ℤ)
    (delta i r : ℕ)
    (hStep : ∀ s : ℕ, s < r →
      3 * Q (i + s) =
        2 * Q (i + s + 1) + (2 : ℤ) ^ delta) :
    (3 : ℤ) ^ r * Q i =
      (2 : ℤ) ^ r * Q (i + r) +
        (2 : ℤ) ^ delta * plateauPhi r := by
  induction r with
  | zero =>
      simp
  | succ r ih =>
      have hPrefix : ∀ s : ℕ, s < r →
          3 * Q (i + s) =
            2 * Q (i + s + 1) + (2 : ℤ) ^ delta := by
        intro s hs
        exact hStep s (by omega)
      have hIH := ih hPrefix
      have hLast := hStep r (Nat.lt_succ_self r)
      have hIdx : i + (r + 1) = i + r + 1 := by omega
      calc
        (3 : ℤ) ^ (r + 1) * Q i =
            3 * ((3 : ℤ) ^ r * Q i) := by
              rw [pow_succ]
              ring
        _ = 3 *
            ((2 : ℤ) ^ r * Q (i + r) +
              (2 : ℤ) ^ delta * plateauPhi r) := by
              rw [hIH]
        _ = (2 : ℤ) ^ r * (3 * Q (i + r)) +
              3 * (2 : ℤ) ^ delta * plateauPhi r := by
              ring
        _ = (2 : ℤ) ^ r *
              (2 * Q (i + r + 1) + (2 : ℤ) ^ delta) +
              3 * (2 : ℤ) ^ delta * plateauPhi r := by
              rw [hLast]
        _ = (2 : ℤ) ^ (r + 1) * Q (i + (r + 1)) +
              (2 : ℤ) ^ delta * plateauPhi (r + 1) := by
              rw [hIdx]
              simp only [plateauPhi_succ, pow_succ]
              ring

end ThirdExampleSearch
end CSTMicro
end Collatz2
