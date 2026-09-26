import CollatzLean.Collatz4.Family.QStart

/-!
# Collatz4.Family.Research

Collatz4 の研究対象を命題として固定する層。

対象はあくまで `A_n = 3*2^n-1` 族であり、一般の Collatz 予想ではない。
-/

namespace Collatz4.Family

/-- 研究対象の各開始値が1へ到達する、という族全体の収束命題。 -/
def FamilyConverges : Prop :=
  ∀ n : ℕ, 0 < n → Collatz4.Dynamics.Reaches (start n) 1

/-- 偶数添字だけに制限した族の収束命題。 -/
def EvenFamilyConverges : Prop :=
  ∀ n : ℕ, 0 < n → n % 2 = 0 → Collatz4.Dynamics.Reaches (start n) 1

end Collatz4.Family
