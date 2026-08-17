import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.CriticalIntegerResidueSeparation

/-!
# López--Stoll corrected convergents: actual-family interface

abstract `LopezStollPacket` を、実際の continued-fraction index `j` に沿う
一族としてまとめる。

このファイルで actual family から要求するのは、文献側で本当に自然な data だけである。
特に `E_j` を「exact 2-adic valuation」として外部入力にはしない。
後段で使う certified precision budget は

  U_j = q_{j+1} + q_{j-1}

とこちらで選び、`packet.E := U_j` と定義する。
実際の corrected approximant がこの budget まで target と一致することは、
Boundary A 側の finite divisibility certificate が担う。

したがって actual instantiation に必要なのは各 `j` について

* continued-fraction denominator scale `q_j`,
* corrected numerator / denominator `P_j,Q_j`,
* `Q_j` は odd,
* `-P_j/Q_j` は nonnegative integer ではない,
* denominator sequence 自身が cofinal,

である。

odd convergent 側の sign branch と、
even convergent 側の mod-3 branch は
既存 pure-integer lemma で `ExcludesNonnegativeExact` に落とせる。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/--
López--Stoll corrected convergent family から必要な actual arithmetic data。

`start` は後段の height / Diophantine estimate が一様に使える index まで
有限個を捨ててよい。その具体的な大きさはこの interface では固定しない。
-/
structure LopezStollInstantiation where
  q : ℕ → ℕ
  P : ℕ → ℤ
  Q : ℕ → ℤ
  start : ℕ
  start_ge_three : 3 ≤ start

  /-- continued-fraction denominator は増加する。 -/
  q_mono : ∀ n : ℕ, q n ≤ q (n + 1)

  /-- denominator sequence 自身が `start` 以降 cofinal。 -/
  q_cofinal :
    ∀ N : ℕ, ∃ j : ℕ,
      start ≤ j ∧ N ≤ q j

  /-- denominator は 2-adic unit。非零性もここから従う。 -/
  Q_odd : ∀ j : ℕ, ¬ (2 : ℤ) ∣ Q j

  /--
  exact equality `R = -P_j/Q_j` は `R ≥ 0` では起こらない。

  odd `j` では sign、
  even `j` では corrected formula の mod-3 argument から入れる。
  -/
  exact_nonnegative_excluded :
    ∀ j : ℕ, ExcludesNonnegativeExact (P j) (Q j)

namespace LopezStollInstantiation

/-- `q_j` は chosen window upper endpoint 以下。 -/
theorem q_le_windowUpper
    (L : LopezStollInstantiation)
    (j : ℕ) :
    L.q j ≤ denominatorWindowUpper L.q j := by
  unfold denominatorWindowUpper
  have hmono : L.q j ≤ L.q (j + 1) := L.q_mono j
  omega

/-- `Q_j` は odd なので非零。 -/
theorem Q_ne_zero
    (L : LopezStollInstantiation)
    (j : ℕ) :
    L.Q j ≠ 0 := by
  intro hzero
  apply L.Q_odd j
  rw [hzero]
  exact dvd_zero _

/--
`q_j` 自身の cofinality から chosen precision window の upper endpoint の
cofinality を導く。
-/
theorem window_upper_cofinal
    (L : LopezStollInstantiation) :
    ∀ N : ℕ, ∃ j : ℕ,
      L.start ≤ j ∧
        N ≤ denominatorWindowUpper L.q j := by
  intro N
  rcases L.q_cofinal N with ⟨j, hjStart, hN⟩
  exact ⟨j, hjStart, le_trans hN (L.q_le_windowUpper j)⟩

/--
index `j` の corrected approximant を abstract packet へ落とす。

`E` は actual valuation ではなく、後段で安全に利用する certified window upper endpoint。
-/
def packet
    (L : LopezStollInstantiation)
    (j : ℕ) : LopezStollPacket := {
  q := L.q j
  E := denominatorWindowUpper L.q j
  P := L.P j
  Q := L.Q j
  q_le_E := L.q_le_windowUpper j
  Q_ne_zero := L.Q_ne_zero j
  denominatorOdd := L.Q_odd j
  exactNonnegativeExcluded := L.exact_nonnegative_excluded j
}

@[simp] theorem packet_q
    (L : LopezStollInstantiation) (j : ℕ) :
    (L.packet j).q = L.q j := rfl

@[simp] theorem packet_E
    (L : LopezStollInstantiation) (j : ℕ) :
    (L.packet j).E = denominatorWindowUpper L.q j := rfl

@[simp] theorem packet_P
    (L : LopezStollInstantiation) (j : ℕ) :
    (L.packet j).P = L.P j := rfl

@[simp] theorem packet_Q
    (L : LopezStollInstantiation) (j : ℕ) :
    (L.packet j).Q = L.Q j := rfl

/-- packet の certified precision budget は chosen window upper endpoint そのもの。 -/
theorem packet_precision
    (L : LopezStollInstantiation) (j : ℕ) :
    (L.packet j).E = denominatorWindowUpper L.q j := by
  rfl

/--
odd-convergent 側の sign argument から
`ExcludesNonnegativeExact` を作るための入口。
-/
theorem exactExcluded_of_positive_branch
    {P Q : ℤ}
    (hP : 0 < P)
    (hQ : 0 < Q) :
    ExcludesNonnegativeExact P Q :=
  excludesNonnegativeExact_of_pos hP hQ

/--
even-convergent 側の corrected right-gap formula で、
`3 ∣ Q` かつ `3 ∤ P` が出た場合の入口。
-/
theorem exactExcluded_of_modThree_branch
    {P Q : ℤ}
    (hQ : (3 : ℤ) ∣ Q)
    (hP : ¬ (3 : ℤ) ∣ P) :
    ExcludesNonnegativeExact P Q :=
  excludesNonnegativeExact_of_three_dvd_denominator hQ hP

end LopezStollInstantiation

end ExternalArithmetic
end CSTMicro
end Collatz2
