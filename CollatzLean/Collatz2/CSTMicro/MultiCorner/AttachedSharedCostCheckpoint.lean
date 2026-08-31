import CollatzLean.Collatz2.CSTMicro.MultiCorner.AttachedSharedCostTransfer
import CollatzLean.Collatz2.CSTMicro.MultiCorner.AttachedEntranceDepthHensel

/-!
# MultiCorner attached branch: Shared-Cost checkpoint

ここまでの数学的整理を、最終排除定理の一歩手前の obligation としてまとめる。

attached の remaining problem は、terminal mountain 単体の存在を否定することではない。
`[1^(W-1), d]` 型 mountain 自体は整数軌道として存在し得る。
必要なのは Multi 固有の「二つの predecessor が同じ minimal bad word に入る」条件を使うこと。

この checkpoint が保持するものは三つ。

1. 共有 cost budget

     C₀, C₁ < G-q

   かつ double predecessor の carry/no-carry は

     C₀+C₁ < G-q

   と

     G-q < C₀+C₁

   の二側へ分かれる。

2. straight corridor transport

     G ∣ 3^W C₁ - 2^(W+rho) C₀.

3. entrance Hensel residue

     3^W ∣ 2^W + 2^h Phi.

したがって attached の最終数学問題は、

* 一個の interval `0 < C_j < G-q`,
* 一個の cost-sum threshold `G-q`,
* gap `G` 上の straight congruence,
* `3^W` 上の entrance-depth congruence

を同時に満たす二角 configuration が存在するか、という純算術問題になる。

このファイルでは「存在しない」とはまだ主張しない。
未証明の最終排除を axiom や placeholder theorem にしないことを意図している。
-/

namespace Collatz2
namespace CSTMicro
namespace MultiCorner

/--
Attached Shared-Cost Lemma を証明する直前までに必要な条件をまとめた packet。

`pair` と `transfer` は同じ数値を指すことを equality fields で明示する。
この形にしておくと、actual `AttachedTwoCornerPacket` からの constructor を後から追加しても、
純算術 kernel 自体を変更せずに済む。
-/
structure AttachedSharedCostCheckpoint where
  pair : AttachedSharedCostPair
  transfer : AttachedStraightCostTransfer
  hensel : AttachedEntranceHenselIdentity

  transfer_modulus_eq : transfer.modulus = pair.modulus
  transfer_gap_eq : transfer.gap = pair.gap
  transfer_cost0_eq : transfer.cost0 = pair.cost0
  transfer_cost1_eq : transfer.cost1 = pair.cost1
  transfer_delta0_eq : transfer.delta0 = pair.delta0
  transfer_delta1_eq : transfer.delta1 = pair.delta1
  transfer_weight0_eq : transfer.weight0 = pair.weight0
  transfer_weight1_eq : transfer.weight1 = pair.weight1

  cost0_pos : 0 < pair.cost0
  cost1_pos : 0 < pair.cost1

  single0_budget : pair.cost0 < pair.sharedBudget
  single1_budget : pair.cost1 < pair.sharedBudget

  doubleSafeNoCarry :
    pair.deltaSum ≤ pair.representativeThreshold →
      pair.normalizedQ - (pair.gap - pair.cost0) -
          (pair.gap - pair.cost1) + pair.gap < 0

namespace AttachedSharedCostCheckpoint

/--
checkpoint から Multi 固有の shared-budget 二分岐を取り出す。
-/
theorem sharedBudget_dichotomy
    (C : AttachedSharedCostCheckpoint) :
    (C.pair.deltaSum ≤ C.pair.representativeThreshold ∧
        C.pair.costSum < C.pair.sharedBudget) ∨
      (C.pair.representativeThreshold < C.pair.deltaSum ∧
        C.pair.sharedBudget < C.pair.costSum) := by
  exact C.pair.sharedCost_branch_dichotomy C.doubleSafeNoCarry

/--
checkpoint から straight corridor の cost congruence を、pair 側の変数で読む。

  G ∣ 3^W C₁ - 2^(W+rho) C₀.
-/
theorem straight_cost_congruence
    (C : AttachedSharedCostCheckpoint) :
    C.pair.gap ∣
      (3 : ℤ) ^ C.transfer.width * C.pair.cost1 -
        (2 : ℤ) ^ (C.transfer.width + C.transfer.rho) * C.pair.cost0 := by
  have h := C.transfer.gap_dvd_cost_transport
  rw [C.transfer_gap_eq, C.transfer_cost0_eq, C.transfer_cost1_eq] at h
  exact h

/--
checkpoint から entrance-depth Hensel congruenceを divisor form で読む。

  3^W ∣ 2^W + 2^h Phi.
-/
theorem entranceDepth_hensel_congruence
    (C : AttachedSharedCostCheckpoint) :
    (3 : ℤ) ^ C.hensel.width ∣
      (2 : ℤ) ^ C.hensel.width +
        (2 : ℤ) ^ C.hensel.entranceDepth * C.hensel.phi := by
  exact C.hensel.threePow_dvd_entranceResidue

def AttachedSharedCostArithmeticObligation
    (C : AttachedSharedCostCheckpoint) : Prop :=
  (((C.pair.deltaSum ≤ C.pair.representativeThreshold ∧
        C.pair.costSum < C.pair.sharedBudget) ∨
      (C.pair.representativeThreshold < C.pair.deltaSum ∧
        C.pair.sharedBudget < C.pair.costSum)) ∧
    (C.pair.gap ∣
      (3 : ℤ) ^ C.transfer.width * C.pair.cost1 -
        (2 : ℤ) ^ (C.transfer.width + C.transfer.rho) * C.pair.cost0) ∧
    ((3 : ℤ) ^ C.hensel.width ∣
      (2 : ℤ) ^ C.hensel.width +
        (2 : ℤ) ^ C.hensel.entranceDepth * C.hensel.phi))

/--
現在の attached 数学 checkpoint の三本柱を一度に取り出す。

これは最終 contradiction ではなく、次に証明すべき純算術 `Attached Shared-Cost Lemma` の
入力を明示するための theorem。
-/
theorem arithmetic_obligation
    (C : AttachedSharedCostCheckpoint) :
    AttachedSharedCostArithmeticObligation C := by
  exact ⟨C.sharedBudget_dichotomy,
    C.straight_cost_congruence,
    C.entranceDepth_hensel_congruence⟩

end AttachedSharedCostCheckpoint

end MultiCorner
end CSTMicro
end Collatz2
