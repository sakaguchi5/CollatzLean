import CollatzLean.CollatzSecondLayer3.ConstantTerminalObstruction
import CollatzLean.CollatzSecondLayer3.SpecialC3ConstantTerminalNested
import CollatzLean.CollatzSecondLayer3.SpecialC3ConstantTerminalEndpointSplit
import CollatzLean.CollatzSecondLayer3.ContractingWindowBounds

/-!
# 新all-length Constant obstructionから既存Constant解析へのbridge

大型リファクタ後の主対象は`ConstantTerminalSpecialC3FamilyData`である。
一方、これまでに証明したnested center、one-bit alignment、carry/depth pattern、
endpoint exponent二分岐を捨てないため、この新対象から従来の
`FutureMinimumSpecialC3TowerData`と`ConstantTerminalNestedAlignmentData`を再構成する。

このbridgeは互換層であり、発散反例排除の主経路はgeneric obstructionや
terminal geometry三分岐を経由しない。
-/

namespace CollatzSecondLayer3

open CollatzCore

namespace FutureMinimumAllLengthTerminalData
namespace ConstantTerminalSpecialC3FamilyData

/--
Constant all-length familyを既存source-preserving Special C3 towerへ持ち上げる。
固定terminal startからの一般軌道評価によりdiscounted growth profileを自動付加する。
-/
noncomputable def toFutureMinimumSpecialC3TowerData
    {O : OddOrbit}
    {A : FutureMinimumAllLengthTerminalData O}
    (F : ConstantTerminalSpecialC3FamilyData A) :
    FutureMinimumSpecialC3TowerData O := by
  let K : ℕ := O.value (A.anchor + F.terminal) + 1
  refine
    { unbounded := A.unbounded
      anchor := A.anchor
      futureMinimum := A.futureMinimum
      select := F.select
      select_strict := F.select_strict
      normalization := fun j => A.normalization (F.select j)
      special := ?_
      lengths_tend_to_infinity := ?_
      growth := .discounted K 0 ?_ }
  · intro j
    have hs := Classical.choice (F.special j)
    simpa [
      FutureMinimumAllLengthTerminalData.IsSpecial,
      FutureMinimumAllLengthTerminalData.terminalStart,
      FutureMinimumAllLengthTerminalData.terminalTime,
      FutureMinimumAllLengthTerminalData.length
    ] using hs
  · intro M
    refine ⟨M, ?_⟩
    intro j hj
    have hsel : j ≤ F.select j :=
      nat_le_strictMono_apply F.select F.select_strict j
    omega
  · intro j
    have hterminal :
        (A.normalization (F.select j)).terminalTime = F.terminal := by
      simpa [FutureMinimumAllLengthTerminalData.terminalTime] using
        F.terminal_eq j
    let q := F.select j + 1
    let s := A.anchor + F.terminal
    have hOrbit :=
      OddOrbit.twoPow_mul_value_add_one_le_threePow O s q
    have hScaled :
        2 ^ q * O.value (s + q) ≤
          3 ^ q * (O.value s + 1) := by
      calc
        2 ^ q * O.value (s + q)
            ≤ 2 ^ q * (O.value (s + q) + 1) :=
          Nat.mul_le_mul_left _ (Nat.le_succ _)
        _ ≤ 3 ^ q * (O.value s + 1) := hOrbit
    change
      2 ^ (F.select j + 1) *
          O.value
            (A.anchor +
                (A.normalization (F.select j)).terminalTime +
              (F.select j + 1)) ≤
        (K * ((F.select j + 1) + 1) ^ 0) *
          3 ^ (F.select j + 1)
    rw [hterminal]
    simpa [K, q, s, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      hScaled

/-- 新Constant familyから作った旧tower。 -/
noncomputable def legacyTower
    {O : OddOrbit}
    {A : FutureMinimumAllLengthTerminalData O}
    (F : ConstantTerminalSpecialC3FamilyData A) :
    FutureMinimumSpecialC3TowerData O :=
  F.toFutureMinimumSpecialC3TowerData

/--
旧towerのterminal time列はfamily全体で既に定数なので、identity部分列を使える。
-/
noncomputable def legacyConstantSubsequence
    {O : OddOrbit}
    {A : FutureMinimumAllLengthTerminalData O}
    (F : ConstantTerminalSpecialC3FamilyData A) :
    ConstantNatSubsequenceData F.legacyTower.terminalTime where
  value := F.terminal
  select := fun n => n
  select_strict := by
    intro a b hab
    exact hab
  value_eq := by
    intro n
    change (A.normalization (F.select n)).terminalTime = F.terminal
    simpa [FutureMinimumAllLengthTerminalData.terminalTime] using
      F.terminal_eq n

/--
新Constant obstructionを、これまでのnested alignment解析へ直接接続する。
既存のsuffix transport / fixed depth pattern / endpoint splitを全て再利用できる。
-/
noncomputable def toNestedAlignmentData
    {O : OddOrbit}
    {A : FutureMinimumAllLengthTerminalData O}
    (F : ConstantTerminalSpecialC3FamilyData A) :
    FutureMinimumSpecialC3TowerData.ConstantTerminalNestedAlignmentData
      F.legacyTower :=
  FutureMinimumSpecialC3TowerData.ConstantTerminalNestedAlignmentData.ofConstant
    F.legacyTower
    F.legacyConstantSubsequence

end ConstantTerminalSpecialC3FamilyData
end FutureMinimumAllLengthTerminalData
end CollatzSecondLayer3
