import CollatzLean.Collatz4.Targets.M7.MasterWitness

--import Mathlib.Tactic

/-!
# Collatz4.Targets.M7.MasterBridge

研究対象に近い命題

`OddQBranchReachable 7`

から、固定 record を仮定しない exact `M7MasterWitness` までを接続する。

このファイルで閉じる範囲は

`actual reachability -> exponent word -> terminal macro -> master equation`

まで。

`M7MasterWitness` から現在の固定 `M7Witness`
`(2401,29) / (13396,8455)` へ落とす定理は意図的にここへ入れない。
-/

namespace Collatz4.Targets.M7

open Collatz4.Dynamics
open Collatz4.Family
open Collatz4.Parametric

/-- 標準 branch point は常に `2 mod 3`。 -/
private theorem branchPoint_mod_three (M r : ℕ) :
    branchPoint M r % 3 = 2 := by
  let a : ℕ := 3 ^ r * 2 ^ (M - r)
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hmul :
      3 ^ (r + 1) * 2 ^ (M - r) = 3 * a := by
    dsimp [a]
    rw [pow_succ]
    ring
  have hre : 3 * a - 1 = 3 * (a - 1) + 2 := by
    omega
  unfold branchPoint
  rw [hmul, hre]
  simp [Nat.add_mod]

/-- 正の `N` では `Q_N` 自身が標準 branch point であることはない。 -/
private theorem qStart_ne_branchPoint_of_pos
    {N M r : ℕ}
    (hN : 0 < N) :
    qStart N ≠ branchPoint M r := by
  intro hEq
  have hmod := congrArg (fun x : ℕ => x % 3) hEq
  rw [qStart_mod_three_of_pos hN, branchPoint_mod_three] at hmod
  omega

/--
`OddQBranchReachable 7` から exact M=7 master witness を構成する。

reachability の step 数が0ではないことを `mod 3` で示し、最後の1 step を取り出す。
その最後の step から `BranchTerminalMacroData` が `q` を復元する。
-/
theorem masterWitness_of_oddQBranchReachable :
    Collatz4.Parametric.OddQBranchReachable 7 →
      HasM7MasterWitness := by
  intro hreach
  rcases hreach with ⟨N, hNodd, hQ⟩
  rcases hQ with ⟨r, hr, hNr⟩
  rcases hNr with ⟨k, hk⟩
  have hNpos : 0 < N := by omega
  have hkne : k ≠ 0 := by
    intro hkzero
    subst k
    have hEq : qStart N = branchPoint 7 r := by
      simpa using hk
    exact qStart_ne_branchPoint_of_pos hNpos hEq
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hkne
  let z : ℕ := oddRun s (qStart N)
  have hlast : oddStep z = branchPoint 7 r := by
    have h := hk
    rw [oddRun_succ_last] at h
    simpa [z] using h
  let terminal := branchTerminalMacroData_of_hit hlast
  refine ⟨{
    N := N
    branch := r
    prefixSteps := s
    predecessor := z
    q := terminal.q
    N_odd := hNodd
    branch_lt := hr
    q_pos := terminal.q_pos
    prefix_endpoint := by simp [z]
    terminal_hit := hlast
    terminal_exponent := terminal.exponent_eq
  }⟩

/-- 同じ bridge を implication ではなく reduction 名で公開する。 -/
theorem oddQBranchReachable7_reducesTo_master :
    Collatz4.Parametric.OddQBranchReachable 7 → HasM7MasterWitness :=
  masterWitness_of_oddQBranchReachable

end Collatz4.Targets.M7
