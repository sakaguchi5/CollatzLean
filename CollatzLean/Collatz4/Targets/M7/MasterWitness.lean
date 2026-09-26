import CollatzLean.Collatz4.Parametric.BranchTerminalMacro


/-!
# Collatz4.Targets.M7.MasterWitness

`OddQBranchReachable 7` から最初に得るべき、固定 record より上流の exact witness。

この層では `(2401,29)` や `(13396,8455)` を仮定しない。
保持するのは

* source `Q_N`
* M=7 branch の入口 `r<7`
* 最後の1 step の直前までの prefix 長 `s`
* その predecessor `z`
* terminal exponent `2q-1`

だけである。

prefix の exponent word、総2指数 `E`、affine 定数 `D` は定義から復元し、
master equation は derived theorem として証明する。
-/

namespace Collatz4.Targets.M7

open Collatz4.Dynamics
open Collatz4.Family
open Collatz4.Parametric

/-- M=7 reachability の exact master witness。 -/
structure M7MasterWitness where
  N : ℕ
  branch : ℕ
  prefixSteps : ℕ
  predecessor : ℕ
  q : ℕ
  N_odd : N % 2 = 1
  branch_lt : branch < 7
  q_pos : 0 < q
  prefix_endpoint :
    oddRun prefixSteps (qStart N) = predecessor
  terminal_hit :
    oddStep predecessor = branchPoint 7 branch
  terminal_exponent :
    stepExponent predecessor = 2 * q - 1

namespace M7MasterWitness

/-- actual prefix から復元した2指数 word。 -/
def prefixWord (h : M7MasterWitness) : List ℕ :=
  reachabilityWord h.prefixSteps (qStart h.N)

/-- prefix が消費する総2指数。 -/
def E (h : M7MasterWitness) : ℕ :=
  wordTwoExponent h.prefixWord

/-- `A=2*x+1` 座標での prefix affine 定数。 -/
def D (h : M7MasterWitness) : ℕ :=
  wordAffineConst h.prefixWord

@[simp] theorem prefixWord_length (h : M7MasterWitness) :
    h.prefixWord.length = h.prefixSteps := by
  simp [prefixWord, reachabilityWord_length]

/--
prefix の exact affine identity。

`A(Q_N)=3^N` を使って source を純粋な3冪へ正規化している。
-/
theorem prefix_affine (h : M7MasterWitness) :
    2 ^ h.E * lifted h.predecessor =
      3 ^ (h.N + h.prefixSteps) + h.D := by
  have hrun := oddRun_lifted_affine h.prefixSteps (qStart h.N)
  rw [h.prefix_endpoint] at hrun
  have hq := qStart_lifted h.N
  unfold E D prefixWord
  rw [hq] at hrun
  have hp : 3 ^ h.prefixSteps * 3 ^ h.N = 3 ^ (h.N + h.prefixSteps) := by
    calc
      3 ^ h.prefixSteps * 3 ^ h.N = 3 ^ (h.prefixSteps + h.N) := by
        rw [pow_add]
      _ = 3 ^ (h.N + h.prefixSteps) := by
        congr 1
        omega
  rw [hp] at hrun
  exact hrun

/-- terminal macro の exact identity。 -/
theorem terminal_macro (h : M7MasterWitness) :
    lifted h.predecessor + terminalGeom h.q =
      3 ^ h.branch * 2 ^ (7 - h.branch + 2 * h.q) := by
  have hdata := branchTerminalMacroData_of_hit h.terminal_hit
  have hq : hdata.q = h.q := by
    have h1 := hdata.exponent_eq
    have h2 := h.terminal_exponent
    have hp1 := hdata.q_pos
    have hp2 := h.q_pos
    omega
  simpa [hq] using hdata.terminal_eq

/--
M=7 reachability master equation。

`E = sum(prefix exponent word)`、`D = affineConst(prefix word)` とすると

`3^(N+s) + D + 2^E S_q = 3^r 2^(E + 7-r + 2q)`。

ここには固定 record `(2401,29)` / `(13396,8455)` はまだ現れない。
-/
theorem master_equation (h : M7MasterWitness) :
    3 ^ (h.N + h.prefixSteps) + h.D +
        2 ^ h.E * terminalGeom h.q =
      3 ^ h.branch * 2 ^ (h.E + (7 - h.branch) + 2 * h.q) := by
  have hprefix := h.prefix_affine
  have hterminal := h.terminal_macro
  calc
    3 ^ (h.N + h.prefixSteps) + h.D +
          2 ^ h.E * terminalGeom h.q =
        2 ^ h.E * lifted h.predecessor +
          2 ^ h.E * terminalGeom h.q := by
      rw [hprefix]
    _ = 2 ^ h.E *
          (lifted h.predecessor + terminalGeom h.q) := by
      ring
    _ = 2 ^ h.E *
          (3 ^ h.branch * 2 ^ (7 - h.branch + 2 * h.q)) := by
      rw [hterminal]
    _ = 3 ^ h.branch *
          (2 ^ h.E * 2 ^ (7 - h.branch + 2 * h.q)) := by
      ring
    _ = 3 ^ h.branch *
          2 ^ (h.E + (7 - h.branch + 2 * h.q)) := by
      have hpowAdd :
          2 ^ (h.E + (7 - h.branch + 2 * h.q)) =
            2 ^ h.E * 2 ^ (7 - h.branch + 2 * h.q) := by
        rw [pow_add]
      rw [hpowAdd]
    _ = 3 ^ h.branch *
          2 ^ (h.E + (7 - h.branch) + 2 * h.q) := by
      have hexp :
          h.E + (7 - h.branch + 2 * h.q) =
            h.E + (7 - h.branch) + 2 * h.q := by omega
      rw [hexp]

end M7MasterWitness

/-- M=7 master witness が存在するという命題。 -/
def HasM7MasterWitness : Prop :=
  Nonempty M7MasterWitness

end Collatz4.Targets.M7
