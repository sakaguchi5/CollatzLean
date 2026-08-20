import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBTerminalCoreValuation

/-!
# Pure B: terminal core の右端 carry decomposition

closed numerator

  C_n(h) = Σ_{k<n} (2^β_k - 2^(β_k-h_k)) 3^(n-k-1)

は右端 column を一つ剥がすと

  C_(n+1) = D_n + 3 C_n,
  D_n = 2^β_n - 2^(β_n-h_n)

と exact に再帰する。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/-- local terminal scale `n+1` での右端 column mass。 -/
def profileRightmostColumnMass
    (h : ℕ → ℕ)
    (n : ℕ) : ℕ :=
  2 ^ beattyIndex n - 2 ^ (beattyIndex n - h n)

/-- closed numerator の一段右 recursion。 -/
theorem profileDyadicClosedNumerator_succ_rightCarry
    (h : ℕ → ℕ)
    (n : ℕ) :
    profileDyadicClosedNumerator (n + 1) h =
      profileRightmostColumnMass h n +
        3 * profileDyadicClosedNumerator n h := by
  unfold profileDyadicClosedNumerator profileRightmostColumnMass
  rw [Finset.sum_range_succ]
  have hPrefix :
      Finset.sum (Finset.range n)
          (fun k => profileDyadicClosedColumn (n + 1) k (h k)) =
        3 *
          Finset.sum (Finset.range n)
            (fun k => profileDyadicClosedColumn n k (h k)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hkLt : k < n := Finset.mem_range.mp hk
    have hExp :
        n + 1 - (k + 1) = (n - (k + 1)) + 1 := by
      omega
    unfold profileDyadicClosedColumn
    rw [hExp, pow_succ]
    ring
  rw [hPrefix]
  have hLast :
      profileDyadicClosedColumn (n + 1) n (h n) =
        2 ^ beattyIndex n - 2 ^ (beattyIndex n - h n) := by
    unfold profileDyadicClosedColumn
    simp
  rw [hLast]
  omega

namespace PureBProfileObstruction

/-- terminal geometric start の直前にある last noncritical column mass。 -/
noncomputable def terminalLastColumnMass
    (P : PureBProfileObstruction) : ℕ :=
  profileRightmostColumnMass P.h (P.terminalCriticalStart - 1)

/-- terminal core を last column + 3 * previous core に exact 分解する。 -/
theorem terminalCore_rightCarryDecomposition
    (P : PureBProfileObstruction)
    (hcPos : 0 < P.terminalCriticalStart) :
    P.terminalNoncriticalProfileCore =
      P.terminalLastColumnMass +
        3 * profileDyadicClosedNumerator
          (P.terminalCriticalStart - 1) P.h := by
  have hc :
      P.terminalCriticalStart =
        (P.terminalCriticalStart - 1) + 1 := by
    omega
  unfold terminalNoncriticalProfileCore terminalLastColumnMass
  rw [hc]
  exact
    profileDyadicClosedNumerator_succ_rightCarry
      P.h (P.terminalCriticalStart - 1)

end PureBProfileObstruction

end ExternalArithmetic
end CSTMicro
end Collatz2
