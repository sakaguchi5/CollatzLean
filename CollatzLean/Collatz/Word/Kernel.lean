import CollatzLean.Collatz.Word.Center

/-!
# 二return間の局所kernel

無限軌道を仮定せず、二つの有限return実現からomegaの2進因子を抽出する。
-/

namespace Collatz
namespace Word

/-- returnの総2進深さ。 -/
def returnDepth (w : Collatz.Word) (lambda : ℕ) : ℕ := w.twoSteps + lambda

/-- 二returnから現れるdefect kernel。 -/
def defectKernel (A B : Collatz.Word) (uA uB s : ℕ) : ℤ :=
  (uA : ℤ) * B.determinant -
    (2 : ℤ) ^ s * (uB : ℤ) * A.determinant

/-- 二return間のomega恒等式。 -/
theorem omega_from_two_returns
    {A B : Collatz.Word} {X YA YB lambdaA lambdaB uA uB : ℕ}
    (hA : A.Realizes X YA) (hB : B.Realizes X YB)
    (rA : IsReturn X YA lambdaA uA) (rB : IsReturn X YB lambdaB uB) :
    A.omega B =
      (2 : ℤ) ^ A.returnDepth lambdaA * (uA : ℤ) * B.determinant -
      (2 : ℤ) ^ B.returnDepth lambdaB * (uB : ℤ) * A.determinant := by
  have dA := hA.return_defect rA
  have dB := hB.return_defect rB
  unfold omega returnDepth
  calc
    A.affineConstInt * B.determinant - B.affineConstInt * A.determinant
        = (A.affineConstInt + A.determinant * (X : ℤ)) * B.determinant -
          (B.affineConstInt + B.determinant * (X : ℤ)) * A.determinant := by ring
    _ = ((2 : ℤ) ^ (A.twoSteps + lambdaA) * (uA : ℤ)) * B.determinant -
          ((2 : ℤ) ^ (B.twoSteps + lambdaB) * (uB : ℤ)) * A.determinant := by rw [dA, dB]
    _ = _ := by ring

/-- depth差` s `が既知なら前側2冪をくくり出せる。 -/
theorem terminal_factorization
    {A B : Collatz.Word} {X YA YB lambdaA lambdaB uA uB s : ℕ}
    (hA : A.Realizes X YA) (hB : B.Realizes X YB)
    (rA : IsReturn X YA lambdaA uA) (rB : IsReturn X YB lambdaB uB)
    (hgap : B.returnDepth lambdaB = A.returnDepth lambdaA + s) :
    A.omega B =
      (2 : ℤ) ^ A.returnDepth lambdaA * A.defectKernel B uA uB s := by
  rw [omega_from_two_returns hA hB rA rB]
  unfold defectKernel
  rw [hgap, pow_add]
  ring

end Word
end Collatz
