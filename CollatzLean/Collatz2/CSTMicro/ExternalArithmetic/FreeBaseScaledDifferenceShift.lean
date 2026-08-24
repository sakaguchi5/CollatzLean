import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.FreeBaseMonotoneHenselRepeatArithmetic

/-!
# Free-base scaled difference の shift identity

repeated block の offset `r` で評価した scaled difference は、
両 endpoint を `r` だけ右へずらした entrance difference と definitionally 同じである。

  M_r(i,j,Delta) = M_0(i+r,j+r,Delta)

terminal-near repeat の右端値 `M_m` を既存の entrance-oriented theorem へ渡すための
名前付き bridge として固定する。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

namespace FreeBaseMonotoneHenselChain

/--
scaled difference の offset 評価は、両 endpoint を同じだけ shift した
entrance difference に exact に一致する。
-/
@[simp] theorem scaledDifference_eq_shifted_zero
    (C : FreeBaseMonotoneHenselChain)
    (i j Delta r : ℕ) :
    C.scaledDifference i j Delta r =
      C.scaledDifference (i + r) (j + r) Delta 0 := by
  unfold scaledDifference
  simp only [add_zero]

end FreeBaseMonotoneHenselChain

end ExternalArithmetic
end CSTMicro
end Collatz2
