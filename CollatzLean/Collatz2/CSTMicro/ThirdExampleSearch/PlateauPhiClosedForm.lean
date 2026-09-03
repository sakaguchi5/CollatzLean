import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.RecordPlateauQOneMacro

/-!
# 第3例探索 次段 2: plateau Phi の閉形式

plateau 補正係数

  Phi(0)   = 0
  Phi(r+1) = 3 Phi(r) + 2^r

は、実は単純に

  Phi(r) = 3^r - 2^r

である。

これにより plateau の一括転送を、再帰定義を残さない純粋な冪等式へ落とせる。
-/

namespace Collatz2
namespace CSTMicro
namespace ThirdExampleSearch

/-- plateau 補正係数の exact closed form。 -/
theorem plateauPhi_eq_threePow_sub_twoPow
    (r : ℕ) :
    plateauPhi r = (3 : ℤ) ^ r - (2 : ℤ) ^ r := by
  induction r with
  | zero =>
      simp
  | succ r ih =>
      rw [plateauPhi_succ, ih, pow_succ, pow_succ]
      ring

end ThirdExampleSearch
end CSTMicro
end Collatz2
