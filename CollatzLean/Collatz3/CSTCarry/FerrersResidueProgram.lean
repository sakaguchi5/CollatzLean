import CollatzLean.Collatz3.CSTCarry.FerrersAffineBudget
import CollatzLean.Collatz3.CSTCarry.ProfileAffineBudgetBridge
import CollatzLean.Collatz3.CSTCarry.FerrersAffineResidueBridge
import CollatzLean.Collatz3.CSTCarry.CarryLiftQuotient
import CollatzLean.Collatz3.CSTCarry.FerrersResidueFrontier

/-!
# Collatz3 CSTCarry: Ferrers affine/residue program aggregate

この集約 import は次の proved chain を公開する。

1. `S = B_boundary - B_actual` の exact affine difference。
2. affine difference と binary start residue displacement の exact bridge。
3. 1-cell / finite Ferrers chain の residue displacement law。
4. final carry の `residue + 2^H * quotient` exact lift。
5. critical rows では quotient が `0/1` に限られ、任意幅 final-wrap 問題が
   `CriticalLiftZero` / complement budget positivity に exact に縮約されること。

未証明なのは最後の `CriticalLiftZero` 自体であり、ここでは仮定や theorem として捏造しない。
-/
