import CollatzLean.Collatz2.Mountain.MountainRunStandardParameterOdd
import CollatzLean.Collatz2.CSTMicro.MultiCorner.AttachedActualTerminalMountain
import CollatzLean.Collatz2.CSTMicro.MultiCorner.AttachedMountainParameterLeftIdentity
import CollatzLean.Collatz2.CSTMicro.MultiCorner.AttachedMountainParameterTerminalInverse

/-!
# MultiCorner attached branch: terminal mountain bridge 集約

この集約ファイルは次の四層を一括 import する。

1. `AttachedTwoCornerPacket.actualTerminalMountain`
   actual `Runs` の lossless interval を terminal mountain へ昇格。

2. `MountainRun.exists_standard_parameter_odd`
   standard mountain parameter `a` の exact equations と odd 性。

3. `AttachedTwoCornerPacket.mountainParameter_left_identity`
   left affine history と `a` の exact gluing。

4. `AttachedTwoCornerPacket.mountainParameter_terminal_inverse`
   terminal drop から `2^l | a*3^W-1` を抽出。

後段では同じ `a` を left Ferrers/profile quotient と right 2-adic inverse class の
共通 coordinate として使う。
-/
