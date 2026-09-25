import CollatzLean.Collatz4.Core.Forward
import CollatzLean.Collatz4.Core.Normalization
import CollatzLean.Collatz4.M7.Constants
import CollatzLean.Collatz4.M7.QBound
import CollatzLean.Collatz4.M7.LengthBound
import CollatzLean.Collatz4.M7.ForwardReduction
import CollatzLean.Collatz4.M7.LivePruning
import CollatzLean.Collatz4.M7.FiniteCertificate
import CollatzLean.Collatz4.M7.Exclusion

set_option linter.style.header false

/-!
# Collatz4

Collatz3 から独立した前向き有限状態アプローチ。

主結果:

`Collatz4.M7.no_m7_forward_candidate`

この集約ファイルは `CollatzLean.Collatz3.*` を一切 import しない。
-/
