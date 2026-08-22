import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBSingleCornerDefectRecurrence

/-!
# MultiCorner restarted branch: sole open arithmetic obligation

このファイルだけが未解決点を持つ。

数学的内容は Collatz から独立している。
`singleCornerDefect b w` は Beatty straight line と critical Beatty line の有限差であり、
full depth `3^w | defect` が成立した場合、その 3-adic order は exact に `w` で、
一段余分な `3^(w+1)` は割らない、という局所 Hensel rigidity。

今後はこの axiom 一個だけを、suffix quotient

  3 z_i = 2 z_(i+1) + 2^(h_i) - 1

と Beatty/Sturmian staircase の injectivity から置換する。
-/

namespace Collatz2
namespace CSTMicro
namespace MultiCorner

open ExternalArithmetic

/--
唯一の未証明補題。

TODO: finite 3-adic staircase encoding の injectivity から証明する。
-/
axiom singleCornerDefect_fullDepth_exact_threeAdicOrder
    {b w : ℕ}
    (hb : 0 < beattyIndex b)
    (hw : 0 < w)
    (hFull :
      (3 : ℤ) ^ w ∣ (singleCornerDefect b w : ℤ)) :
    ¬ (3 : ℤ) ^ (w + 1) ∣ (singleCornerDefect b w : ℤ)

end MultiCorner
end CSTMicro
end Collatz2
