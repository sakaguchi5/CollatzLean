import CollatzLean.Collatz3.Bridge.Experimental2Beatty
import CollatzLean.Collatz3.Bridge.Experimental2Profile
import CollatzLean.Collatz3.Bridge.Experimental2Record

set_option linter.style.header false

/-!
# Collatz3 Bridge: Experimental2 Collatz realization

Experimental2 の generic unit-carry / mechanical roof kernel を、
現行 Collatz3 の Critical / Ferrers 正本へ接続する入口。

この bridge では新しい primitive data を導入しない。

1. `Critical.beattyIndex` が generic `HasUnitCarry` を実現する。
2. admissible `profileHeight` が generic roof path を実現する。
3. `RecordFerrers` の canonical Beatty factorization が generic carry budget を実現する。

これにより、Beatty carry・local failure・terminal minimality・Record carry budget は
個別の現象ではなく Experimental2 の一般 theorem の Collatz specialization として読める。

実数 slope の具体値 `log₂ 3` の同定はこのファイルでは行わない。
現段階で必要なのは「Beatty roof が unique mechanical slope を持つ」ことまでであり、
対数との analytic identification は独立 bridge として後から追加できる。
-/
