import CollatzLean.Collatz3.Bridge.Experimental2Beatty
import CollatzLean.Collatz3.Bridge.Experimental2Profile
import CollatzLean.Collatz3.Bridge.Experimental2Record
import CollatzLean.Collatz3.Bridge.Experimental2BeattyNatLog
import CollatzLean.Collatz3.Bridge.Experimental2BeattyLog

set_option linter.style.header false

/-!
# Collatz3 Bridge: Experimental2 Collatz realization

Experimental2 の generic unit-carry / mechanical roof kernel を、
現行 Collatz3 の Critical / Ferrers 正本へ接続する入口。

この bridge では新しい primitive data を導入しない。

1. `Critical.beattyIndex` が generic `HasUnitCarry` を実現する。
2. admissible `profileHeight` が generic roof path を実現する。
3. `RecordFerrers` の canonical Beatty factorization が generic carry budget を実現する。
4. power-form `beattyIndex` は computable `Nat.log 2 (3^m)` と一致する。
5. その unique direct slope は exact に `Real.logb 2 3` であり、無理数である。
6. integer anchor `1` を除いた normalized slope は exact に `Real.logb 2 (3/2)` であり、
   一歩 Beatty carry はその irrational rotation の floor 差分になる。

これにより、Beatty carry・local failure・terminal minimality・Record carry budget に加え、
従来 power-form のまま保持していた Beatty roof の解析的意味まで、
Experimental2 の generic mechanical geometry と一本につながる。
-/
