import CollatzLean.Collatz3.Residue
import CollatzLean.Collatz3.Bridge.CountRunResidue
import CollatzLean.Collatz3.Bridge.ResidueDerived

/-!
# Collatz3 Bridge: Residue

R1 の 3進 residue arithmetic と actual `Runs` の接続、および fixed-depth 決定性をまとめる。

利用側で actual residue lift まで必要な場合は、このファイルだけを import すればよい。
-/
