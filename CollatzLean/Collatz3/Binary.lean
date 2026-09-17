import CollatzLean.Collatz3.Binary.Basic
import CollatzLean.Collatz3.Binary.AlternatingWeight
import CollatzLean.Collatz3.Binary.Defect

-- B2: binary dynamics kernel
import CollatzLean.Collatz3.Binary.Deinterleave
import CollatzLean.Collatz3.Binary.Runs
import CollatzLean.Collatz3.Binary.Carry
import CollatzLean.Collatz3.Binary.RunResolution

-- R1: 3-adic binary statistics
import CollatzLean.Collatz3.Binary.ResidueWeight
import CollatzLean.Collatz3.Binary.ResidueSupport

/-!
# Collatz3 Binary

binary vocabulary / dynamics / residue statistics の集約 import。

この入口は actual Collatz `OddStep / Runs` semantics を import しない。
actual orbit との接続は Bridge 層に置く。
-/
