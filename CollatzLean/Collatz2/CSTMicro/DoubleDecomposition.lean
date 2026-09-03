import CollatzLean.Collatz2.CSTMicro.DoubleDecomposition.CriticalHeightBeattyBridge
import CollatzLean.Collatz2.CSTMicro.DoubleDecomposition.CriticalDefectProfile
import CollatzLean.Collatz2.CSTMicro.DoubleDecomposition.RecordFerrersRowBandPhi
import CollatzLean.Collatz2.CSTMicro.DoubleDecomposition.RecordCarryCorrectionPhi
import CollatzLean.Collatz2.CSTMicro.DoubleDecomposition.GapOneParadoxical
import CollatzLean.Collatz2.CSTMicro.DoubleDecomposition.CriticalGapOneFerrersCertificate
import CollatzLean.Collatz2.CSTMicro.DoubleDecomposition.ActualRecordFerrersDeficit

/-
# RecordFerrers / Ostrowski-Christoffel 二重分解: 集約

同じ global interval に、役割の異なる二つの分解を重ねる。

* Record/Ferrers: defect geometry を「構成」する。
* Ostrowski/Christoffel: 同じ区間の重みを `Phi` として「計算」する。

この集約は両分解を同一視しない。両者が同じ affine/Ferrers budget へ写ることだけを使う。

収録する五段階:

1. `Word.criticalHeight = beattyIndex`
2. valid minimal crossing block と admissible critical defect profile の同値
3. integer Ferrers deficit と row-band shifted Phi sum の一致
4. Record carry correction = shifted Phi - origin Phi
5. Ferrers deficit equation から gap-one actual run への復元
-/

import CollatzLean.Collatz2.CSTMicro.DoubleDecomposition.ExactGapOneBeattyCertificate
import CollatzLean.Collatz2.CSTMicro.DoubleDecomposition.MaximalHorizontalBandCoarsening
import CollatzLean.Collatz2.CSTMicro.DoubleDecomposition.IndependentCriticalDefectInverse

/-
# 第3例探索 geometry: A/B/C 集約

A. terminal depth を `beattyIndex p + 1` に固定した真の gap-one certificate
B. unit-cell actual Ferrers deficit から maximal horizontal bands への exact coarsening
C. independent defect profile と exact-terminal minimal FirstCrossing word の逆構成

この3層により、巨大な exponent word を直接列挙せず、
独立 Ferrers profile -> maximal horizontal bands -> shifted Phi evaluation -> gap-one certificate
という探索経路を使えるようにする。
-/
