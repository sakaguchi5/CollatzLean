import CollatzLean.Collatz2.CSTMicro.DoubleDecomposition.CriticalHeightBeattyBridge
import CollatzLean.Collatz2.CSTMicro.DoubleDecomposition.CriticalDefectProfile
import CollatzLean.Collatz2.CSTMicro.DoubleDecomposition.RecordFerrersRowBandPhi
import CollatzLean.Collatz2.CSTMicro.DoubleDecomposition.RecordCarryCorrectionPhi
import CollatzLean.Collatz2.CSTMicro.DoubleDecomposition.GapOneParadoxical

/-!
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
