import CollatzLean.Collatz3.Analysis.IrrationalRotationFourier
import CollatzLean.Collatz3.Analysis.IrrationalRotationCesaro
import CollatzLean.Collatz3.Analysis.IrrationalRotationRealCesaro

/-!
# Collatz3 Analysis: irrational rotation / Weyl–Cesàro package

Collatz から独立した無理回転の解析層。

* Fourier 1文字の exact 幾何級数平均
* Fourier span から任意の連続複素値関数への Weyl–Cesàro 拡張
* 実数値連続関数版

をまとめて import する。

この package 自体は 2021年論文の completion 議論も Collatz の定義も使用しない。
-/
