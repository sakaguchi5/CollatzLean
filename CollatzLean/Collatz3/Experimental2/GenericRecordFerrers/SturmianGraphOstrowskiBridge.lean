import CollatzLean.Collatz3.Experimental2.GenericRecordFerrers.SturmianGraph
import CollatzLean.Collatz3.Experimental2.GenericRecordFerrers.RotationOstrowskiSystem

/-!
# Collatz3 Experimental2: generic Ostrowski system と Sturmian graph の exact 接続

前ファイル `SturmianGraph` は 2012 年論文 Definition 6 の infinite semi-normalized
Sturmian graph を `UnitOstrowskiWeightSystem` だけから構成した。

ここでは任意無理回転 `α` の `RotationOstrowskiSystem α` がすでに持つ
`horizontalWeights` を、そのまま Sturmian graph の partial quotient / arc-weight data
として使う。

重要なのは新しい数列を一切導入しないこと。

* graph block 幅 = `D.horizontalWeights.a`,
* graph arc weight = `D.horizontalWeights.Q`,
* horizontal canonical Ostrowski digits も同じ `D.horizontalWeights.Q`
  で自然数を復元する。

従って RecordFerrers が使っている horizontal Ostrowski 座標と、
Sturmian graph の weighted coordinate は同じ weight system 上に置かれる。

この段階では 2012 年 Theorem 47 の「unique path = lazy representation」までは仮定しない。
まず graph 本体と現行 repo の canonical coordinate が同じ continued-fraction lattice を
共有することだけを axiom-free に固定する。
-/

namespace Collatz3
namespace Experimental2
namespace GenericRecordFerrers

namespace RotationOstrowskiSystem

/-- `D` に付随する Sturmian graph の arc relation。 -/
abbrev SturmianGraphArc
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (i j w : ℕ) : Prop :=
  IsSturmianArc D.horizontalWeights i j w

/-- `D` に付随する Sturmian graph の finite weighted path。 -/
abbrev SturmianGraphPath
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (i j N : ℕ) : Type :=
  SturmianPath D.horizontalWeights i j N

/-- 初期状態から weight `N` を持つ `D`-Sturmian path certificate。 -/
abbrev InitialSturmianGraphPathOfWeight
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (N : ℕ) : Type :=
  InitialSturmianPathOfWeight D.horizontalWeights N

/--
Sturmian graph の第 `h` short arc weight は、horizontal convergent lattice の
対応する `P` 座標そのもの。
-/
theorem sturmianGraph_shortWeight_eq_convergentP
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (h : ℕ) :
    D.horizontalWeights.Q h =
      D.conv.P (D.horizontalIndex h) := by
  exact D.horizontalWeights_Q h

/--
Sturmian graph の第 `h` jump arc weight は、次の horizontal convergent `P` 座標。
-/
theorem sturmianGraph_jumpWeight_eq_nextConvergentP
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (h : ℕ) :
    D.horizontalWeights.Q (h + 1) =
      D.conv.P (D.horizontalIndex h + 1) := by
  exact D.horizontalWeights_Q_succ h

/--
Sturmian graph と共有する horizontal weight 上で digit prefix を評価する。

2012 年 Definition 46 の「weight `Q_i` の arc 本数を digit `d_i` と読む」側の
純粋な weighted-sum 部分だけを切り出したもの。
-/
def sturmianGraphCoordinateValue
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (d : ℕ → ℕ)
    (t : ℕ) : ℕ :=
  ostrowskiPrefixSum D.horizontalWeights.Q d t

/--
現行 horizontal canonical Ostrowski digits は、Sturmian graph と同じ arc-weight basis 上で
元の自然数 `N` を exact に復元する。
-/
theorem sturmianGraphCoordinateValue_horizontalDigits
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (N : ℕ) :
    D.sturmianGraphCoordinateValue
        (D.horizontalOstrowskiDigits N) (N + 1) = N := by
  exact D.horizontalOstrowskiDigits_reconstruct N

/--
canonical horizontal digits が持つ normal form も graph coordinate 上でそのまま保持される。

後段で greedy/canonical 座標から 2012 年の lazy path 座標へ変換するときの入口。
-/
theorem horizontalDigits_canonical_for_sturmianGraph
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (N : ℕ) :
    IsCanonicalOstrowskiDigits D.horizontalWeights
      (D.horizontalOstrowskiDigits N) := by
  exact D.horizontalOstrowskiDigits_canonical N

/-- `0` の Sturmian graph path certificate は canonical に存在する。 -/
def zeroInitialSturmianGraphPath
    {α : ℝ}
    (D : RotationOstrowskiSystem α) :
    D.InitialSturmianGraphPathOfWeight 0 :=
  zeroInitialSturmianPath D.horizontalWeights

end RotationOstrowskiSystem

end GenericRecordFerrers
end Experimental2
end Collatz3
