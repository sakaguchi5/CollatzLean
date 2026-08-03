import CollatzLean.CollatzFirstLayer.Orbit
import CollatzLean.CollatzFirstLayer.DepthCoefficient

/-!
# 第一層の監査用小定理

主要定義の向きと数値例を固定する。
このファイルに`axiom`、`sorry`、`admit`は置かない。
-/

namespace CollatzFirstLayer
open ExpWord

example : affineConst [1] = 1 := by norm_num [affineConst, oddSteps]
example : affineConst [1, 2] = 5 := by norm_num [affineConst, oddSteps]
example : twoSteps [1, 2] = 3 := by norm_num [twoSteps]
example : oddSteps [1, 2] = 2 := by norm_num [oddSteps]

example : Realizes [1, 2] 3 4 := by
  norm_num [Realizes, twoSteps, oddSteps, affineConst]

example : ExpWord.Runs [1, 1] 7 17 := by
  apply ExpWord.Runs.cons (y := 11)
  · norm_num
  · norm_num
  · exact ⟨5, by norm_num⟩
  · apply ExpWord.Runs.cons (y := 17)
    · norm_num
    · norm_num
    · exact ⟨8, by norm_num⟩
    · exact ExpWord.Runs.nil 17

example : determinant [1, 2] = 1 := by
  norm_num [determinant, twoSteps, oddSteps]

example : omega [1] [2] = -2 := by
  norm_num [omega, affineConstInt, determinant, affineConst, twoSteps, oddSteps]

/-- 深さ更新則を監査する最小データ。 -/
def sampleDepthCoefficientData : DepthCoefficientData where
  L := 2
  P := 1
  «λ» := 1
  «λnext» := 2
  t := 3
  u := 1
  unext := 1
  w := 5
  carryOddPart := 1
  transition := by norm_num
  carryFactorization := by norm_num
  unextOdd := by norm_num [Odd]
  carryOdd := by norm_num [Odd]

example :
    sampleDepthCoefficientData.«λ» + sampleDepthCoefficientData.t =
      sampleDepthCoefficientData.L + sampleDepthCoefficientData.«λnext» :=
  sampleDepthCoefficientData.depth_update

example :
    sampleDepthCoefficientData.unext =
      sampleDepthCoefficientData.carryOddPart :=
  sampleDepthCoefficientData.coefficient_update

end CollatzFirstLayer
