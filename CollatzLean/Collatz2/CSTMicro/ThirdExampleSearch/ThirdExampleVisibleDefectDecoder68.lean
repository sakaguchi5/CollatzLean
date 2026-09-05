import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.FerrersDeficitValuationPeeling


/-!
# 第3例探索 6: 最大68回の executable visible-defect decoder

前段の valuation-peeling を実行形へ落とす。
状態は

* 次に調べる column `cutoff`
* full deficit の残差 `mod 2^68`

だけを持つ。

非零 residual の 2進深さ `a < 68` を読み、`criticalHeight k > a` となる最初の
column を探す。その `(k,a)` を visible defect とし、その一列の affine difference を
`mod 2^68` で引いて次状態へ進む。

fuel は68に固定するため、巨大 target `p` に比例する loop は存在しない。
-/

namespace Collatz2
namespace CSTMicro
namespace ThirdExampleSearch

open FerrersDeficit

/-- 非零 Nat の 2進深さを `fuel` 以下で数える小核。 -/
def visibleTwoAdicDepthAux : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, n =>
      if n % 2 = 0 then
        1 + visibleTwoAdicDepthAux fuel (n / 2)
      else
        0

/-- `mod 2^68` の非零 residue から visible 2進深さを読む。 -/
def visibleTwoAdicDepth
    (x : ZMod thirdExampleLeftModulus) : Option ℕ := by
  letI : NeZero thirdExampleLeftModulus :=
    ⟨Nat.ne_of_gt thirdExampleLeftModulus_pos⟩
  exact if x = 0 then none else some (visibleTwoAdicDepthAux 68 x.val)

/-- `criticalHeight k > a` となる最初の index を有限 fuel で探す。 -/
def firstCriticalRoofAboveAux : ℕ → ℕ → ℕ → Option ℕ
  | _, _, 0 => none
  | cutoff, a, fuel + 1 =>
      if a < Word.criticalHeight cutoff then
        some cutoff
      else
        firstCriticalRoofAboveAux (cutoff + 1) a fuel

/-- visible height は68未満なので、最大68回だけ見る hot-path 版。 -/
def firstCriticalRoofAboveFrom (cutoff a : ℕ) : Option ℕ :=
  firstCriticalRoofAboveAux cutoff a 68

/-- visible defect 一列が full deficit に与える左 residue。 -/
def visibleDefectColumnModTwo
    (E : VisibleDefect) : ZMod thirdExampleLeftModulus :=
  (((2 : ZMod thirdExampleLeftModulus) ^ Word.criticalHeight E.index) -
      ((2 : ZMod thirdExampleLeftModulus) ^ E.height)) *
    ((3 : ZMod thirdExampleLeftModulus) ^
      (thirdExampleTargetP - (E.index + 1)))

/-- decoder の有限状態。 -/
@[ext]
structure ThirdExampleVisibleDecoderState where
  cutoff : ℕ
  residual : ZMod thirdExampleLeftModulus
  deriving DecidableEq, Repr

/-- 一段の valuation-peeling。 -/
def thirdExampleVisibleDecodeOne
    (S : ThirdExampleVisibleDecoderState) :
    Option (VisibleDefect × ThirdExampleVisibleDecoderState) :=
  match visibleTwoAdicDepth S.residual with
  | none => none
  | some a =>
      match firstCriticalRoofAboveFrom S.cutoff a with
      | none => none
      | some j =>
          if a < Word.criticalHeight j then
            let E : VisibleDefect := { index := j, height := a }
            some (E,
              { cutoff := j + 1
                residual := S.residual - visibleDefectColumnModTwo E })
          else
            none

/-- fuel 回だけ decoder を回す。residual が消えればその場で停止する。 -/
def thirdExampleVisibleDecodeFuel :
    ℕ → ThirdExampleVisibleDecoderState →
      List VisibleDefect × ThirdExampleVisibleDecoderState
  | 0, S => ([], S)
  | fuel + 1, S =>
      match thirdExampleVisibleDecodeOne S with
      | none => ([], S)
      | some (E, S') =>
          let R := thirdExampleVisibleDecodeFuel fuel S'
          (E :: R.1, R.2)

/-- target 用の最大68回 decoder。 -/
def thirdExampleVisibleDefectDecoder68
    (deficitModTwo : ZMod thirdExampleLeftModulus) :
    List VisibleDefect :=
  (thirdExampleVisibleDecodeFuel 68
    { cutoff := 0, residual := deficitModTwo }).1

/-- fuel 回 decoder の出力数は fuel を越えない。 -/
theorem thirdExampleVisibleDecodeFuel_length_le
    (fuel : ℕ)
    (S : ThirdExampleVisibleDecoderState) :
    (thirdExampleVisibleDecodeFuel fuel S).1.length ≤ fuel := by
  induction fuel generalizing S with
  | zero =>
      simp [thirdExampleVisibleDecodeFuel]
  | succ fuel ih =>
      simp only [thirdExampleVisibleDecodeFuel]
      cases h : thirdExampleVisibleDecodeOne S with
      | none =>
          simp only [List.length_nil, le_add_iff_nonneg_left, zero_le]
      | some P =>
          rcases P with ⟨E, S'⟩
          simp only [List.length_cons, add_le_add_iff_right, ih S']

/-- target decoder は最大68個しか entry を生成しない。 -/
theorem thirdExampleVisibleDefectDecoder68_length_le
    (d : ZMod thirdExampleLeftModulus) :
    (thirdExampleVisibleDefectDecoder68 d).length ≤ 68 := by
  unfold thirdExampleVisibleDefectDecoder68
  exact thirdExampleVisibleDecodeFuel_length_le 68
    { cutoff := 0, residual := d }

end ThirdExampleSearch
end CSTMicro
end Collatz2
