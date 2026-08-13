import CollatzLean.Collatz2.ObstructionAudit.ConstraintPackets
/-!
# Collatz2 Obstruction Audit: sharp kappa-one model

`kappa = 1` 自体が primitive affine arithmetic では矛盾を生まないことを、
全点 `kappa = 1` の明示的無限 model で固定する。

この model は word profile を要求しない。
-/

namespace Collatz2
namespace ObstructionAudit
namespace SharpKappaOneModel

def startValue (n : ℕ) : ℕ := 4 * n + 3
def oddCoeff (_n : ℕ) : ℕ := 3
def twoCoeff (_n : ℕ) : ℕ := 4
def translate (n : ℕ) : ℕ := 4 * n + 19

def coordinate (n : ℕ) : ℕ := n
def returnGap (_n : ℕ) : ℕ := 4
def centerContent (_n : ℕ) : ℕ := 1
def denominator (_n : ℕ) : ℕ := 1
def primitiveGap (_n : ℕ) : ℕ := 1
def alpha (n : ℕ) : ℕ := n + 4
def kappa (_n : ℕ) : ℤ := 1

def primitivePacket : PrimitiveReturnGapConstraints where
  startValue := startValue
  oddCoeff := oddCoeff
  twoCoeff := twoCoeff
  translate := translate

  start_gt_one := by
    intro n
    simp [startValue]
  start_strict := by
    intro a b hab
    simp [startValue]
    omega

  positive_return := by
    intro n
    simp [startValue]

  realizes := by
    intro n
    simp [twoCoeff, startValue, oddCoeff, translate]
    ring

  negative := by
    intro n
    norm_num [oddCoeff, twoCoeff]

  coordinate := coordinate
  returnGap := returnGap
  centerContent := centerContent
  denominator := denominator
  primitiveGap := primitiveGap
  alpha := alpha
  kappa := kappa

  start_coordinate := by
    intro n
    simp [startValue, coordinate]

  returnGap_spec := by
    intro n
    simp [startValue, returnGap]
    omega

  centerGap_factor := by
    intro n
    norm_num [twoCoeff, oddCoeff, centerContent, denominator]

  returnGap_factor := by
    intro n
    norm_num [returnGap, centerContent, primitiveGap]

  centerContent_pos := by
    intro n
    norm_num [centerContent]

  denominator_pos := by
    intro n
    norm_num [denominator]

  primitiveGap_pos := by
    intro n
    norm_num [primitiveGap]

  centerContent_odd := by
    intro n
    exact ⟨0, by norm_num [centerContent]⟩

  denominator_odd := by
    intro n
    exact ⟨0, by norm_num [denominator]⟩

  primitiveGap_coprime_denominator := by
    intro n
    norm_num [primitiveGap, denominator]

  translate_center_normal_form := by
    intro n
    simp [translate, centerContent, denominator, alpha]
    ring

  alpha_start_coordinate := by
    intro n
    simp [alpha, denominator, coordinate, twoCoeff, primitiveGap]

  alpha_end_coordinate := by
    intro n
    simp [alpha, denominator, coordinate, oddCoeff, primitiveGap]

  kappa_center_cross := by
    intro n
    simp [kappa, denominator, alpha]

  kappa_gap_balance := by
    intro n
    norm_num [kappa, denominator, twoCoeff, oddCoeff, primitiveGap]

def positivePacket : PositiveKappaConstraints where
  toPrimitiveReturnGapConstraints := primitivePacket

  kappa_pos := by
    intro n
    change (0 : ℤ) < kappa n
    norm_num [kappa]

  center_escape := by
    intro M
    refine ⟨M, ?_⟩
    change
      M * denominator M <
        3 * denominator M + 4 * alpha M
    simp [denominator, alpha]
    omega

def packet : SharpKappaOneConstraints where
  toPositiveKappaConstraints := positivePacket

  kappa_eq_one := by
    intro n
    rfl

/--
`kappa = 1` を全点に課しても primitive affine packet は inhabitant を持つ。
-/
theorem constraints_satisfiable :
    Nonempty SharpKappaOneConstraints :=
  ⟨packet⟩

end SharpKappaOneModel
end ObstructionAudit
end Collatz2
