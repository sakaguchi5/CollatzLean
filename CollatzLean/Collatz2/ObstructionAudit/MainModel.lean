import CollatzLean.Collatz2.ObstructionAudit.ConstraintPackets

/-!
# Collatz2 Obstruction Audit: main infinite model

primitive-center / return-gap / positive-kappa 条件に加え、
diagonal が `3^p / 2^H` 型で、word が exponent `1` から始まることまで
同時に無限反復できる明示 model を与える。

この model は最後の genuine word translation
`translate = Word.affineConst word` を意図的に要求しない。
-/

namespace Collatz2
namespace ObstructionAudit
namespace MainModel

def startValue (n : ℕ) : ℕ := 4 * n + 3
def oddCoeff (_n : ℕ) : ℕ := 9
def twoCoeff (_n : ℕ) : ℕ := 16
def translate (n : ℕ) : ℕ := 28 * n + 85

def coordinate (n : ℕ) : ℕ := n
def returnGap (_n : ℕ) : ℕ := 4
def centerContent (_n : ℕ) : ℕ := 1
def denominator (_n : ℕ) : ℕ := 7
def primitiveGap (_n : ℕ) : ℕ := 1
def alpha (n : ℕ) : ℕ := 7 * n + 16
def kappa (_n : ℕ) : ℤ := 49

def word (_n : ℕ) : Word := [1, 3]

def transfer (n : ℕ) : AffineTransfer :=
  { oddCoeff := oddCoeff n
    twoCoeff := twoCoeff n
    translate := translate n }

/-- 主 model の affine equation。 -/
theorem realizes_equation (n : ℕ) :
    twoCoeff n * startValue (n + 1) =
      oddCoeff n * startValue n + translate n := by
  simp [twoCoeff, startValue, oddCoeff, translate]
  ring

/-- 主 model は全点で negative determinant。 -/
theorem negative_everywhere (n : ℕ) :
    oddCoeff n < twoCoeff n := by
  norm_num [oddCoeff, twoCoeff]
  decide

/-- 主 model の actual return gap は常に4。 -/
theorem return_gap_four (n : ℕ) :
    startValue (n + 1) = startValue n + 4 := by
  simp [startValue]
  omega

/-- diagonal は `[1,3]` の genuine Collatz diagonal と一致する。 -/
theorem diagonal_matches_word (n : ℕ) :
    (transfer n).oddCoeff =
        (AffineTransfer.ofWord (word n)).oddCoeff ∧
      (transfer n).twoCoeff =
        (AffineTransfer.ofWord (word n)).twoCoeff := by
  constructor <;>
    norm_num [transfer, oddCoeff, twoCoeff, word,
      AffineTransfer.ofWord, Word.oddSteps, Word.twoSteps]

/-- primitive-center / return-gap 条件を全て満たす。 -/
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

  realizes := realizes_equation
  negative := negative_everywhere

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
    simpa [returnGap] using return_gap_four n

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
    exact ⟨3, by norm_num [denominator]⟩

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
    ring

  kappa_center_cross := by
    intro n
    simp [kappa, denominator, alpha]
    ring

  kappa_gap_balance := by
    intro n
    norm_num [kappa, denominator, twoCoeff, oddCoeff, primitiveGap]

/-- `kappa > 0` と center escape まで加えても model が存在する。 -/
def positivePacket : PositiveKappaConstraints where
  toPrimitiveReturnGapConstraints := primitivePacket

  kappa_pos := by
    intro n
    change (0 : ℤ) < kappa n
    norm_num [kappa]
    decide

  center_escape := by
    intro M
    refine ⟨M, ?_⟩
    change
      M * denominator M <
        3 * denominator M + 4 * alpha M
    simp [denominator, alpha]
    omega
/--
diagonal が `3^p / 2^H` 型で、word が exponent `1` から始まることまで加えても
無限 model が存在する。
-/
def packet : DiagonalWordProfileConstraints where
  toPositiveKappaConstraints := positivePacket

  word := word

  word_valid := by
    intro n e he
    simp only [word, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · omega
    · omega

  word_nonempty := by
    intro n
    simp [word]

  word_begins_one := by
    intro n
    exact ⟨[3], rfl⟩

  oddCoeff_eq_word := by
    intro n
    change oddCoeff n =
      (AffineTransfer.ofWord (word n)).oddCoeff
    norm_num [oddCoeff, word, AffineTransfer.ofWord,
      Word.oddSteps, Word.twoSteps]

  twoCoeff_eq_word := by
    intro n
    change twoCoeff n =
      (AffineTransfer.ofWord (word n)).twoCoeff
    norm_num [twoCoeff, word, AffineTransfer.ofWord,
      Word.oddSteps, Word.twoSteps]

/--
現在列挙した primitive-center / return-gap / positive-kappa /
diagonal-word-profile 条件群は inhabitant を持つ。
-/
theorem constraints_satisfiable :
    Nonempty DiagonalWordProfileConstraints :=
  ⟨packet⟩

end MainModel
end ObstructionAudit
end Collatz2
