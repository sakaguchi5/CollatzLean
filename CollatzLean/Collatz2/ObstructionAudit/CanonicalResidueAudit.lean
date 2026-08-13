import CollatzLean.Collatz2.ObstructionAudit.ConstraintPackets
import CollatzLean.Collatz2.Canonical.Representative

/-!
# Collatz2 Obstruction Audit: canonical-residue boundary

exact word translation より弱い genuine-word consequence として、
各 start がその word の odd-endpoint canonical residue class に属する条件だけを戻す。

この条件を加えても relaxed infinite model が残ることを明示する。
従って canonical residue geometry 単独では obstruction にならない。
-/

namespace Collatz2
namespace ObstructionAudit

/-- genuine canonical start residue だけを diagonal word profile に追加した packet。 -/
structure CanonicalResidueConstraints extends DiagonalWordProfileConstraints where
  start_mod_eq_canonicalStart : ∀ n,
    startValue n % Word.residueModulus (word n) =
      Word.canonicalStart (word n)

namespace CanonicalResidueModel

/-- `word=[1,3]` の genuine canonical residue class を保つ relaxed model。 -/
def startValue (n : ℕ) : ℕ := 32 * n + 19
def oddCoeff (_n : ℕ) : ℕ := 9
def twoCoeff (_n : ℕ) : ℕ := 16
def translate (n : ℕ) : ℕ := 224 * n + 645

def coordinate (n : ℕ) : ℕ := 8 * n + 4
def returnGap (_n : ℕ) : ℕ := 32
def centerContent (_n : ℕ) : ℕ := 1
def denominator (_n : ℕ) : ℕ := 7
def primitiveGap (_n : ℕ) : ℕ := 8
def alpha (n : ℕ) : ℕ := 56 * n + 156
def kappa (_n : ℕ) : ℤ := 392

def word (_n : ℕ) : Word := [1, 3]

def witnessEnd (n : ℕ) : ℕ := 18 * n + 11

/-- relaxed affine equation。 -/
theorem realizes_equation (n : ℕ) :
    twoCoeff n * startValue (n + 1) =
      oddCoeff n * startValue n + translate n := by
  simp [twoCoeff, startValue, oddCoeff, translate]
  ring

/-- `[1,3]` の genuine affine realization が canonical residue 証明用 witness を与える。 -/
theorem genuine_word_realizes_witness (n : ℕ) :
    Word.Realizes (word n) (startValue n) (witnessEnd n) := by
  apply (Word.realizes_iff (word n) (startValue n) (witnessEnd n)).2
  norm_num [word, startValue, witnessEnd,
    Word.twoSteps, Word.oddSteps, Word.affineConst]
  ring

/-- witness endpoint は odd。 -/
theorem witnessEnd_odd (n : ℕ) : Odd (witnessEnd n) := by
  refine ⟨9 * n + 5, ?_⟩
  simp [witnessEnd]
  ring

/-- start は `[1,3]` の genuine canonical residue class に属する。 -/
theorem start_mod_eq_canonical (n : ℕ) :
    startValue n % Word.residueModulus (word n) =
      Word.canonicalStart (word n) := by
  exact
    (genuine_word_realizes_witness n).start_mod_eq_canonicalStart
      (witnessEnd_odd n)

/-- primitive-center / return-gap 条件。 -/
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
  negative := by
    intro n
    norm_num [oddCoeff, twoCoeff]
    decide
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
    ring
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
    exact ⟨3, by norm_num [denominator]⟩
  primitiveGap_coprime_denominator := by
    intro n
    norm_num [primitiveGap, denominator]
    decide
  translate_center_normal_form := by
    intro n
    simp [translate, centerContent, denominator, alpha]
    ring
  alpha_start_coordinate := by
    intro n
    simp [alpha, denominator, coordinate, twoCoeff, primitiveGap]
    ring
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

/-- `kappa>0` と center escape も維持する。 -/
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

/-- diagonal / begins-one profile も genuine `[1,3]` と一致する。 -/
def diagonalPacket : DiagonalWordProfileConstraints where
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
    change oddCoeff n = (AffineTransfer.ofWord (word n)).oddCoeff
    norm_num [oddCoeff, word, AffineTransfer.ofWord,
      Word.oddSteps, Word.twoSteps]
  twoCoeff_eq_word := by
    intro n
    change twoCoeff n = (AffineTransfer.ofWord (word n)).twoCoeff
    norm_num [twoCoeff, word, AffineTransfer.ofWord,
      Word.oddSteps, Word.twoSteps]

/-- canonical residue 条件まで追加した strongest relaxed witness。 -/
def packet : CanonicalResidueConstraints where
  toDiagonalWordProfileConstraints := diagonalPacket
  start_mod_eq_canonicalStart := start_mod_eq_canonical

/-- canonical residue geometry だけでは relaxed obstruction は閉じない。 -/
theorem constraints_satisfiable :
    Nonempty CanonicalResidueConstraints :=
  ⟨packet⟩

/-- この witness は exact word translation ではない。 -/
theorem translate_ne_affineConst (n : ℕ) :
    translate n ≠ Word.affineConst (word n) := by
  norm_num [translate, word, Word.affineConst]
  omega

end CanonicalResidueModel
end ObstructionAudit
end Collatz2
