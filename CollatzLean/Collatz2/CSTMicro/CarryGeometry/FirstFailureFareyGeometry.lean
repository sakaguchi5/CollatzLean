import CollatzLean.Collatz2.CSTMicro.CarryCorridorExtraction
import Mathlib.Tactic.LinearCombination

/-!
# General CST: first-failure carry の Farey / terminal-gap 幾何

current `FirstFailureEdge` から無条件に得られる 2-adic carry 座標を、
後で terminal-gap / Farey 座標へ接続しやすい形に独立化する。

このファイルではまず

* carry complement `2^k - deltaR`,
* first-failure の small error `upperR`,
* separation defect の exact jump,
* first-failure では jump が strict positive,

を current CSTMicro object だけから証明する。

後半では pure arithmetic packet

  2^d * s - 3^a * h = 1

から cell residue

  D = 2^i * h - 3^r * s

を定義し、terminal gap `G = 2^k - 3^m` に対する exact identities

  2^d * D = G*h - 3^r
  3^a * D = G*s - 2^i

を証明する。

`AdjacentFerrersSwap` からこの Farey packet を自動抽出する bridge は、
modular inverse representative の quotient を ordinary integer に持ち上げる
次段の証明義務として意図的に分離している。
-/

namespace Collatz2
namespace CSTMicro

/-- word-level pure separation の signed defect `B - G*R`。 -/
def wordSeparationDefectInt (v : ParityWord) : ℤ :=
  (affineConst v : ℤ) -
    (wordTerminalGap v : ℤ) * (leastRepresentative v : ℤ)

namespace FirstFailureEdge

/-- first failure の lower side は signed defect が strict negative。 -/
theorem lower_wordSeparationDefectInt_neg
    (F : FirstFailureEdge) :
    wordSeparationDefectInt F.lower < 0 := by
  have h := F.lower_safe
  unfold WordPureSeparation at h
  have h' :
      (affineConst F.lower : ℤ) <
        (wordTerminalGap F.lower : ℤ) *
          (leastRepresentative F.lower : ℤ) := by
    exact_mod_cast h
  unfold wordSeparationDefectInt
  omega

/-- first failure の upper side は signed defect が nonnegative。 -/
theorem upper_wordSeparationDefectInt_nonneg
    (F : FirstFailureEdge) :
    0 ≤ wordSeparationDefectInt F.upper := by
  have hFail := F.upper_failure
  unfold WordPureSeparation at hFail
  have hNat :
      wordTerminalGap F.upper * leastRepresentative F.upper ≤
        affineConst F.upper := by
    omega
  have h :
      (wordTerminalGap F.upper : ℤ) *
          (leastRepresentative F.upper : ℤ) ≤
        (affineConst F.upper : ℤ) := by
    exact_mod_cast hNat
  unfold wordSeparationDefectInt
  omega

end FirstFailureEdge

namespace AdjacentFerrersSwap

/-- carry 時に `deltaR` の反対側に残る modulus complement。 -/
def carryComplement (S : AdjacentFerrersSwap) : ℕ :=
  S.modulus - S.deltaR

/-- carry complement は常に正。 -/
theorem carryComplement_pos (S : AdjacentFerrersSwap) :
    0 < S.carryComplement := by
  unfold carryComplement
  exact Nat.sub_pos_of_lt S.deltaR_lt_modulus

/-- lower word の terminal gap を edge 座標へ展開する。 -/
@[simp] theorem wordTerminalGap_lowerWord
    (S : AdjacentFerrersSwap) :
    wordTerminalGap S.lowerWord =
      S.modulus - 3 ^ S.oddTotal := by
  simp [wordTerminalGap, modulus]

/-- upper word の terminal gap も同じ edge 座標になる。 -/
@[simp] theorem wordTerminalGap_upperWord
    (S : AdjacentFerrersSwap) :
    wordTerminalGap S.upperWord =
      S.modulus - 3 ^ S.oddTotal := by
  simp [wordTerminalGap, modulus]

/-- adjacent swap の lower/upper terminal gap は exact に同じ。 -/
theorem wordTerminalGap_eq
    (S : AdjacentFerrersSwap) :
    wordTerminalGap S.lowerWord =
      wordTerminalGap S.upperWord := by
  rw [S.wordTerminalGap_lowerWord, S.wordTerminalGap_upperWord]

/--
carry なら lower representative は

  carryComplement + upperR

に exact 分解する。
-/
theorem lowerR_eq_carryComplement_add_upperR_of_hasCarry
    (S : AdjacentFerrersSwap)
    (hCarry : S.HasCarry) :
    S.lowerR = S.carryComplement + S.upperR := by
  have hsum :=
    S.lowerR_add_deltaR_eq_modulus_add_upperR_of_hasCarry hCarry
  have hdelta := S.deltaR_lt_modulus
  unfold carryComplement
  omega

/--
一つの carry cell が signed separation defect に与える integer jump。

後で `carryComplement = 2^i*h` を抽出すると

  jump = 2^i * (G*h - 3^r)

へ変形される。
-/
def carryCellJumpInt (S : AdjacentFerrersSwap) : ℤ :=
  (wordTerminalGap S.lowerWord : ℤ) *
      (S.carryComplement : ℤ) -
    (S.deltaB : ℤ)

/--
carry edge では upper defect - lower defect が
`carryCellJumpInt` に exact 一致する。
-/
theorem upper_defect_sub_lower_defect_eq_carryCellJumpInt_of_hasCarry
    (S : AdjacentFerrersSwap)
    (hCarry : S.HasCarry) :
    wordSeparationDefectInt S.upperWord -
        wordSeparationDefectInt S.lowerWord =
      S.carryCellJumpInt := by
  have hB := S.lower_affineConst_eq_upper_add_deltaB
  have hR :=
    S.lowerR_eq_carryComplement_add_upperR_of_hasCarry hCarry
  have hBz :
      (affineConst S.lowerWord : ℤ) =
        (affineConst S.upperWord : ℤ) + (S.deltaB : ℤ) := by
    exact_mod_cast hB
  have hRz :
      (S.lowerR : ℤ) =
        (S.carryComplement : ℤ) + (S.upperR : ℤ) := by
    exact_mod_cast hR
  unfold wordSeparationDefectInt carryCellJumpInt
  change
    ((affineConst S.upperWord : ℤ) -
        (wordTerminalGap S.upperWord : ℤ) * (S.upperR : ℤ)) -
      ((affineConst S.lowerWord : ℤ) -
        (wordTerminalGap S.lowerWord : ℤ) * (S.lowerR : ℤ)) =
      (wordTerminalGap S.lowerWord : ℤ) *
          (S.carryComplement : ℤ) -
        (S.deltaB : ℤ)
  rw [← S.wordTerminalGap_eq]
  rw [hBz, hRz]
  ring

end AdjacentFerrersSwap

namespace FirstFailureEdge

/-- first failure edge の carry complement 分解。 -/
theorem lowerR_eq_carryComplement_add_upperR
    (F : FirstFailureEdge) :
    F.step.edge.lowerR =
      F.step.edge.carryComplement + F.step.edge.upperR := by
  exact
    F.step.edge.lowerR_eq_carryComplement_add_upperR_of_hasCarry
      F.hasCarry

/--
first failure では carry cell jump が strict positive。

これは lower defect < 0, upper defect >= 0 と、
carry 時の exact defect jump を合わせただけの結論。
-/
theorem carryCellJumpInt_pos
    (F : FirstFailureEdge) :
    0 < F.step.edge.carryCellJumpInt := by
  have hLower :
      wordSeparationDefectInt F.step.edge.lowerWord < 0 := by
    rw [← F.step.lower_eq]
    exact F.lower_wordSeparationDefectInt_neg
  have hUpper :
      0 ≤ wordSeparationDefectInt F.step.edge.upperWord := by
    rw [← F.step.upper_eq]
    exact F.upper_wordSeparationDefectInt_nonneg
  have hJump :=
    F.step.edge.upper_defect_sub_lower_defect_eq_carryCellJumpInt_of_hasCarry
      F.hasCarry
  omega

/--
first failure は

  lowerR = carryComplement + error
  error  = upperR <= polynomial(length)

という exact `large structured base + small error` packet を持つ。
-/
theorem carryComplement_polynomial_packet
    (F : FirstFailureEdge)
    {K A : ℕ}
    (hGap :
      ∀ p H : ℕ,
        0 < p →
        3 ^ p < 2 ^ H →
        3 ^ p ≤
          K * (p + 1) ^ A * (2 ^ H - 3 ^ p)) :
    F.step.edge.lowerR =
        F.step.edge.carryComplement + F.step.edge.upperR ∧
      F.step.edge.upperR ≤
        K * (F.step.edge.length + 1) ^ (A + 1) := by
  constructor
  · exact F.lowerR_eq_carryComplement_add_upperR
  · exact F.upperR_le_simpleLengthPolynomial hGap

/-- polynomial error を lowerR 自身の上界へ持ち上げる。 -/
theorem lowerR_le_carryComplement_add_lengthPolynomial
    (F : FirstFailureEdge)
    {K A : ℕ}
    (hGap :
      ∀ p H : ℕ,
        0 < p →
        3 ^ p < 2 ^ H →
        3 ^ p ≤
          K * (p + 1) ^ A * (2 ^ H - 3 ^ p)) :
    F.step.edge.lowerR ≤
      F.step.edge.carryComplement +
        K * (F.step.edge.length + 1) ^ (A + 1) := by
  rw [F.lowerR_eq_carryComplement_add_upperR]
  exact Nat.add_le_add_left (F.upperR_le_simpleLengthPolynomial hGap) _

end FirstFailureEdge

/-!
## Pure Farey cell packet

ここから下は `AdjacentFerrersSwap` の implementation から独立した純整数論層。
`h,s,G` は signed algebra を簡潔に保つため `ℤ` で持つ。
-/

/--
一つの local cell に付随する determinant-one / terminal-gap 座標。

`k=i+d`, `m=a+r` と

  G = 2^k - 3^m,
  2^d*s - 3^a*h = 1

だけを core data とする。
-/
structure FareyCellPacket where
  i : ℕ
  d : ℕ
  a : ℕ
  r : ℕ
  k : ℕ
  m : ℕ
  h : ℤ
  s : ℤ
  G : ℤ
  k_eq : k = i + d
  m_eq : m = a + r
  gap_eq : G = (2 : ℤ) ^ k - (3 : ℤ) ^ m
  determinant_one :
    (2 : ℤ) ^ d * s - (3 : ℤ) ^ a * h = 1

namespace FareyCellPacket

/-- power-value Farey cell の signed terminal residue。 -/
def residue (P : FareyCellPacket) : ℤ :=
  (2 : ℤ) ^ P.i * P.h -
    (3 : ℤ) ^ P.r * P.s

/--
Farey determinant を 2-side から消去した exact identity。

  2^d * D = G*h - 3^r.
-/
theorem twoPow_mul_residue
    (P : FareyCellPacket) :
    (2 : ℤ) ^ P.d * P.residue =
      P.G * P.h - (3 : ℤ) ^ P.r := by
  unfold residue
  rw [P.gap_eq, P.k_eq, P.m_eq, pow_add, pow_add]
  linear_combination
    -((3 : ℤ) ^ P.r) * P.determinant_one

/--
Farey determinant を 3-side から消去した exact identity。

  3^a * D = G*s - 2^i.
-/
theorem threePow_mul_residue
    (P : FareyCellPacket) :
    (3 : ℤ) ^ P.a * P.residue =
      P.G * P.s - (2 : ℤ) ^ P.i := by
  unfold residue
  rw [P.gap_eq, P.k_eq, P.m_eq, pow_add, pow_add]
  linear_combination
    -((2 : ℤ) ^ P.i) * P.determinant_one

/-- positive cell residue は `G*h > 3^r` を強制する。 -/
theorem threePow_lt_gap_mul_h_of_residue_pos
    (P : FareyCellPacket)
    (hD : 0 < P.residue) :
    (3 : ℤ) ^ P.r < P.G * P.h := by
  have hEq := P.twoPow_mul_residue
  have hPow : 0 < (2 : ℤ) ^ P.d := by positivity
  nlinarith

/-- positive cell residue は双対側で `G*s > 2^i` も強制する。 -/
theorem twoPow_lt_gap_mul_s_of_residue_pos
    (P : FareyCellPacket)
    (hD : 0 < P.residue) :
    (2 : ℤ) ^ P.i < P.G * P.s := by
  have hEq := P.threePow_mul_residue
  have hPow : 0 < (3 : ℤ) ^ P.a := by positivity
  nlinarith

end FareyCellPacket

/-!
## Bridge target

次段で証明すべき modular-inverse extraction を interface として固定する。
existence はこのファイルでは仮定しない。
-/

/--
first-failure edge の carry complement が Farey denominator `h` を持つ、
という次段 bridge 用 packet。
-/
structure FirstFailureFareyData (F : FirstFailureEdge) where
  farey : FareyCellPacket
  i_eq_position : farey.i = F.step.edge.position
  d_eq_tail : farey.d = 2 + F.step.edge.rightContext.length
  a_eq_left :
    farey.a = oddCount F.step.edge.leftContext + 1
  r_eq_right :
    farey.r = oddCount F.step.edge.rightContext
  k_eq_length : farey.k = F.step.edge.length
  m_eq_oddTotal : farey.m = F.step.edge.oddTotal
  complement_eq :
    (F.step.edge.carryComplement : ℤ) =
      (2 : ℤ) ^ farey.i * farey.h

namespace FirstFailureFareyData

/-- bridge があれば carry equation は `2^i*h + small error` に exact 化する。 -/
theorem lowerR_eq_twoPow_mul_h_add_upperR
    {F : FirstFailureEdge}
    (D : FirstFailureFareyData F) :
    (F.step.edge.lowerR : ℤ) =
      (2 : ℤ) ^ D.farey.i * D.farey.h +
        (F.step.edge.upperR : ℤ) := by
  have hCarry := F.lowerR_eq_carryComplement_add_upperR
  have hCarryZ :
      (F.step.edge.lowerR : ℤ) =
        (F.step.edge.carryComplement : ℤ) +
          (F.step.edge.upperR : ℤ) := by
    exact_mod_cast hCarry
  rw [hCarryZ, D.complement_eq]

/--
bridge + polynomial gap input から、first failure の small error bound をそのまま保持する。
-/
theorem upperR_le_lengthPolynomial
    {F : FirstFailureEdge}
    (D : FirstFailureFareyData F)
    {K A : ℕ}
    (hGap :
      ∀ p H : ℕ,
        0 < p →
        3 ^ p < 2 ^ H →
        3 ^ p ≤
          K * (p + 1) ^ A * (2 ^ H - 3 ^ p)) :
    F.step.edge.upperR ≤
      K * (D.farey.k + 1) ^ (A + 1) := by
  rw [D.k_eq_length]
  exact F.upperR_le_simpleLengthPolynomial hGap

end FirstFailureFareyData

end CSTMicro
end Collatz2
