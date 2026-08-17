import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.DenominatorWindowCover

/-!
# Critical integer-residue separation: abstract closure theorem

前3ファイルを組み合わせる最終 pure arithmetic layer。

ここでは infinite 2-adic number `Ξ` 自体を構成しない。
代わりに

  Candidate e R

を「`R` が target 2-adic object と precision `e` まで一致する」という
任意の predicate として受け取る。

外部 López--Stoll theory が各 window index `j` に packet `A_j` を与え、
Candidate なら `2^e ∣ P_j + R Q_j` が従うとする。
さらに Christoffel height と Baker/Gouillon dyadic slack が size squeeze を与えれば、
十分大きい全 `e` で polynomially-small candidate は存在しない。

最後に有限初期範囲を直接検証すれば全 precision を閉じられる。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/--
一族の rational approximants が critical integer residue を排除するための
完全な arithmetic input packet。
-/
structure CriticalResidueApproximationFamily where
  q : ℕ → ℕ
  packet : ℕ → LopezStollPacket
  H : ℕ
  start : ℕ
  start_ge_three : 3 ≤ start
  q_mono : ∀ n : ℕ, q n ≤ q (n + 1)
  packet_q : ∀ j : ℕ, (packet j).q = q j
  packet_precision :
    ∀ j : ℕ,
      (packet j).E = denominatorWindowUpper q j
  height :
    ∀ j : ℕ,
      HasChristoffelHeightBound H (q j)
        (packet j).P (packet j).Q
  upper_cofinal :
    ∀ N : ℕ, ∃ j : ℕ,
      start ≤ j ∧ N ≤ denominatorWindowUpper q j

namespace CriticalResidueApproximationFamily

/-- family の最初の covered precision。 -/
def firstPrecision (F : CriticalResidueApproximationFamily) : ℕ :=
  denominatorWindowLower F.q F.start

/--
Candidate が packet `j` と precision `e` で共通 2-adic target を持つこと。
実際の López--Stoll bridge では `e <= E_j` と
`Ξ ≡ R (mod 2^e)`, `Ξ ≡ -P_j/Q_j (mod 2^e)` から導く。
-/
def CandidateMatches
    (F : CriticalResidueApproximationFamily)
    (Candidate : ℕ → ℕ → Prop) : Prop :=
  ∀ j e R : ℕ,
    F.start ≤ j →
    e ≤ (F.packet j).E →
    Candidate e R →
    (F.packet j).Matches e R

/--
指定 bound `B(e)` に対し、coarse window の全点で size squeeze が成立する。
Baker/Gouillon + Christoffel height から最終的に示すべき elementary inequality。
-/
def WindowHeightSqueeze
    (F : CriticalResidueApproximationFamily)
    (B : ℕ → ℕ) : Prop :=
  ∀ j e : ℕ,
    F.start ≤ j →
    denominatorWindowLower F.q j ≤ e →
    e ≤ denominatorWindowUpper F.q j →
    (F.H * F.q j * 2 ^ F.q j) * (B e + 1) < 2 ^ e

/--
cofinal windows + height squeeze から、十分大きい precision の
small Candidate を全排除する。
-/
theorem no_small_candidate_eventually
    (F : CriticalResidueApproximationFamily)
    {Candidate : ℕ → ℕ → Prop}
    {B : ℕ → ℕ}
    (hMatch : F.CandidateMatches Candidate)
    (hSqueeze : F.WindowHeightSqueeze B)
    {e R : ℕ}
    (hLarge : F.firstPrecision ≤ e)
    (hR : R ≤ B e)
    (hCandidate : Candidate e R) :
    False := by
  rcases exists_denominatorWindow_cofinal
      F.q F.start_ge_three hLarge F.upper_cofinal with
    ⟨j, hjStart, hLower, hUpper⟩
  have hE : e ≤ (F.packet j).E := by
    rw [F.packet_precision j]
    exact hUpper
  have hPacketMatch : (F.packet j).Matches e R :=
    hMatch j e R hjStart hE hCandidate
  have hHeight0 := F.height j
  have hHeight :
      HasChristoffelHeightBound F.H (F.packet j).q
        (F.packet j).P (F.packet j).Q := by
    rw [F.packet_q j]
    exact hHeight0
  have hSq0 := hSqueeze j e hjStart hLower hUpper
  have hSq :
      (F.H * (F.packet j).q * 2 ^ (F.packet j).q) *
          (B e + 1) < 2 ^ e := by
    rw [F.packet_q j]
    exact hSq0
  exact noSmallResidue_of_height_squeeze
    (F.packet j)
    hPacketMatch hHeight hR hSq

/-- eventual separation を論理式として取り出す。 -/
theorem eventual_integer_residue_separation
    (F : CriticalResidueApproximationFamily)
    {Candidate : ℕ → ℕ → Prop}
    {B : ℕ → ℕ}
    (hMatch : F.CandidateMatches Candidate)
    (hSqueeze : F.WindowHeightSqueeze B) :
    ∀ e R : ℕ,
      F.firstPrecision ≤ e →
      R ≤ B e →
      ¬ Candidate e R := by
  intro e R he hR hC
  exact F.no_small_candidate_eventually hMatch hSqueeze he hR hC

/--
finite exceptions closure。

`e < firstPrecision` の有限範囲だけ直接確認すれば、
全 precision で small Candidate を排除できる。
-/
theorem integer_residue_separation_of_finite_check
    (F : CriticalResidueApproximationFamily)
    {Candidate : ℕ → ℕ → Prop}
    {B : ℕ → ℕ}
    (hMatch : F.CandidateMatches Candidate)
    (hSqueeze : F.WindowHeightSqueeze B)
    (hFinite :
      ∀ e R : ℕ,
        e < F.firstPrecision →
        R ≤ B e →
        ¬ Candidate e R) :
    ∀ e R : ℕ,
      R ≤ B e →
      ¬ Candidate e R := by
  intro e R hR
  by_cases he : F.firstPrecision ≤ e
  · exact F.eventual_integer_residue_separation
      hMatch hSqueeze e R he hR
  · have hlt : e < F.firstPrecision := by omega
    exact hFinite e R hlt hR

end CriticalResidueApproximationFamily

/--
特に polynomial small residues `B(e)=C*(e+1)^D` 用の bound function。
`+1` は `e=0` を含めて扱いやすくするためだけの正規化。
-/
def polynomialResidueBound (C D e : ℕ) : ℕ :=
  C * (e + 1) ^ D

/--
最終的に必要な integer-only separation theorem の abstract Lean form。

López--Stoll packet family、window height squeeze、有限初期検証を与えれば

  0 <= R <= C (e+1)^D

の Candidate は全 precision で存在しない。
-/
theorem critical_integer_residue_separation
    (F : CriticalResidueApproximationFamily)
    {Candidate : ℕ → ℕ → Prop}
    {C D : ℕ}
    (hMatch : F.CandidateMatches Candidate)
    (hSqueeze :
      F.WindowHeightSqueeze (polynomialResidueBound C D))
    (hFinite :
      ∀ e R : ℕ,
        e < F.firstPrecision →
        R ≤ polynomialResidueBound C D e →
        ¬ Candidate e R) :
    ∀ e R : ℕ,
      R ≤ polynomialResidueBound C D e →
      ¬ Candidate e R := by
  exact F.integer_residue_separation_of_finite_check
    hMatch hSqueeze hFinite

end ExternalArithmetic
end CSTMicro
end Collatz2
