import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleFullDeficitProfileNumeratorBridge

/-!
# 第3例探索 3: branch-local deficit candidates

`(r,d,w)` が deficit residue を一意に決めることは、まだ仮定しない。
代わりに各 branch から有限個の residue candidate を返す多値 API を採用する。
これにより、一意性が後で証明できても、複数候補が必要でも verifier の完全性を失わない。
-/

namespace Collatz2
namespace CSTMicro
namespace ThirdExampleSearch

/-- `mod 3^42` の residue は canonical representative を持つ `Fin` で保持する。 -/
abbrev ThirdExampleDeficitResidue := Fin thirdExampleRightModulus

/-- 一つの finite deficit candidate。 -/
@[ext]
structure ThirdExampleBranchDeficitCandidate where
  branch : ThirdExampleRDW
  deficit : ThirdExampleDeficitResidue
  deriving DecidableEq, Repr

/-- branch ごとに有限個の deficit residue を返す proof-free generator。 -/
abbrev ThirdExampleBranchDeficitGenerator :=
  ThirdExampleRDW → List ThirdExampleDeficitResidue

/-- generator を全12,341枝へ flatMap した runtime table。 -/
def thirdExampleBranchDeficitCandidates
    (G : ThirdExampleBranchDeficitGenerator) :
    List ThirdExampleBranchDeficitCandidate :=
  thirdExampleFiniteDeficitBranches.flatMap (fun B =>
    (G B).map (fun z => { branch := B, deficit := z }))

/--
proof-side completeness。
actual deficit residue が admissible relation を満たすなら generator に必ず含まれる、
という形にして local state の選び方を後段から差し替えられる。
-/
def ThirdExampleBranchDeficitGeneratorComplete
    (Admissible : ThirdExampleRDW → ThirdExampleDeficitResidue → Prop)
    (G : ThirdExampleBranchDeficitGenerator) : Prop :=
  ∀ B z,
    B ∈ thirdExampleFiniteDeficitBranches →
    Admissible B z →
    z ∈ G B

/-- complete generator なら admissible candidate は flat table に現れる。 -/
theorem thirdExampleBranchDeficitCandidates_mem_of_complete
    {Admissible : ThirdExampleRDW → ThirdExampleDeficitResidue → Prop}
    {G : ThirdExampleBranchDeficitGenerator}
    (hG : ThirdExampleBranchDeficitGeneratorComplete Admissible G)
    {B : ThirdExampleRDW}
    {z : ThirdExampleDeficitResidue}
    (hB : B ∈ thirdExampleFiniteDeficitBranches)
    (hz : Admissible B z) :
    ({ branch := B, deficit := z } : ThirdExampleBranchDeficitCandidate) ∈
      thirdExampleBranchDeficitCandidates G := by
  unfold thirdExampleBranchDeficitCandidates
  simp only [List.mem_flatMap, List.mem_map]
  refine ⟨B, hB, ?_⟩
  refine ⟨z, hG B z hB hz, ?_⟩
  rfl

end ThirdExampleSearch
end CSTMicro
end Collatz2
