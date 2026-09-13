import CollatzLean.Collatz3.Bridge.SurvivorRecordWindows
import CollatzLean.Collatz3.Bridge.FiniteParityResidue

/-!
# Collatz3 Bridge: natural infinite survivor の 2進 residue stability

abstract infinite survivor path は、各 positive physical depth `n` に survivor composition を持ち、
一段深い code の parent が一段浅い code と一致する coherent family として保存する。

一個の自然数 `x` がこの path を実現するとは、各 depth の actual parity residue が

`x mod 2^n`

に一致することとする。

普通の自然数では binary expansion が有限なので、`2^n > x` となった後は
`x mod 2^n = x`。従って自然数から実現される infinite survivor の residue representative は
eventually constant であり、最終的には常に `x` そのものになる。
-/

namespace Collatz3
namespace Bridge

/-- positive physical depth。 -/
abbrev PositiveParityDepth := {n : ℕ // 0 < n}

/-- 全 positive depth で coherent な survivor parity path。 -/
structure InfiniteSurvivorParityPath where
  code : ∀ n : PositiveParityDepth, SurvivorParityCode n.1
  parent :
    ∀ n : PositiveParityDepth,
      parityParent
          (code ⟨n.1 + 1, by omega⟩).1 =
        (code n).1

namespace InfiniteSurvivorParityPath

/-- depth `n` の underlying survivor composition。 -/
def composition
    (P : InfiniteSurvivorParityPath)
    (n : PositiveParityDepth) :
    ParityComposition n.1 :=
  (P.code n).1

/-- depth `n` の actual odd residue representative。 -/
noncomputable def residue
    (P : InfiniteSurvivorParityPath)
    (n : PositiveParityDepth) : ℕ :=
  (parityCompositionResidue n.2 (P.code n).1).1

/-- residue representative は `2^n` 未満。 -/
theorem residue_lt_twoPow
    (P : InfiniteSurvivorParityPath)
    (n : PositiveParityDepth) :
    P.residue n < 2 ^ n.1 :=
  (parityCompositionResidue n.2 (P.code n).1).2.1

/-- residue representative は odd。 -/
theorem residue_odd
    (P : InfiniteSurvivorParityPath)
    (n : PositiveParityDepth) :
    Odd (P.residue n) :=
  (parityCompositionResidue n.2 (P.code n).1).2.2

end InfiniteSurvivorParityPath

/--
自然数 `x` が infinite survivor path を実現すること。
各 finite prefix の actual residue は `x mod 2^n`。
-/
def NaturalNumberRealizesSurvivorPath
    (x : ℕ)
    (P : InfiniteSurvivorParityPath) : Prop :=
  ∀ n : PositiveParityDepth,
    P.residue n = x % 2 ^ n.1

namespace NaturalNumberRealizesSurvivorPath

/-- modulus が `x` より大きければ residue representative は `x` そのもの。 -/
theorem residue_eq_of_lt_twoPow
    {x : ℕ}
    {P : InfiniteSurvivorParityPath}
    (R : NaturalNumberRealizesSurvivorPath x P)
    (n : PositiveParityDepth)
    (hx : x < 2 ^ n.1) :
    P.residue n = x := by
  rw [R n]
  exact Nat.mod_eq_of_lt hx

/-- 自然数 realization は必ず odd start を持つ。 -/
theorem start_odd
    {x : ℕ}
    {P : InfiniteSurvivorParityPath}
    (R : NaturalNumberRealizesSurvivorPath x P) :
    Odd x := by
  let n : PositiveParityDepth := ⟨x + 1, by omega⟩
  have hx0 : x < 2 ^ x := x.lt_two_pow_self
  have hmono : 2 ^ x ≤ 2 ^ (x + 1) :=
    Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega)
  have hx : x < 2 ^ n.1 := by
    dsimp [n]
    exact lt_of_lt_of_le hx0 hmono
  have hEq : P.residue n = x := R.residue_eq_of_lt_twoPow n hx
  rw [← hEq]
  exact P.residue_odd n

/--
`N = x+1` 以降では actual residue representative が完全に `x` に固定される。
-/
theorem residue_eventually_constant
    {x : ℕ}
    {P : InfiniteSurvivorParityPath}
    (R : NaturalNumberRealizesSurvivorPath x P) :
    ∃ N : ℕ,
      0 < N ∧
        ∀ n : ℕ,
          N ≤ n →
          (hn : 0 < n) →
          P.residue ⟨n, hn⟩ = x := by
  refine ⟨x + 1, by omega, ?_⟩
  intro n hN hn
  have hx0 : x < 2 ^ x := x.lt_two_pow_self
  have hxn : x ≤ n := by omega
  have hmono : 2 ^ x ≤ 2 ^ n :=
    Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hxn
  have hx : x < 2 ^ n := lt_of_lt_of_le hx0 hmono
  exact R.residue_eq_of_lt_twoPow ⟨n, hn⟩ hx

/-- より直接的な形: `x+1 ≤ n` なら residue は `x`。 -/
theorem residue_eq_self_of_x_succ_le
    {x n : ℕ}
    {P : InfiniteSurvivorParityPath}
    (R : NaturalNumberRealizesSurvivorPath x P)
    (hxn : x + 1 ≤ n)
    (hn : 0 < n) :
    P.residue ⟨n, hn⟩ = x := by
  have hx0 : x < 2 ^ x := x.lt_two_pow_self
  have hxn' : x ≤ n := by omega
  have hmono : 2 ^ x ≤ 2 ^ n :=
    Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hxn'
  exact R.residue_eq_of_lt_twoPow ⟨n, hn⟩ (lt_of_lt_of_le hx0 hmono)

end NaturalNumberRealizesSurvivorPath

end Bridge
end Collatz3
