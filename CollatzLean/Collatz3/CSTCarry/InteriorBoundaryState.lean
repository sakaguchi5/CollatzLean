import CollatzLean.Collatz3.CSTCarry.ShiftedBlockCarryTransport

/-!
# Collatz3 CSTCarry: interior block boundary state

Record chain を terminal 側から読むと、block endpoint `a+r` から incoming carry が来る。

interior block では

`beattyCarry a r = 1`

なので

`beattyIndex (a+r) = beattyIndex a + criticalTwoDepth r`。

従って endpoint scale で factor された carry は、block start scale では

`2^criticalTwoDepth(r) * q`

として見える。

追加の residue field は保存しない。digit phase は
`profileBlockCanonicalCarry_scale` の exact canonical transport が保持する。
-/

namespace Collatz3
namespace CSTCarry

open Critical

/--
cut `a` における最小 boundary state。

`E = 2^beattyIndex(a) * q` かつ quotient が `slack` bit 幅内にある。
-/
def InteriorBoundaryState
    (a slack q E : ℕ) : Prop :=
  E = 2 ^ beattyIndex a * q ∧
    q < 2 ^ slack

/-- boundary state は global bit-width bound を与える。 -/
theorem InteriorBoundaryState.global_lt
    {a slack q E : ℕ}
    (S : InteriorBoundaryState a slack q E) :
    E < 2 ^ (beattyIndex a + slack) := by
  rw [S.1, pow_add]
  exact (Nat.mul_lt_mul_left
    (by positivity : 0 < 2 ^ beattyIndex a)).2 S.2

/--
interior endpoint state を block start scale へ rebase する。

incoming quotient は `2^H_r * q` となり、
ambient local width `H_r + slack` の strict range 内に入る。
-/
theorem interiorBoundaryState_rebase
    {a r slack q E : ℕ}
    (hOne : beattyCarry a r = 1)
    (S : InteriorBoundaryState (a + r) slack q E) :
    E =
        2 ^ beattyIndex a *
          (2 ^ criticalTwoDepth r * q) ∧
      2 ^ criticalTwoDepth r * q <
        2 ^ (criticalTwoDepth r + slack) := by
  have hIndex :=
    beattyIndex_add_eq_beatty_add_criticalTwoDepth_of_carry_one hOne
  constructor
  · rw [S.1, hIndex, pow_add]
    ring
  · rw [pow_add]
    exact (Nat.mul_lt_mul_left
      (by positivity : 0 < 2 ^ criticalTwoDepth r)).2 S.2

/--
interior block の本当の induction frontier。

任意 slack と endpoint quotient `q < 2^slack` に対して、
shifted-local canonical run を

`initial = 2^H_r * q`
`modulus = 2^(H_r + slack)`

で走らせても final carry が同じ ambient modulus 未満に残ること。

この predicate 自体には新しい数学仮定を埋め込まない。
未証明核心を一箇所へ隔離するための thin interface である。
-/
def InteriorBlockTransportProperty
    {m : ℕ}
    (h : Profile m)
    (a r : ℕ)
    (B : IsLocalCriticalBlock h a r) : Prop :=
  ∀ (slack q : ℕ),
    q < 2 ^ slack →
      canonicalFinalCarry
          (criticalTwoDepth r + slack)
          (shiftedCriticalBlockCarryRows h a r B)
          (2 ^ criticalTwoDepth r * q) <
        2 ^ (criticalTwoDepth r + slack)

/--
`InteriorBlockTransportProperty` があれば boundary state は一 block 逆向きに保存される。

これは global row recurrence ではなく shifted-local recurrence へ exact に縮約してから戻す。
-/
theorem interiorBoundaryState_transport
    {m : ℕ}
    {h : Profile m}
    (A : Admissible h)
    {a r slack q E : ℕ}
    (hStartRoof : IsRoofCut h a)
    (B : IsLocalCriticalBlock h a r)
    (hOne : beattyCarry a r = 1)
    (S : InteriorBoundaryState (a + r) slack q E)
    (T : InteriorBlockTransportProperty h a r B) :
    let qOut :=
      canonicalFinalCarry
        (criticalTwoDepth r + slack)
        (shiftedCriticalBlockCarryRows h a r B)
        (2 ^ criticalTwoDepth r * q)
    InteriorBoundaryState
      a
      (criticalTwoDepth r + slack)
      qOut
      (canonicalFinalCarry
        (beattyIndex a + (criticalTwoDepth r + slack))
        (profileBlockCarryRows h a r B.2.1)
        E) := by
  dsimp
  have hRebase := interiorBoundaryState_rebase hOne S
  have hScale :=
    profileBlockCanonicalCarry_scale
      A hStartRoof B
      (Hglobal := beattyIndex a + (criticalTwoDepth r + slack))
      (Hlocal := criticalTwoDepth r + slack)
      (E := 2 ^ criticalTwoDepth r * q)
      rfl
  rw [hRebase.1]
  exact ⟨hScale.2, T slack q S.2⟩

/--
上の state transport から global strict bound も直ちに得られる。
-/
theorem interiorBlock_globalFinal_lt
    {m : ℕ}
    {h : Profile m}
    (A : Admissible h)
    {a r slack q E : ℕ}
    (hStartRoof : IsRoofCut h a)
    (B : IsLocalCriticalBlock h a r)
    (hOne : beattyCarry a r = 1)
    (S : InteriorBoundaryState (a + r) slack q E)
    (T : InteriorBlockTransportProperty h a r B) :
    canonicalFinalCarry
        (beattyIndex a + (criticalTwoDepth r + slack))
        (profileBlockCarryRows h a r B.2.1)
        E <
      2 ^ (beattyIndex a + (criticalTwoDepth r + slack)) := by
  let qOut :=
    canonicalFinalCarry
      (criticalTwoDepth r + slack)
      (shiftedCriticalBlockCarryRows h a r B)
      (2 ^ criticalTwoDepth r * q)
  have hState :
      InteriorBoundaryState
        a
        (criticalTwoDepth r + slack)
        qOut
        (canonicalFinalCarry
          (beattyIndex a + (criticalTwoDepth r + slack))
          (profileBlockCarryRows h a r B.2.1)
          E) := by
    exact interiorBoundaryState_transport
      A hStartRoof B hOne S T
  exact hState.global_lt

end CSTCarry
end Collatz3
