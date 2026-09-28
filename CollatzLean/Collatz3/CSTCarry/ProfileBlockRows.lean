import CollatzLean.Collatz3.CSTCarry.CarryBudgetGeneralBound
import CollatzLean.Collatz3.CSTCarry.ShiftedBlockDefect
import CollatzLean.Collatz3.CSTCarry.ProfileAffineBudgetBridge
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-!
# Collatz3 CSTCarry: profileCarryRows の block row 表現

`profileCarryRows h` は critical index を

`m-1, ..., 1, 0`

の順に読む。

このファイルでは forward interval `[a,a+r)` に属する row だけを
carry 順 `a+r-1,...,a` で読む `profileBlockCarryRows` を定義する。

新しい幾何仮定は置かない。
-/

namespace Collatz3
namespace CSTCarry

open Critical
open scoped BigOperators

/--
profile の interval `[a,a+r)` を carry の向き、すなわち terminal 側から読む row list。
`hEnd` は interval が profile width 内にあることだけを保証する。
-/
def profileBlockCarryRows
    {m : ℕ}
    (h : Profile m)
    (a : ℕ) :
    (r : ℕ) → a + r ≤ m → List FerrersRow
  | 0, _ => []
  | r + 1, hEnd =>
      profileFerrersRow h ⟨a + r, by omega⟩ ::
        profileBlockCarryRows h a r (by omega)

@[simp] theorem profileBlockCarryRows_zero
    {m : ℕ}
    (h : Profile m)
    (a : ℕ)
    (hEnd : a + 0 ≤ m) :
    profileBlockCarryRows h a 0 hEnd = [] := by
  rfl

@[simp] theorem profileBlockCarryRows_length
    {m : ℕ}
    (h : Profile m)
    (a : ℕ) :
    ∀ (r : ℕ) (hEnd : a + r ≤ m),
      (profileBlockCarryRows h a r hEnd).length = r
  | 0, _ => by
      rfl
  | r + 1, hEnd => by
      simp [profileBlockCarryRows,
        profileBlockCarryRows_length h a r (by omega)]

/--
隣接 interval の row list は carry 向きでは後ろの interval が先に来る。

`[a,a+r+s) = [a+r,a+r+s) ++ [a,a+r)`。
-/
theorem profileBlockCarryRows_add
    {m : ℕ}
    (h : Profile m)
    (a r s : ℕ)
    (hEnd : a + (r + s) ≤ m) :
    profileBlockCarryRows h a (r + s) (by omega) =
      profileBlockCarryRows h (a + r) s (by omega) ++
        profileBlockCarryRows h a r (by omega) := by
  revert r
  induction s with
  | zero =>
      intro r hEnd
      simp [profileBlockCarryRows]
  | succ s ih =>
      intro r hEnd
      simp only [profileBlockCarryRows,List.cons_append]
      have hHead :
          profileFerrersRow h
              ⟨a + (r + s), by omega⟩ =
            profileFerrersRow h
              ⟨(a + r) + s, by omega⟩ := by
        have hFin :
            (⟨a + (r + s), by omega⟩ : Fin m) =
              ⟨(a + r) + s, by omega⟩ := by
          apply Fin.ext
          change a + (r + s) = (a + r) + s
          omega
        exact congrArg (profileFerrersRow h) hFin
      have hTail :
          profileBlockCarryRows h a (r + s) (by omega) =
            profileBlockCarryRows h (a + r) s (by omega) ++
              profileBlockCarryRows h a r (by omega) := by
        exact ih r (by omega)
      exact congrArg₂
        (fun (R : FerrersRow) (Rs : List FerrersRow) => R :: Rs)
        hHead
        hTail

/-- block row list を forward `Fin r` family の reverse として読む exact view。 -/
theorem profileBlockCarryRows_eq_reverse_ofFn
    {m : ℕ}
    (h : Profile m)
    (a : ℕ) :
    ∀ (r : ℕ) (hEnd : a + r ≤ m),
      profileBlockCarryRows h a r hEnd =
        (List.ofFn (fun j : Fin r =>
          profileFerrersRow h ⟨a + j.1, by omega⟩)).reverse
  | 0, _ => by
      simp [profileBlockCarryRows]
  | r + 1, hEnd => by
      simp only [profileBlockCarryRows, List.ofFn_succ',
        List.concat_eq_append, List.reverse_concat']
      rw [profileBlockCarryRows_eq_reverse_ofFn h a r (by omega)]
      rfl

/-- index `0` から全 width を読む block row list は既存 `profileCarryRows` と一致する。 -/
theorem profileBlockCarryRows_zero_full
    {m : ℕ}
    (h : Profile m) :
    profileBlockCarryRows h 0 m (by omega) = profileCarryRows h := by
  rw [profileBlockCarryRows_eq_reverse_ofFn]
  unfold profileCarryRows
  have hFun :
      (fun j : Fin m =>
        profileFerrersRow h ⟨0 + j.1, by omega⟩) =
      (fun j : Fin m =>
        profileFerrersRow h j) := by
    funext j
    have hFin :
        (⟨0 + j.1, by omega⟩ : Fin m) = j := by
      apply Fin.ext
      simp
    rw [hFin]
  rw [hFun]

/--
有限和として定義したブロック欠損の後続項に関する漸化式。

この漸化式自体は区間が profile の幅の内側にあることを必要とせず、
任意の `a r` について定義から成立する。
-/
theorem profileBlockWeightedDefect_succ
    {m : ℕ}
    (h : Profile m)
    {a r : ℕ} :
    profileBlockWeightedDefect h a (r + 1) =
      (2 ^ beattyIndex (a + r) - 2 ^ profileHeight h (a + r)) +
        3 * profileBlockWeightedDefect h a r := by
  unfold profileBlockWeightedDefect
  rw [Finset.sum_range_succ]
  have hScale :
      (∑ j ∈ Finset.range r,
          3 ^ ((r + 1) - (j + 1)) *
            (2 ^ beattyIndex (a + j) - 2 ^ profileHeight h (a + j))) =
        3 *
          (∑ j ∈ Finset.range r,
            3 ^ (r - (j + 1)) *
              (2 ^ beattyIndex (a + j) - 2 ^ profileHeight h (a + j))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hjLt : j < r := Finset.mem_range.mp hj
    have hExp :
        (r + 1) - (j + 1) = (r - (j + 1)) + 1 := by
      omega
    rw [hExp, pow_succ]
    ring
  rw [hScale]
  simp
  ring

/--
block row list の `ferrersWeightedDefect` は direct index sum
`profileBlockWeightedDefect` と exact に一致する。
-/
theorem ferrersWeightedDefect_profileBlockCarryRows
    {m : ℕ}
    (h : Profile m)
    (a : ℕ) :
    ∀ (r : ℕ) (hEnd : a + r ≤ m),
      ferrersWeightedDefect (profileBlockCarryRows h a r hEnd) =
        profileBlockWeightedDefect h a r
  | 0, _ => by
      simp [profileBlockCarryRows, profileBlockWeightedDefect]
  | r + 1, hEnd => by
      have hProper : a + r < m := by omega
      simp only [profileBlockCarryRows, ferrersWeightedDefect_cons]
      rw [ferrersWeightedDefect_profileBlockCarryRows h a r (by omega)]
      rw [profileBlockWeightedDefect_succ h]
      rw [profileFerrersRow_defect_eq]
      rw [profileHeight_of_lt h hProper]

/--
local critical block では actual row-list defect も shifted-local defect の scale 版になる。
-/
theorem ferrersWeightedDefect_profileBlockCarryRows_eq_scaled_shifted
    {m : ℕ}
    {h : Profile m}
    (A : Admissible h)
    {a r : ℕ}
    (hStartRoof : IsRoofCut h a)
    (B : IsLocalCriticalBlock h a r) :
    ferrersWeightedDefect
        (profileBlockCarryRows h a r B.2.1) =
      2 ^ beattyIndex a * shiftedBlockWeightedDefect h a r := by
  rw [ferrersWeightedDefect_profileBlockCarryRows h a r B.2.1]
  exact profileBlockWeightedDefect_eq_scaled_shifted_of_localCritical
    A hStartRoof B

/--
terminal carry `0` block の strict budget を、実際の block row list から
shifted-local budget へ exact に縮約する。
-/
theorem profileBlockRows_terminal_strictBudget_iff_shiftedLocal
    {m : ℕ}
    {h : Profile m}
    (A : Admissible h)
    {a r D : ℕ}
    (hStartRoof : IsRoofCut h a)
    (B : IsLocalCriticalBlock h a r)
    (hTerminal : a + r = m)
    (hCarryZero : beattyCarry a r = 0) :
    ferrersWeightedDefect
          (profileBlockCarryRows h a r B.2.1) <
        2 ^ criticalTwoDepth m * (D + 1) ↔
      shiftedBlockWeightedDefect h a r <
        2 ^ criticalTwoDepth r * (D + 1) := by
  rw [ferrersWeightedDefect_profileBlockCarryRows h a r B.2.1]
  exact terminalBlock_strictBudget_iff_shiftedLocal
    A hStartRoof B hTerminal hCarryZero

end CSTCarry
end Collatz3
