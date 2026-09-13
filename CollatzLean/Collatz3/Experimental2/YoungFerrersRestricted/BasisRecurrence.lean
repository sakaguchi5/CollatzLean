import CollatzLean.Collatz3.Experimental2.YoungFerrersRestricted.SuccessiveRank

/-!
# Collatz3 Experimental2: successive rank から作る basis recurrence

successive rank vector `s₀,...,s_{D-1}` だけから、
同じ rank vector を持つ Frobenius symbol のうち最小候補となる arm 列を右から再帰的に作る。

最後の arm は

  max(0, s_last)

であり、それより左では

* arm 自身が1以上ずつ減少する条件、
* leg = arm - rank が1以上ずつ減少する条件

のうち強い方を exact に採用する。
-/

namespace Collatz3
namespace Experimental2
namespace YoungFerrersRestricted

/--
successive rank vector から canonical basis arm 列を作る。
`if` 版にしておくことで、どちらの strictness 条件が active かを theorem で直接読める。
-/
def basisArms : List ℤ → List ℤ
  | [] => []
  | [s] => [if s ≤ 0 then 0 else s]
  | s :: t :: ss =>
      let tail := basisArms (t :: ss)
      let next := tail.getD 0 0
      (if s ≤ t then next + 1 else next + 1 + s - t) :: tail

/-- basis leg は `arm - successive rank`。 -/
def basisLegs (ranks : List ℤ) : List ℤ :=
  List.zipWith (fun a s => a - s) (basisArms ranks) ranks

/--
Frobenius symbol `(arms, ranks)` の重量。
`legs = arms - ranks` を代入した

  D + Σ arms + Σ legs
  = D + 2 Σ arms - Σ ranks

を整数のまま保持する。
-/
def symbolWeightZ (ranks arms : List ℤ) : ℤ :=
  (ranks.length : ℤ) + 2 * arms.sum - ranks.sum

/-- successive rank vector の canonical basis weight。 -/
def basisWeightZ (ranks : List ℤ) : ℤ :=
  symbolWeightZ ranks (basisArms ranks)

@[simp] theorem basisArms_length :
    ∀ ranks : List ℤ,
      (basisArms ranks).length = ranks.length
  | [] => rfl
  | [s] => by simp [basisArms]
  | s :: t :: ss => by
      simp [basisArms, basisArms_length (t :: ss)]

@[simp] theorem basisLegs_length
    (ranks : List ℤ) :
    (basisLegs ranks).length = ranks.length := by
  simp [basisLegs, basisArms_length]

/-- singleton rank の basis arm。 -/
theorem basisArms_singleton
    (s : ℤ) :
    basisArms [s] = [if s ≤ 0 then 0 else s] := by
  rfl

/-- 2要素以上の rank vector に対する一段 recurrence。 -/
theorem basisArms_cons_cons
    (s t : ℤ)
    (ss : List ℤ) :
    basisArms (s :: t :: ss) =
      (if s ≤ t then
          (basisArms (t :: ss)).getD 0 0 + 1
        else
          (basisArms (t :: ss)).getD 0 0 + 1 + s - t) ::
        basisArms (t :: ss) := by
  rfl

end YoungFerrersRestricted
end Experimental2
end Collatz3
