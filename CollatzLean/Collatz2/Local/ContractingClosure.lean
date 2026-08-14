import CollatzLean.Collatz2.Orbit.Runs
import CollatzLean.Collatz2.Local.DeterminantSign

/-!
# Collatz2 Local: contracting closure from actual order

future-minimum minimalization で使う二つの一般補題を分離する。

* nonempty normalized run が strict descent なら、その word は contracting
* contracting word を二つ連結しても contracting

trajectory-specific packet は導入しない。
-/

namespace Collatz2
namespace Word

/-- 二つの contracting word の連結も contracting。 -/
theorem Contracting.append
    {u v : Word}
    (hu : Contracting u)
    (hv : Contracting v) :
    Contracting (u ++ v) := by
  have huPow : 3 ^ oddSteps u < 2 ^ twoSteps u :=
    (contracting_iff_threePow_lt_twoPow).1 hu
  have hvPow : 3 ^ oddSteps v < 2 ^ twoSteps v :=
    (contracting_iff_threePow_lt_twoPow).1 hv
  apply (contracting_iff_threePow_lt_twoPow).2
  rw [oddSteps_append, twoSteps_append, pow_add, pow_add]
  have hCvPos : 0 < 3 ^ oddSteps v := Nat.pow_pos (by omega)
  have hAuPos : 0 < 2 ^ twoSteps u := Nat.pow_pos (by omega)
  calc
    3 ^ oddSteps u * 3 ^ oddSteps v
        < 2 ^ twoSteps u * 3 ^ oddSteps v :=
      (Nat.mul_lt_mul_right hCvPos).2 huPow
    _ < 2 ^ twoSteps u * 2 ^ twoSteps v :=
      (Nat.mul_lt_mul_left hAuPos).2 hvPow

/--
nonempty actual normalized run が strict descent `y < x` を実現するなら word は contracting。
-/
theorem Runs.contracting_of_end_lt_start
    {w : Word} {x y : ℕ}
    (hrun : Runs w x y)
    (hne : w ≠ [])
    (hyx : y < x) :
    Contracting w := by
  rcases expanding_or_contracting_of_valid_nonempty hrun.valid hne with hE | hC
  · exfalso
    have hPow : 2 ^ twoSteps w < 3 ^ oddSteps w :=
      (expanding_iff_twoPow_lt_threePow).1 hE
    have hxOdd : Odd x := hrun.start_odd_of_ne_nil hne
    have hxPos : 0 < x := by
      rcases hxOdd with ⟨a, ha⟩
      omega
    have hApos : 0 < 2 ^ twoSteps w := Nat.pow_pos (by omega)
    have hAyAx :
        2 ^ twoSteps w * y < 2 ^ twoSteps w * x :=
      (Nat.mul_lt_mul_left hApos).2 hyx
    have hAxCx :
        2 ^ twoSteps w * x < 3 ^ oddSteps w * x :=
      (Nat.mul_lt_mul_right hxPos).2 hPow
    have hAyCx :
        2 ^ twoSteps w * y < 3 ^ oddSteps w * x :=
      lt_trans hAyAx hAxCx
    have hreal :=
      (realizes_iff w x y).1 hrun.realizes
    omega
  · exact hC

end Word
end Collatz2
