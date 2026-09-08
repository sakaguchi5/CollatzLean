import CollatzLean.Collatz3.Arithmetic.Pow23
import CollatzLean.Collatz3.Semantics.Runs

/-!
# Collatz3: 有限到達と軌道合流

`Runs` は指数語を保持した有限実軌道である。
このファイルでは、指数語を忘れた有限到達 `Reaches` と、
二つの始点が共通の後続点を持つことを表す `Merges` だけを薄い語彙として導入する。

`Merges` の推移性は定義に埋め込まない。
odd-only Collatz の 1 step が決定的であることと、`Runs` の連結から theorem として導く。
-/

namespace Collatz3

namespace OddStep

/--
同じ始点からの exact odd-only step は、2 除算指数も終点も一意。

証明では `2^e * y = 2^f * z` を比較する。
仮に `e < f` なら、奇数 `y` が正の 2 の冪で割り切れることになり矛盾する。
`f < e` も対称である。
-/
theorem deterministic
    {e f x y z : ℕ}
    (hy : OddStep e x y)
    (hz : OddStep f x z) :
    e = f ∧ y = z := by
  have hEq : 2 ^ e * y = 2 ^ f * z := by
    calc
      2 ^ e * y = 3 * x + 1 := hy.equation
      _ = 2 ^ f * z := hz.equation.symm
  have hef : e = f := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hef | hfe
    · have hle : e ≤ f := Nat.le_of_lt hef
      have hPow : 2 ^ f = 2 ^ e * 2 ^ (f - e) := by
        calc
          2 ^ f = 2 ^ (e + (f - e)) := by
            rw [Nat.add_sub_of_le hle]
          _ = 2 ^ e * 2 ^ (f - e) := by
            rw [pow_add]
      have hEq' :
          2 ^ e * y = 2 ^ e * (2 ^ (f - e) * z) := by
        calc
          2 ^ e * y = 2 ^ f * z := hEq
          _ = (2 ^ e * 2 ^ (f - e)) * z := by rw [hPow]
          _ = 2 ^ e * (2 ^ (f - e) * z) := by ring
      have hyFactor : y = 2 ^ (f - e) * z :=
        Nat.mul_left_cancel (Arithmetic.twoPow_pos e) hEq'
      have hdPos : 0 < f - e := Nat.sub_pos_of_lt hef
      obtain ⟨d, hd⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hdPos)
      have hyEven : ∃ q : ℕ, y = 2 * q := by
        refine ⟨2 ^ d * z, ?_⟩
        rw [hyFactor, hd, pow_succ]
        ring
      rcases hy.end_odd with ⟨k, hk⟩
      rcases hyEven with ⟨q, hq⟩
      omega
    · have hle : f ≤ e := Nat.le_of_lt hfe
      have hPow : 2 ^ e = 2 ^ f * 2 ^ (e - f) := by
        calc
          2 ^ e = 2 ^ (f + (e - f)) := by
            rw [Nat.add_sub_of_le hle]
          _ = 2 ^ f * 2 ^ (e - f) := by
            rw [pow_add]
      have hEq' :
          2 ^ f * z = 2 ^ f * (2 ^ (e - f) * y) := by
        calc
          2 ^ f * z = 2 ^ e * y := hEq.symm
          _ = (2 ^ f * 2 ^ (e - f)) * y := by rw [hPow]
          _ = 2 ^ f * (2 ^ (e - f) * y) := by ring
      have hzFactor : z = 2 ^ (e - f) * y :=
        Nat.mul_left_cancel (Arithmetic.twoPow_pos f) hEq'
      have hdPos : 0 < e - f := Nat.sub_pos_of_lt hfe
      obtain ⟨d, hd⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hdPos)
      have hzEven : ∃ q : ℕ, z = 2 * q := by
        refine ⟨2 ^ d * y, ?_⟩
        rw [hzFactor, hd, pow_succ]
        ring
      rcases hz.end_odd with ⟨k, hk⟩
      rcases hzEven with ⟨q, hq⟩
      omega
  subst f
  refine ⟨rfl, ?_⟩
  exact Nat.mul_left_cancel (Arithmetic.twoPow_pos e) hEq

end OddStep

/--
指数語の情報を忘れた finite odd-only 到達。
空語を許すため反射的である。
-/
def Reaches (x y : ℕ) : Prop :=
  ∃ w : Word, Runs w x y

namespace Reaches

/-- 任意の値は空 run で自分自身へ到達する。 -/
@[refl]
theorem refl (x : ℕ) : Reaches x x :=
  ⟨[], Runs.nil x⟩

/-- finite 到達は run の連結で推移的。 -/
@[trans]
theorem trans
    {x y z : ℕ}
    (hxy : Reaches x y)
    (hyz : Reaches y z) :
    Reaches x z := by
  rcases hxy with ⟨u, hu⟩
  rcases hyz with ⟨v, hv⟩
  exact ⟨u ++ v, Runs.append hu hv⟩

/-- 1 個の exact odd-only step は finite 到達を与える。 -/
theorem of_oddStep
    {e x y : ℕ}
    (h : OddStep e x y) :
    Reaches x y :=
  ⟨[e], Runs.cons h (Runs.nil y)⟩

/--
同じ始点から二つの finite run を進めた終点は、どちらかが他方の後続点になる。
これは odd-only step の決定性から従う。
-/
theorem comparable_of_common_start
    {x y z : ℕ}
    (hxy : Reaches x y)
    (hxz : Reaches x z) :
    Reaches y z ∨ Reaches z y := by
  rcases hxy with ⟨u, hu⟩
  rcases hxz with ⟨v, hv⟩
  induction hu generalizing v z with
  | nil x =>
      exact Or.inl ⟨v, hv⟩
  | @cons e u x m y hstep htail ih =>
      cases hv with
      | nil x =>
          exact Or.inr ⟨e :: u, Runs.cons hstep htail⟩
      | @cons f v x n z hstep' htail' =>
          have hmn : m = n := (OddStep.deterministic hstep hstep').2
          subst n
          exact ih (v := v) (z := z) htail'

end Reaches

/--
二つの始点の前向き odd-only 軌道が有限時間後に合流する。
「最初から同じ軌道」という意味ではなく、共通の後続点が存在することだけを表す。
-/
def Merges (x y : ℕ) : Prop :=
  ∃ z : ℕ, Reaches x z ∧ Reaches y z

namespace Merges

/-- 任意の値は自分自身と合流する。 -/
@[refl]
theorem refl (x : ℕ) : Merges x x :=
  ⟨x, Reaches.refl x, Reaches.refl x⟩

/-- 合流関係は対称。 -/
@[symm]
theorem symm
    {x y : ℕ}
    (h : Merges x y) :
    Merges y x := by
  rcases h with ⟨z, hxz, hyz⟩
  exact ⟨z, hyz, hxz⟩

/-- 一方向の finite 到達は特に合流を与える。 -/
theorem of_reaches
    {x y : ℕ}
    (h : Reaches x y) :
    Merges x y :=
  ⟨y, h, Reaches.refl y⟩

/--
合流関係は推移的。
中央の始点から得られる二つの合流点を比較し、後ろ側の共通点まで連結する。
-/
@[trans]
theorem trans
    {x y z : ℕ}
    (hxy : Merges x y)
    (hyz : Merges y z) :
    Merges x z := by
  rcases hxy with ⟨a, hxa, hya⟩
  rcases hyz with ⟨b, hyb, hzb⟩
  rcases Reaches.comparable_of_common_start hya hyb with hab | hba
  · exact ⟨b, Reaches.trans hxa hab, hzb⟩
  · exact ⟨a, hxa, Reaches.trans hzb hba⟩

/-- `Merges` は同値関係。 -/
theorem equivalence : Equivalence Merges :=
  ⟨Merges.refl, Merges.symm, Merges.trans⟩

end Merges
end Collatz3
