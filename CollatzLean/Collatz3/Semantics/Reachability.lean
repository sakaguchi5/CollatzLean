import CollatzLean.Collatz3.Semantics.Runs

/-!
# Collatz3: 有限到達と軌道合流

`Runs` は指数語を保持した有限実軌道である。
このファイルでは、指数語を忘れた有限到達 `Reaches` と、
二つの始点が共通の後続点を持つことを表す `Merges` だけを薄い語彙として導入する。

1 step の決定性は `OddStep.deterministic`、finite run の prefix 決定性は `Runs` 層に置く。
`Merges` の推移性は定義に埋め込まず、決定性と `Runs` の連結から theorem として導く。
-/

namespace Collatz3

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
これは `Runs.prefixComparable_of_common_start` の word 情報を忘れた像。
-/
theorem comparable_of_common_start
    {x y z : ℕ}
    (hxy : Reaches x y)
    (hxz : Reaches x z) :
    Reaches y z ∨ Reaches z y := by
  rcases hxy with ⟨u, hu⟩
  rcases hxz with ⟨v, hv⟩
  rcases Runs.prefixComparable_of_common_start hu hv with
      ⟨t, _hEq, hRun⟩ | ⟨t, _hEq, hRun⟩
  · exact Or.inl ⟨t, hRun⟩
  · exact Or.inr ⟨t, hRun⟩

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
