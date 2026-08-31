import CollatzLean.Collatz2.CSTMicro.MultiCorner.AttachedCanonicalHenselBridge

/-!
# MultiCorner attached branch: entrance depth の 3-adic Hensel 条件

attached straight suffix の normalized quotient recurrence を幅 `W` だけ展開すると、
入口 state `Q₀` と entrance depth `h` は

  3^W Q₀ = 2^W + 2^h Φ

という形になる。

ここで `Φ` は straight corridor の Beatty/checkpoint 配置だけから決まる正規化係数である。
このファイルでは、その展開自体を新しい大きな recurrence proof として重複実装せず、
上の exact identity から直ちに得られる本質的な 3-adic 条件を独立 checkpoint にする。

  3^W ∣ 2^W + 2^h Φ

すなわち数学的には

  2^h Φ ≡ -2^W  (mod 3^W).

attached の free-base `h` は、この条件を満たす residue class に制限される。
-/

namespace Collatz2
namespace CSTMicro
namespace MultiCorner

/--
straight Hensel chain を全幅展開した後に必要な最小整数データ。

`phi` の具体式は既存 canonical quotient chain から供給する。
この packet は final congruence の純算術部分だけを保持する。
-/
structure AttachedEntranceHenselIdentity where
  width : ℕ
  entranceDepth : ℕ
  entranceState : ℤ
  phi : ℤ

  expanded_identity :
    (3 : ℤ) ^ width * entranceState =
      (2 : ℤ) ^ width +
        (2 : ℤ) ^ entranceDepth * phi

namespace AttachedEntranceHenselIdentity

/--
全幅 Hensel identity を modulus `3^W` で読む。

  3^W ∣ 2^W + 2^h Φ.

負数を含む `Int.ModEq` へ無理に変換せず、後段で最も扱いやすい divisor form を正本にする。
-/
theorem threePow_dvd_entranceResidue
    (H : AttachedEntranceHenselIdentity) :
    (3 : ℤ) ^ H.width ∣
      (2 : ℤ) ^ H.width +
        (2 : ℤ) ^ H.entranceDepth * H.phi := by
  refine ⟨H.entranceState, ?_⟩
  exact H.expanded_identity.symm

/--
`Phi` が 3-adic unit であることまで分かっている場合の checkpoint。

ここでは inverse を新しく定義せず、

* `3^W | 2^W + 2^h Phi`
* `3 ∤ Phi`

の二条件を lossless に束ねる。discrete-log/Hensel lifting は次段の arithmetic theorem に渡す。
-/
structure UnitResidueCheckpoint
    (H : AttachedEntranceHenselIdentity) where
  phi_not_three_dvd : ¬ (3 : ℤ) ∣ H.phi

/-- unit checkpoint から divisor form と unit 条件を同時に取り出す。 -/
theorem unitResidue_checkpoint
    (H : AttachedEntranceHenselIdentity)
    (U : UnitResidueCheckpoint H) :
    ((3 : ℤ) ^ H.width ∣
        (2 : ℤ) ^ H.width +
          (2 : ℤ) ^ H.entranceDepth * H.phi) ∧
      ¬ (3 : ℤ) ∣ H.phi := by
  exact ⟨H.threePow_dvd_entranceResidue, U.phi_not_three_dvd⟩

end AttachedEntranceHenselIdentity

end MultiCorner
end CSTMicro
end Collatz2
