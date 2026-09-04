import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleConvergent22Checkpoint


/-!
# 第3例探索: 最後41列への枝圧縮

このファイルは、有限 verifier の直前で使う座標

* `r = p - c`
* `d = c - s`
* `w = attached straight width`

について、すでに得られた `p - s < 42` と attached 幅条件から従う
純粋な自然数算術だけを固定する。

重要:
`last41` 自体の幾何・3進証明をこのファイルで再実行しない。
このファイルは、その証明済み事実を入力として受け取り、後段の有限枝へ
lossless に圧縮する層である。
-/

namespace Collatz2
namespace CSTMicro
namespace ThirdExampleSearch

/--
第3例の最後41列枝を記述する軽量座標。

`c` : critical cut
`s` : criticalization start
`r` : terminal odd-column から cut までの残り幅 `p-c`
`d` : cut から criticalization start までの深さ `c-s`
`w` : attached straight width
-/
structure ThirdExampleLast41TailCoordinates where
  c : ℕ
  s : ℕ
  r : ℕ
  d : ℕ
  w : ℕ
  s_le_c : s ≤ c
  c_le_target : c ≤ thirdExampleTargetP
  r_eq : r = thirdExampleTargetP - c
  d_eq : d = c - s
  /-- 3進 valuation の枝狩りから、start は terminal の最後41列内にある。 -/
  last41 : thirdExampleTargetP - s < 42
  /-- attached straight width `w` は深さ `d` の中に少なくとも `w+1` 列を必要とする。 -/
  attached_width : w + 1 ≤ d

/-- `s ≤ c ≤ p` なので、二つの局所距離は exact に `p-s` を分割する。 -/
theorem thirdExampleLast41_r_add_d_eq
    (B : ThirdExampleLast41TailCoordinates) :
    B.r + B.d = thirdExampleTargetP - B.s := by
  have hsc := B.s_le_c
  have hct := B.c_le_target
  rw [B.r_eq, B.d_eq]
  omega

/-- `p-s < 42` を自然数の閉区間表現 `r+d ≤ 41` に直す。 -/
theorem thirdExampleLast41_r_add_d_le_41
    (B : ThirdExampleLast41TailCoordinates) :
    B.r + B.d ≤ 41 := by
  have hsplit := thirdExampleLast41_r_add_d_eq B
  have hlast := B.last41
  omega

/-- criticalization start は target terminal から高々41 odd-column 左にある。 -/
theorem thirdExampleLast41_target_le_s_add_41
    (B : ThirdExampleLast41TailCoordinates) :
    thirdExampleTargetP ≤ B.s + 41 := by
  have hsc := B.s_le_c
  have hct := B.c_le_target
  have hlast := B.last41
  have hsTarget : B.s ≤ thirdExampleTargetP := by
    omega
  omega

/-- attached 幅が1列以上の深さを要求するので `d` は正。 -/
theorem thirdExampleLast41_d_pos
    (B : ThirdExampleLast41TailCoordinates) :
    0 < B.d := by
  have hwidth := B.attached_width
  omega

/-- `r+d ≤ 41` と `w+1 ≤ d` を合成すると `r+w ≤ 40`。 -/
theorem thirdExampleLast41_r_add_w_le_40
    (B : ThirdExampleLast41TailCoordinates) :
    B.r + B.w ≤ 40 := by
  have hrd := thirdExampleLast41_r_add_d_le_41 B
  have hwidth := B.attached_width
  omega

/-- 特に attached straight width 自体も40以下。 -/
theorem thirdExampleLast41_w_le_40
    (B : ThirdExampleLast41TailCoordinates) :
    B.w ≤ 40 := by
  have hrw := thirdExampleLast41_r_add_w_le_40 B
  omega

/-- 固定 `r` に対し、許される `d` の上端は `41-r`。 -/
theorem thirdExampleLast41_d_le_sub
    (B : ThirdExampleLast41TailCoordinates) :
    B.d ≤ 41 - B.r := by
  have hrd := thirdExampleLast41_r_add_d_le_41 B
  omega

/-- 固定 `w` に対し、attached 条件から `w+1 ≤ d`。後段の branch table の下端。 -/
theorem thirdExampleLast41_d_lower
    (B : ThirdExampleLast41TailCoordinates) :
    B.w + 1 ≤ B.d :=
  B.attached_width

end ThirdExampleSearch
end CSTMicro
end Collatz2
