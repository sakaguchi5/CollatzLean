import CollatzLean.CollatzSecondLayer3.FutureMinimumSpecialC3
import CollatzLean.CollatzFirstLayer.NegativeShadowIteration

/-!
# source-preserving Special C3 seedへのshadow tower付加

各Special C3 seedの最初のexact exponent 1 re-anchoringを入口とし、
その後のnegative shadowを自動反復する。
元のfuture-minimum normalization履歴と縦方向のshadow towerを同時に参照できる。
-/

namespace CollatzCore.SpecialC3At

open CollatzCore
open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

/-- 最初のre-anchoring後のcanonical run。 -/
private theorem firstReanchoring_canonical_run
    {O : OddOrbit} {start length : ℕ}
    (S : SpecialC3At O start length) :
    Runs
      (O.segmentWord start length ++
        [S.firstNegativeShadowStep.exponent])
      (canonicalStart
        (O.segmentWord start length ++
          [S.firstNegativeShadowStep.exponent]))
      (canonicalEnd
        (O.segmentWord start length ++
          [S.firstNegativeShadowStep.exponent])) := by
  have h := S.firstReanchoring.runs
  rw [S.firstReanchoring.start_eq_canonical,
    S.firstReanchoring.finish_eq_canonical] at h
  exact h

/--
一つのSpecial C3 seedから始まる無限negative shadow re-anchoring tower。
深さ0は最初のexact exponent 1 re-anchoring後のwordである。
-/
noncomputable def shadowReanchoringTower
    {O : OddOrbit} {start length : ℕ}
    (S : SpecialC3At O start length) :
    NegativeShadowReanchoringTowerData
      (O.segmentWord start length ++
        [S.firstNegativeShadowStep.exponent]) :=
  NegativeShadowReanchoringTowerData.ofCanonicalNegativeShadow
    S.firstReanchoring_canonical_run
    S.firstShadowMagnitude_pos
    S.firstShadowMagnitude_odd
    S.firstReanchoring.predecessorShadow_eq

/-- shadow towerのsource wordは元wordへexponent 1をappendしたもの。 -/
theorem shadowReanchoringTower_sourceWord_eq
    {O : OddOrbit} {start length : ℕ}
    (S : SpecialC3At O start length) :
    O.segmentWord start length ++
        [S.firstNegativeShadowStep.exponent] =
      O.segmentWord start length ++ [1] := by
  rfl

/-- 全shadow tower段で元Special C3 seedのnegative centerを保存する。 -/
theorem shadowReanchoringTower_center_eq_source
    {O : OddOrbit} {start length : ℕ}
    (S : SpecialC3At O start length)
    (n : ℕ) :
    predecessorStart (S.shadowReanchoringTower.word n) =
      predecessorStart (O.segmentWord start length) := by
  calc
    predecessorStart (S.shadowReanchoringTower.word n)
        = predecessorStart
            (O.segmentWord start length ++
              [S.firstNegativeShadowStep.exponent]) :=
      S.shadowReanchoringTower.predecessorStart_word_eq_source n
    _ = predecessorStart (O.segmentWord start length) :=
      S.firstReanchoring.predecessorStart_eq

end CollatzCore.SpecialC3At

namespace CollatzSecondLayer3

open CollatzCore
open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

namespace FutureMinimumSpecialC3TowerData

/-- source-preserving towerのj番目のSpecial C3 seedに付随するshadow tower。 -/
noncomputable def shadowTower
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    (j : ℕ) :
    NegativeShadowReanchoringTowerData
      (R.word j ++ [(R.special j).firstNegativeShadowStep.exponent]) := by
  simpa [word, start, length, terminalTime] using
    (R.special j).shadowReanchoringTower

/-- j番目のseedのshadow towerにおけるn段目のword。 -/
noncomputable def shadowWord
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    (j n : ℕ) : ExpWord :=
  (R.shadowTower j).word n

/-- j番目のseedから追加された最初のn個のshadow exponent word。 -/
noncomputable def shadowExtensionWord
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    (j n : ℕ) : ExpWord :=
  (R.shadowTower j).extensionWord n

/-- j番目のseedのshadow towerにおけるn段目のmagnitude。 -/
noncomputable def shadowMagnitudeAt
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    (j n : ℕ) : ℕ :=
  (R.shadowTower j).magnitude n

/-- j番目のseedのshadow towerにおけるn段目の次指数。 -/
noncomputable def shadowExponent
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    (j n : ℕ) : ℕ :=
  (R.shadowTower j).exponent n

/-- 深さ0のshadow wordはseed wordへ最初のexact exponent 1をappendしたもの。 -/
theorem shadowWord_zero
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    (j : ℕ) :
    R.shadowWord j 0 = R.word j ++ [1] := by
  calc
    R.shadowWord j 0
        = R.word j ++
            [(R.special j).firstNegativeShadowStep.exponent] := by
              exact (R.shadowTower j).word_zero
    _ = R.word j ++ [1] := by rfl

/-- shadow extension wordの長さは反復深さに一致する。 -/
theorem shadowExtensionWord_length
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    (j n : ℕ) :
    (R.shadowExtensionWord j n).length = n :=
  (R.shadowTower j).extensionWord_length n

/-- shadow wordは最初のre-anchored wordへ有限prefixをappendしたもの。 -/
theorem shadowWord_eq_seed_append_extensionWord
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    (j n : ℕ) :
    R.shadowWord j n =
      (R.word j ++ [1]) ++ R.shadowExtensionWord j n := by
  calc
    R.shadowWord j n
        =
      (R.word j ++
        [(R.special j).firstNegativeShadowStep.exponent]) ++
        R.shadowExtensionWord j n :=
      (R.shadowTower j).word_eq_source_append_extensionWord n
    _ = (R.word j ++ [1]) ++ R.shadowExtensionWord j n := by rfl

/-- shadow wordの一段append式。 -/
theorem shadowWord_succ
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    (j n : ℕ) :
    R.shadowWord j (n + 1) =
      R.shadowWord j n ++ [R.shadowExponent j n] :=
  (R.shadowTower j).word_succ n

/-- shadow towerの全段で元seedのcenterを保存する。 -/
theorem predecessorStart_shadowWord_eq_center
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    (j n : ℕ) :
    predecessorStart (R.shadowWord j n) = R.center j := by
  calc
    predecessorStart (R.shadowWord j n)
        = predecessorStart
            (R.word j ++
              [(R.special j).firstNegativeShadowStep.exponent]) :=
      (R.shadowTower j).predecessorStart_word_eq_source n
    _ = predecessorStart (R.word j) :=
      (R.firstReanchoring j).predecessorStart_eq
    _ = R.center j := rfl

/-- 各shadow magnitudeは正。 -/
theorem shadowMagnitudeAt_pos
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    (j n : ℕ) :
    0 < R.shadowMagnitudeAt j n :=
  (R.shadowTower j).magnitude_pos n

/-- 各shadow magnitudeは奇数。 -/
theorem shadowMagnitudeAt_odd
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    (j n : ℕ) :
    Odd (R.shadowMagnitudeAt j n) :=
  (R.shadowTower j).magnitude_odd n

/-- 各seed・各深さのshadow step equation。 -/
theorem shadowStepEquation
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    (j n : ℕ) :
    2 ^ R.shadowExponent j n *
          R.shadowMagnitudeAt j (n + 1) + 1 =
      3 * R.shadowMagnitudeAt j n :=
  (R.shadowTower j).stepEquation n

end FutureMinimumSpecialC3TowerData
end CollatzSecondLayer3
