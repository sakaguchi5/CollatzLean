import CollatzLean.Collatz2.ObstructionAudit.ConstraintPackets
import CollatzLean.Collatz2.ObstructionAudit.MainModel
import CollatzLean.Collatz2.ObstructionAudit.SharpKappaOneModel
import CollatzLean.Collatz2.ObstructionAudit.WordRealizabilityBoundary
import CollatzLean.Collatz2.ObstructionAudit.TranslationShadowAudit

/-!
# Collatz2 Obstruction Audit

`EventuallyNegative` から抽出した obstruction 候補について、
どの条件集合まで明示的な無限 model が存在するかを formal に監査する入口。

現在固定している事実:

* negative affine positive return は無限反復可能。
* primitive-center / return-gap arithmetic を加えても可能。
* positive separation (`kappa > 0`) と center escape を加えても可能。
* diagonal を genuine `3^p / 2^H` にし、exponent `1` から始まる
  word profile まで加えても可能。
* primitive affine level では `kappa = 1` を全点に課しても可能。
* canonical start residue だけを genuine にしても relaxed infinite model は残る。
* しかしその canonical-residue witness は、exact translation より薄い
  endpoint-side translation shadow `mod 2*C` と genuine path-size bound `B < A*C`
  の時点ですでに消える。
* exact word translation `B = Word.affineConst word` は、それらの shadow を
  すべて同時に固定し、さらに `RealizationRecovery` を通して `Runs` を復元する。

この directory は `EventuallyNegative` な genuine Collatz orbit の存在を
主張するものではない。新しい obstruction 候補が得られたら displacement form の
どの shadow を固定しているかを明示し、既存 witness が延長可能かを検査する
regression suite として使う。
-/

namespace Collatz2
namespace ObstructionAudit

/--
現在の strongest old-style audited packet は inhabitant を持つ。
従って、ここに列挙した diagonal/profile 条件群だけでは `False` は導けない。
-/
theorem current_obstruction_packet_satisfiable :
    Nonempty DiagonalWordProfileConstraints :=
  MainModel.constraints_satisfiable

/-- sharp `kappa = 1` packet も primitive affine level では inhabitant を持つ。 -/
theorem sharp_kappa_one_packet_satisfiable :
    Nonempty SharpKappaOneConstraints :=
  SharpKappaOneModel.constraints_satisfiable

end ObstructionAudit
end Collatz2
