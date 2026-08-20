import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBSingleCornerSmallRootReduction
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBSingleCornerLeftSmallRoot
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBSingleCornerRightShiftedSmallRoot

/-!
# Pure B single-corner small-root stage

1. polynomial / dyadic-size reduction と `b+n+s=m`,
2. left origin-critical prefix -> BoundaryXiCandidate / precision bound,
3. right shifted-critical suffix -> terminal record candidate / polylog bound

の aggregate import。
-/
