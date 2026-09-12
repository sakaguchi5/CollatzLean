import CollatzLean.Collatz3.CSTMicro.Path
import CollatzLean.Collatz3.CSTMicro.Affine
import CollatzLean.Collatz3.CSTMicro.Residue
import CollatzLean.Collatz3.CSTMicro.FirstPassageArithmetic
import CollatzLean.Collatz3.CSTMicro.Capacity

-- Stage 2A: realization / lift / CST criterion
import CollatzLean.Collatz3.CSTMicro.Realization
import CollatzLean.Collatz3.CSTMicro.LiftClassification
import CollatzLean.Collatz3.CSTMicro.CSTCriterion

-- Stage 2B: standard parity と odd-only exponent word の exact bridge
import CollatzLean.Collatz3.CSTMicro.ParityExpansion
import CollatzLean.Collatz3.CSTMicro.AffineExpansion
import CollatzLean.Collatz3.CSTMicro.CriticalExpansion
import CollatzLean.Collatz3.CSTMicro.Compression

-- Stage 3: Beatty roof による affine numerator の deterministic sharp envelope
import CollatzLean.Collatz3.CSTMicro.RoofEnvelope

-- Stage 4: pure 2--3 critical gap interface と single-lift bridge
import CollatzLean.Collatz3.CSTMicro.CriticalGapBridge

-- Stage 5: standard first-passage -> canonical critical word -> admissible profile
import CollatzLean.Collatz3.CSTMicro.ProfileExtraction
import CollatzLean.Collatz3.CSTMicro.ProfileReindex

-- Stage 6: odd endpoint -> actual first-passage -> canonical R/Y/Q
import CollatzLean.Collatz3.CSTMicro.OddEndpointCanonical

-- Stage 7: RecordFerrers compatibility -> shape-sensitive B/R/Q corridor
import CollatzLean.Collatz3.CSTMicro.RecordCompatibility
import CollatzLean.Collatz3.CSTMicro.RecordShapeEnvelope
import CollatzLean.Collatz3.CSTMicro.RecordSurvivor

set_option linter.style.header false
