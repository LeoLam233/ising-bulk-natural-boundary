import IsingBulk.HT.Tail.CoupledOccupancy
import IsingBulk.HT.Tail.CoupledPlateau
import IsingBulk.HT.Tail.NoncancellationBridge
import IsingBulk.HT.Tail.FullSiteDomination
import IsingBulk.HT.Tail.SignedOddLargeCurrent
import IsingBulk.HT.Tail.RightOddSeries
import IsingBulk.HT.Tail.SignedHighKSTail
import IsingBulk.HT.Tail.SignedOriginalKSSummability
import IsingBulk.HT.Tail.SignedSelectorOrderSplit
import IsingBulk.HT.Tail.SignedCommonSourceSummability
import IsingBulk.HT.Tail.SignedCommonCompletedParameters
import IsingBulk.HT.Tail.SignedOddTailDomination
import IsingBulk.HT.Tail.SignedExactSectorNormDomination
import IsingBulk.HT.Tail.SignedExteriorNegativeTheorem
import IsingBulk.HT.Tail.SignedCompactRightWindow
import IsingBulk.HT.Tail.SignedMixedLeftAsymptotic
import IsingBulk.HT.Tail.NegativeAbsoluteOddTailAssembly
import IsingBulk.HT.Tail.NegativeOriginalOddTailAssembly
import IsingBulk.HT.Tail.FullOddTailAssembly

/-!
HT complete odd offsite tail source aggregate. It includes actual upper/right
normal convergence, the positive selected all-order infinite tail, the signed
reflected all-order infinite tail, the original negative integer-angle
family tail, and their epsilon-scaled complex limits.
The complete onsite boundary subpower series and full-site higher tail
are included. Physical natural-boundary assembly is separate. Every new HT source requires pinned-toolchain compilation
and kernel-axiom audit; source closure is not verified proof completion.
-/
