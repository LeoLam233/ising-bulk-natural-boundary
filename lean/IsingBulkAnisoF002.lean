import IsingBulk.AnisoF002.Geometry.EndpointBridge
import IsingBulk.AnisoF002.RegularTail.CollisionBudget
import IsingBulk.AnisoF002.RegularTail.GaussianEnvelope
import IsingBulk.AnisoF002.RegularTail.SchurContraction
import IsingBulk.AnisoF002.RegularTail.VandermondeBlock
import IsingBulk.AnisoF002.NegativeHT.All
import IsingBulk.AnisoF002.Isotropic.All

/-!
# F002 additive partial mathematical development

This is the root for the newly proved lemmas and their official fresh kernel
replay.  It does not declare `full_uniform_field_conclusion`.  The exact open
terminal proposition is stored separately in `IsingBulk.AnisoF002.TargetSpec`
and checked by `IsingBulk.AnisoF002.Audit.TargetContract`.

No historical completed endpoint or audit-only control is imported here.
Only the five primitive frozen spectral definitions are used by the endpoint
bridge; all remaining mathematical dependencies are Mathlib or new F002 code.
-/
