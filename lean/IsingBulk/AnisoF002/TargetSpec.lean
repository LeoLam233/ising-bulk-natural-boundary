import IsingBulk.Anisotropic.Final.CompleteTarget

/-!
# The unchanged, unproved terminal specification

`RequiredStatement` is a definition of a proposition.  It is not a proof of
that proposition, not an axiom, and not a replacement terminal theorem.
The intended theorem name is
`IsingBulk.AnisoF002.full_uniform_field_conclusion`.

This partial development deliberately leaves that name undeclared until all
of F002's mathematical obligations are closed with an admissible stored
proof route.  The statement uses the existing terminal type and exactly the
two original published real physical premises.  In particular it imposes no
`lam ≠ 1`, no generic-ratio condition, and no boundary exceptions.
-/

namespace IsingBulk.AnisoF002
open IsingBulk.Anisotropic
open IsingBulk.Anisotropic.FormFactors IsingBulk.Anisotropic.PhysicalField

def RequiredStatement : Prop :=
  ∀ {J lam : ℝ}, 0 < J → 0 < lam →
    ∀ {corrH corrL : ℝ → LatticeSite → ℝ} {mH mL : ℝ → ℝ → ℝ},
      PublishedRealSpinFormFactors lam corrH corrL →
      PublishedRealGibbsFields J lam corrH corrL mH mL →
      FullUniformFieldConclusion J lam corrH corrL mH mL

/-- The separately requested analytic endpoint is also an open specification,
not an axiom or a theorem derived from the partial lemmas. -/
def RequiredAnalyticStatement : Prop :=
  ∀ {J lam : ℝ}, 0 < J → 0 < lam →
    ∀ {corrH corrL : ℝ → LatticeSite → ℝ},
      PublishedRealSpinFormFactors lam corrH corrL → FullAnalyticConclusion J lam

end IsingBulk.AnisoF002
