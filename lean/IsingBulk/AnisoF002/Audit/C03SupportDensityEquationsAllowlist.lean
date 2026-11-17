import IsingBulk.AnisoF002.Audit.C03SupportAllowlist

/-! Three independently inspected literal definitional equations. Stored proofs are Eq.refl; twelve other historical dependencies match existing inspected finite catalogues. No endpoint or namespace admission. -/

namespace AnisoF002Audit.C03DensityEquations
open Lean AnisoF002Audit.C03

def densityEquationRules : Array HistoricalRule := #[
  { name := "IsingBulk.Anisotropic.FormFactors.commonDensity.eq_1".toName, owner := "IsingBulk.AnisoF002.C03.PhysicalAxisCoefficients".toName, kind := "theorem", typeHash := 3033811172, valueHash := some 1313434353, group := "parent_inspected_density_definition_refl" },
  { name := "IsingBulk.Anisotropic.FormFactors.fullDensity.eq_1".toName, owner := "IsingBulk.AnisoF002.C03.PhysicalAxisCoefficients".toName, kind := "theorem", typeHash := 3484470503, valueHash := some 860665917, group := "parent_inspected_density_definition_refl" },
  { name := "IsingBulk.HT.Contour.physicalDependentAngles.eq_1".toName, owner := "IsingBulk.AnisoF002.C03.PhysicalAngularIdentification".toName, kind := "theorem", typeHash := 1113643053, valueHash := some 4017941786, group := "parent_inspected_density_definition_refl" }
]

end AnisoF002Audit.C03DensityEquations
