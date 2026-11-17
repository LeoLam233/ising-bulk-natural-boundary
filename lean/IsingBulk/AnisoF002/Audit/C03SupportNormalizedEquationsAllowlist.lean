import IsingBulk.AnisoF002.Audit.C03SupportAllowlist

/-! Two independently inspected literal definitional equations. Each stored proof is Eq.refl; the 38 other historical dependencies exactly match prior inspected finite catalogues. No endpoint or namespace admission. -/

namespace AnisoF002Audit.C03NormalizedEquations
open Lean AnisoF002Audit.C03

def normalizedEquationRules : Array HistoricalRule := #[
  { name := "IsingBulk.Anisotropic.FormFactors.highNormalizedBulk.eq_1".toName, owner := "IsingBulk.Anisotropic.Final.PhysicalIdentification".toName, kind := "theorem", typeHash := 706991127, valueHash := some 31698844, group := "parent_inspected_normalized_definition_refl" },
  { name := "IsingBulk.Anisotropic.FormFactors.lowNormalizedBulk.eq_1".toName, owner := "IsingBulk.Anisotropic.Final.PhysicalIdentification".toName, kind := "theorem", typeHash := 3369310446, valueHash := some 1204653230, group := "parent_inspected_normalized_definition_refl" }
]

end AnisoF002Audit.C03NormalizedEquations
