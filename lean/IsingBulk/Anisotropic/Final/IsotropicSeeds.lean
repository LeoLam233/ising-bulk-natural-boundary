import IsingBulk.Anisotropic.Final.LocalPullback
import IsingBulk.Final.UnconditionalNaturalBoundary
import IsingBulk.HT.Final.FullNaturalBoundary
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! Literal imported normalized full-sum endpoints. In particular LT uses the
normalized exterior theorem, not an enlarged physical right-chart theorem. -/
namespace IsingBulk.Anisotropic
noncomputable section
open Set Filter
open scoped Topology

def isotropicHighPullback : ℂ → ℂ := IsingBulk.HT.Final.interiorFullBulk ∘ Complex.sinh
def isotropicLowPullback : ℂ → ℂ := IsingBulk.Tail.exteriorNormalizedBulk ∘ Complex.sinh

theorem isotropic_high_seed_no_extension {s : ℂ} (hs : ‖s‖ = 1) :
    ¬ HasDomainExtension {w : ℂ | ‖w‖ < 1} IsingBulk.HT.Final.interiorFullBulk s := by
  intro he
  apply IsingBulk.HT.Final.interiorFullBulk_unit_circle_no_extension s hs
  obtain ⟨U,hU,hsU,g,hg,hEq⟩ := he
  exact ⟨U,hU,hsU,g,hg,fun _ hw => hEq ⟨hw.1,hw.2.2⟩⟩

theorem isotropic_low_seed_no_extension {s : ℂ} (hs : ‖s‖ = 1) :
    ¬ HasDomainExtension {w : ℂ | 1 < ‖w‖} IsingBulk.Tail.exteriorNormalizedBulk s :=
  IsingBulk.Final.theorem_nb s hs

theorem isotropicHighPullback_analyticOn :
    AnalyticOnNhd ℂ isotropicHighPullback {z : ℂ | ‖Complex.sinh z‖ < 1} := by
  intro z hz
  exact (IsingBulk.HT.Final.interiorFullBulk_analyticOn (Complex.sinh z) hz).comp
    Complex.analyticAt_sinh

theorem isotropicLowPullback_analyticOn :
    AnalyticOnNhd ℂ isotropicLowPullback {z : ℂ | 1 < ‖Complex.sinh z‖} := by
  intro z hz
  exact (IsingBulk.Tail.exteriorNormalizedBulk_analyticOn (Complex.sinh z) hz).comp
    Complex.analyticAt_sinh

theorem isotropic_high_local_obstruction {D : Set ℂ} {z : ℂ}
    (hz : ‖Complex.sinh z‖ = 1) (hcosh : Complex.cosh z ≠ 0)
    (hside : ∀ᶠ v in 𝓝 z, ‖Complex.sinh v‖ < 1 → v ∈ D) :
    ¬ HasDomainExtension D isotropicHighPullback z := by
  apply no_domain_extension_analytic_pullback (E := {w : ℂ | ‖w‖ < 1}) Complex.analyticAt_sinh
    (by simpa only [(Complex.hasDerivAt_sinh z).deriv] using hcosh) hside
  exact isotropic_high_seed_no_extension hz

theorem isotropic_low_local_obstruction {D : Set ℂ} {z : ℂ}
    (hz : ‖Complex.sinh z‖ = 1) (hcosh : Complex.cosh z ≠ 0)
    (hside : ∀ᶠ v in 𝓝 z, 1 < ‖Complex.sinh v‖ → v ∈ D) :
    ¬ HasDomainExtension D isotropicLowPullback z := by
  apply no_domain_extension_analytic_pullback (E := {w : ℂ | 1 < ‖w‖}) Complex.analyticAt_sinh
    (by simpa only [(Complex.hasDerivAt_sinh z).deriv] using hcosh) hside
  exact isotropic_low_seed_no_extension hz

end
end IsingBulk.Anisotropic
