import IsingBulk.Anisotropic.Final.IsotropicSeeds
import IsingBulk.Anisotropic.Geometry.IsotropicDomains

namespace IsingBulk.Anisotropic
noncomputable section
open Set Filter
open scoped Topology

theorem isotropicHighPullback_analyticOn_omega :
    AnalyticOnNhd ℂ isotropicHighPullback (omegaH 1) := by
  intro z hz
  exact isotropicHighPullback_analyticOn z ((mem_omegaH_one_iff z).mp hz).2

theorem isotropicLowPullback_analyticOn_omega :
    AnalyticOnNhd ℂ isotropicLowPullback (omegaL 1) := by
  intro z hz
  exact isotropicLowPullback_analyticOn z ((mem_omegaL_one_iff z).mp hz).2

theorem isotropic_high_no_extension_in_strip {z : ℂ}
    (hz : ‖Complex.sinh z‖ = 1) (hcosh : Complex.cosh z ≠ 0)
    (him : |z.im| < Real.pi/2) :
    ¬ HasDomainExtension (omegaH 1) isotropicHighPullback z := by
  apply isotropic_high_local_obstruction hz hcosh
  have hnear : ∀ᶠ v : ℂ in 𝓝 z, |v.im| < Real.pi/2 :=
    (isOpen_lt Complex.continuous_im.abs continuous_const).mem_nhds him
  filter_upwards [hnear] with v hv
  intro hnorm
  exact (mem_omegaH_one_iff v).mpr ⟨hv,hnorm⟩

theorem isotropic_low_no_extension_right {z : ℂ}
    (hz : ‖Complex.sinh z‖ = 1) (hcosh : Complex.cosh z ≠ 0)
    (hre : 0 < z.re) :
    ¬ HasDomainExtension (omegaL 1) isotropicLowPullback z := by
  apply isotropic_low_local_obstruction hz hcosh
  have hnear : ∀ᶠ v : ℂ in 𝓝 z, 0 < v.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hre
  filter_upwards [hnear] with v hv
  intro hnorm
  exact (mem_omegaL_one_iff v).mpr ⟨hv,hnorm⟩

end
end IsingBulk.Anisotropic
