import IsingBulk.AnisoF002.C03.IsotropicLocalTemperatureCharts
import IsingBulk.AnisoF002.C03.IsotropicPhysicalSeries
import IsingBulk.AnisoF002.C03.PhysicalConjugation

/-!
# Actual radial germs and local physical-domain extensions at lambda one

The germ is at the actual dispersion value 2 cos alpha. The inverse of
t + t^{-1} and the inverse sinh temperature charts are constructed
analytically, and equality is required along the exterior radial path.
The signed odd reflection retains its full minus sign and total angle pi.
-/

noncomputable section
namespace IsingBulk.AnisoF002.Isotropic
open scoped Topology ComplexConjugate
open Set Filter IsingBulk.Anisotropic IsingBulk.AnisoF002.Geometry
open IsingBulk.AnisoF002.RegularTail.C03

def HasIsotropicRadialGerm (F : ℂ → ℂ) (α : ℝ) : Prop :=
  ∃ g : ℂ → ℂ, AnalyticAt ℂ g ((2 * Real.cos α : ℝ) : ℂ) ∧
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      g (isotropicRadialParameter α ε) = F (isotropicRadialParameter α ε)

theorem isotropic_radial_germ_of_domain_extension
    {D : Set ℂ} {F G Z : ℂ → ℂ} {z : ℂ} {α : ℝ}
    (hα : 0 < α ∧ α < Real.pi)
    (hZa : AnalyticAt ℂ Z (Complex.exp ((α : ℂ) * Complex.I)))
    (hZ0 : Z (Complex.exp ((α : ℂ) * Complex.I)) = z)
    (himage : ∀ᶠ ε in 𝓝[>] (0 : ℝ), Z (isotropicExteriorRadial α ε) ∈ D)
    (hidentity : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      F (Z (isotropicExteriorRadial α ε)) = G (isotropicRadialParameter α ε))
    (he : HasDomainExtension D F z) : HasIsotropicRadialGerm G α := by
  obtain ⟨U, hU, hzU, g, hg, heq⟩ := he
  obtain ⟨T, hTa, hT0, _, hTleft⟩ := exists_isotropic_joukowski_inverse hα
  have hZTa : AnalyticAt ℂ (fun S => Z (T S)) ((2 * Real.cos α : ℝ) : ℂ) := by
    apply AnalyticAt.comp _ hTa
    simpa only [hT0] using hZa
  have hga : AnalyticAt ℂ (fun S => g (Z (T S))) ((2 * Real.cos α : ℝ) : ℂ) := by
    apply AnalyticAt.comp _ hZTa
    simpa only [hT0, hZ0] using hg z hzU
  refine ⟨fun S => g (Z (T S)), hga, ?_⟩
  have ht : Tendsto (isotropicExteriorRadial α) (𝓝[>] (0 : ℝ))
      (𝓝 (Complex.exp ((α : ℂ) * Complex.I))) :=
    (isotropicExteriorRadial_tendsto α).mono_left nhdsWithin_le_nhds
  have hzt : Tendsto (fun ε => Z (isotropicExteriorRadial α ε))
      (𝓝[>] (0 : ℝ)) (𝓝 z) := by
    simpa only [hZ0, Function.comp_def] using hZa.continuousAt.tendsto.comp ht
  filter_upwards [ht.eventually hTleft, hzt.eventually (hU.mem_nhds hzU), himage,
    hidentity] with ε hT hUz hD hFG
  change g (Z (T (isotropicExteriorRadial α ε + (isotropicExteriorRadial α ε)⁻¹))) = _
  rw [hT]
  exact (heq ⟨hUz, hD⟩).trans hFG

theorem isotropic_low_canonical_radial_germ {z : ℂ} {α : ℝ} (m : ℕ)
    (hα : 0 < α ∧ α < Real.pi) (hx : 0 < z.re)
    (he : Complex.sinh z = Complex.exp ((α : ℂ) * Complex.I))
    (hext : HasDomainExtension (omegaL 1) (canonicalAngularTailF002 1 m) z) :
    HasIsotropicRadialGerm (isotropicFullParticleSeries m 0 1) α := by
  obtain ⟨Z, hZa, hZ0, hZeq, hZD⟩ := exists_isotropic_low_temperature_chart hx he
  apply isotropic_radial_germ_of_domain_extension hα hZa hZ0 hZD _ hext
  have ht : Tendsto (isotropicExteriorRadial α) (𝓝[>] (0 : ℝ))
      (𝓝 (Complex.exp ((α : ℂ) * Complex.I))) :=
    (isotropicExteriorRadial_tendsto α).mono_left nhdsWithin_le_nhds
  filter_upwards [ht.eventually hZeq, isotropicRadialParameter_eventually_upper hα] with ε heq hu
  have hS : isotropicPhysicalParameter (Z (isotropicExteriorRadial α ε)) =
      isotropicRadialParameter α ε := heq.2
  rw [← hS]
  exact (isotropicFullParticleSeries_eq_canonical m (hS ▸ hu)).symm

theorem isotropic_high_canonical_radial_germ {z : ℂ} {α : ℝ} (m : ℕ)
    (hα : 0 < α ∧ α < Real.pi) (hx : z.re ≠ 0) (hy : |z.im| < Real.pi / 2)
    (he : Complex.sinh z = (Complex.exp ((α : ℂ) * Complex.I))⁻¹)
    (hext : HasDomainExtension (omegaH 1) (canonicalAngularTailF002 1 m) z) :
    HasIsotropicRadialGerm (isotropicFullParticleSeries m 0 1) α := by
  obtain ⟨Z, hZa, hZ0, hZeq, hZD⟩ := exists_isotropic_high_temperature_chart hx hy he
  apply isotropic_radial_germ_of_domain_extension hα hZa hZ0 hZD _ hext
  have ht : Tendsto (isotropicExteriorRadial α) (𝓝[>] (0 : ℝ))
      (𝓝 (Complex.exp ((α : ℂ) * Complex.I))) :=
    (isotropicExteriorRadial_tendsto α).mono_left nhdsWithin_le_nhds
  filter_upwards [ht.eventually hZeq, isotropicRadialParameter_eventually_upper hα] with ε heq hu
  have hS : isotropicPhysicalParameter (Z (isotropicExteriorRadial α ε)) =
      isotropicRadialParameter α ε := heq.2
  rw [← hS]
  exact (isotropicFullParticleSeries_eq_canonical m (hS ▸ hu)).symm

theorem isotropic_odd_radial_germ_reflection {α : ℝ} (hα : 0 < α ∧ α < Real.pi)
    (hgerm : HasIsotropicRadialGerm (isotropicFullParticleSeries 0 0 1) (Real.pi - α)) :
    HasIsotropicRadialGerm (isotropicFullParticleSeries 0 Real.pi (-1)) α := by
  obtain ⟨g, hga, heq⟩ := hgerm
  have hc : ((2 * Real.cos (Real.pi - α) : ℝ) : ℂ) =
      -((2 * Real.cos α : ℝ) : ℂ) := by rw [Real.cos_pi_sub]; push_cast; ring
  have hgg : AnalyticAt ℂ (fun S => conj (g (conj S))) (-((2 * Real.cos α : ℝ) : ℂ)) := by
    simpa only [hc, map_neg, Complex.conj_ofReal] using analyticAt_twice_conjugated hga
  have ha : AnalyticAt ℂ (fun S => -conj (g (-conj S))) ((2 * Real.cos α : ℝ) : ℂ) := by
    have hh : AnalyticAt ℂ (fun S => conj (g (-conj S))) ((2 * Real.cos α : ℝ) : ℂ) := by
      simpa only [Function.comp_def, map_neg] using hgg.comp analyticAt_id.neg
    convert hh.neg using 1
  refine ⟨fun S => -conj (g (-conj S)), ha, ?_⟩
  filter_upwards [heq, isotropicRadialParameter_eventually_upper hα] with ε he hu
  rw [← isotropicRadialParameter_neg_conj, he, isotropicRadialParameter_neg_conj,
    isotropic_odd_complete_series_neg_conj hu, map_neg, starRingEnd_self_apply, neg_neg]

theorem isotropic_even_radial_germ_reflection {α : ℝ} (hα : 0 < α ∧ α < Real.pi)
    (hgerm : HasIsotropicRadialGerm (isotropicFullParticleSeries 1 0 1) (Real.pi - α)) :
    HasIsotropicRadialGerm (isotropicFullParticleSeries 1 0 1) α := by
  obtain ⟨g, hga, heq⟩ := hgerm
  have hc : ((2 * Real.cos (Real.pi - α) : ℝ) : ℂ) =
      -((2 * Real.cos α : ℝ) : ℂ) := by rw [Real.cos_pi_sub]; push_cast; ring
  have hgg : AnalyticAt ℂ (fun S => conj (g (conj S))) (-((2 * Real.cos α : ℝ) : ℂ)) := by
    simpa only [hc, map_neg, Complex.conj_ofReal] using analyticAt_twice_conjugated hga
  have ha : AnalyticAt ℂ (fun S => conj (g (-conj S))) ((2 * Real.cos α : ℝ) : ℂ) := by
    simpa only [Function.comp_def, map_neg] using hgg.comp analyticAt_id.neg
  refine ⟨fun S => conj (g (-conj S)), ha, ?_⟩
  filter_upwards [heq, isotropicRadialParameter_eventually_upper hα] with ε he hu
  rw [← isotropicRadialParameter_neg_conj, he, isotropicRadialParameter_neg_conj,
    isotropic_even_complete_series_neg_conj hu, starRingEnd_self_apply]

end IsingBulk.AnisoF002.Isotropic
