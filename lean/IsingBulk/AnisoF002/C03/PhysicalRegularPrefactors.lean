import IsingBulk.AnisoF002.C03.PhysicalBranchExtension
import IsingBulk.AnisoF002.C03.EndpointCharts

/-!
# Actual regular-edge prefactor cancellation

Regularity itself excludes the fourth-root zeros: the unsquared spectral
incidence and Cramer's determinant force a unit endpoint if p²=1.  Thus the
actual chosen prefactors extend nonvanishingly at every regular physical
frontier point, and multiplication preserves the F002 obstruction there.
-/

namespace IsingBulk.AnisoF002.Physical
noncomputable section
open IsingBulk.Anisotropic IsingBulk.Anisotropic.FormFactors
open Geometry Set Filter
open scoped Topology

theorem product_sq_one_unit_incidence {lam : ℝ} {z : ℂ}
    (hp : spectralProduct lam z ^ 2 = 1) :
    ∃ u v : ℝ, (u = 1 ∨ u = -1) ∧ (v = 1 ∨ v = -1) ∧
      spectralA lam z = spectralS z * (u : ℂ) + spectralT lam z * (v : ℂ) := by
  rcases sq_eq_one_iff.mp hp with hp | hp
  · have hh := spectral_product_minus_factor lam z
    rw [hp, sub_self, zero_pow two_ne_zero] at hh
    rcases mul_eq_zero.mp hh with hh | hh
    · refine ⟨1, 1, Or.inl rfl, Or.inl rfl, ?_⟩
      push_cast
      linear_combination hh
    · refine ⟨-1, -1, Or.inr rfl, Or.inr rfl, ?_⟩
      push_cast
      linear_combination hh
  · have hh := spectral_product_plus_factor lam z
    rw [hp, neg_add_cancel, zero_pow two_ne_zero] at hh
    rcases mul_eq_zero.mp hh with hh | hh
    · refine ⟨1, -1, Or.inl rfl, Or.inr rfl, ?_⟩
      push_cast
      linear_combination hh
    · refine ⟨-1, 1, Or.inr rfl, Or.inl rfl, ?_⟩
      push_cast
      linear_combination hh

theorem regular_boundary_product_sq_ne_one {lam : ℝ} (hlam : 0 < lam)
    {D : Set ℂ} (hD : frontier D ⊆ endpointLocusF002 lam) {z : ℂ}
    (hz : z ∈ regularBoundaryF002 lam D) : spectralProduct lam z ^ 2 ≠ 1 := by
  intro hp
  obtain ⟨u', v', hu', hv', hinc'⟩ := product_sq_one_unit_incidence hp
  rcases regularBoundaryF002_factors hlam hD hz with hfirst | hsecond
  · obtain ⟨hdet, u, e, hu, _, hinc⟩ :=
      regular_first_endpoint_exists_all_re hlam hz.2.1 hfirst.1 hfirst.2
    have hue : u = u' := (cramerU_of_incidence hdet hinc).symm.trans
      (cramerU_of_incidence hdet hinc')
    rcases hu' with hu' | hu' <;> rw [hue, hu'] at hu <;> norm_num at hu
  · obtain ⟨v, e, d, hv, _, hinc, hdet, _⟩ :=
      regular_second_endpoint_chart_all_re hlam hz.2.1 hsecond.1 hsecond.2
    have hve : v = v' := (cramerV_of_incidence hdet hinc).symm.trans
      (cramerV_of_incidence hdet hinc')
    rcases hv' with hv' | hv' <;> rw [hve, hv'] at hv <;> norm_num at hv

theorem low_frontier_product_ne_zero_of_re_ne_zero {lam : ℝ} (hlam : 0 < lam)
    {z : ℂ} (hz : z ∈ frontier (omegaL lam)) (hx : z.re ≠ 0) :
    spectralProduct lam z ≠ 0 := by
  have he : lowProfileF002 lam z.im = z.re := by
    have hh : z ∈ frontier (omegaLF002 lam) := hz
    simpa only [frontier_omegaLF002 hlam, Set.mem_ofPred_eq] using hh
  have hre : 0 < z.re := lt_of_le_of_ne (he ▸ lowProfile_nonneg hlam z.im) hx.symm
  apply mul_ne_zero (spectralS_ne_zero_of_re_pos hre)
  exact spectralS_ne_zero_of_re_pos (by
    simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero] using mul_pos hlam hre)

theorem high_regular_prefactor_nonzero_extension {lam : ℝ} (hlam : 0 < lam)
    {z : ℂ} (hz : z ∈ regularBoundaryF002 lam (omegaH lam)) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g z ∧ g z ≠ 0 ∧
      ∀ᶠ w in 𝓝 z, w ∈ omegaH lam → g w = highPrefactor lam w :=
  highPrefactor_local_nonzero_extension hlam hz.1 hz.2.1
    (regular_boundary_product_sq_ne_one hlam (frontier_omegaHF002_subset_endpoint hlam) hz)

theorem low_regular_prefactor_nonzero_extension {lam : ℝ} (hlam : 0 < lam)
    {z : ℂ} (hz : z ∈ regularBoundaryF002 lam (omegaL lam)) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g z ∧ g z ≠ 0 ∧
      ∀ᶠ w in 𝓝 z, w ∈ omegaL lam → g w = lowPrefactor lam w :=
  lowPrefactor_local_nonzero_extension hlam hz.1
    (low_frontier_product_ne_zero_of_re_ne_zero hlam hz.1 hz.2.1)
    (regular_boundary_product_sq_ne_one hlam (frontier_omegaLF002_subset_endpoint hlam) hz)

theorem extension_cancel_locally_extended_factor {D : Set ℂ} {b f g : ℂ → ℂ} {z : ℂ}
    (hg : AnalyticAt ℂ g z) (hg0 : g z ≠ 0)
    (hgb : ∀ᶠ w in 𝓝 z, w ∈ D → g w = b w)
    (he : HasDomainExtension D (b * f) z) : HasDomainExtension D f z := by
  obtain ⟨U, hU, hzU, F, hF, hFb⟩ := he
  obtain ⟨V, hVsub, hVopen, hzV⟩ := mem_nhds_iff.mp
    (hg.eventually_analyticAt.and ((hg.continuousAt.eventually_ne hg0).and hgb))
  refine ⟨U ∩ V, hU.inter hVopen, ⟨hzU, hzV⟩, fun w => F w / g w, ?_, ?_⟩
  · intro w hw
    exact (hF w hw.1).div (hVsub hw.2).1 (hVsub hw.2).2.1
  · intro w hw
    dsimp only
    rw [hFb ⟨hw.1.1, hw.2⟩]
    simp only [Pi.mul_apply]
    rw [← (hVsub hw.1.2).2.2 hw.2]
    exact mul_div_cancel_left₀ (f w) (hVsub hw.1.2).2.1

theorem high_regular_nonextension_mul_prefactor {lam : ℝ} (hlam : 0 < lam)
    {z : ℂ} (hz : z ∈ regularBoundaryF002 lam (omegaH lam)) {f : ℂ → ℂ}
    (hf : ¬ HasDomainExtension (omegaH lam) f z) :
    ¬ HasDomainExtension (omegaH lam) (highPrefactor lam * f) z := by
  obtain ⟨g, hg, hg0, hgb⟩ := high_regular_prefactor_nonzero_extension hlam hz
  exact fun he => hf (extension_cancel_locally_extended_factor hg hg0 hgb he)

theorem low_regular_nonextension_mul_prefactor {lam : ℝ} (hlam : 0 < lam)
    {z : ℂ} (hz : z ∈ regularBoundaryF002 lam (omegaL lam)) {f : ℂ → ℂ}
    (hf : ¬ HasDomainExtension (omegaL lam) f z) :
    ¬ HasDomainExtension (omegaL lam) (lowPrefactor lam * f) z := by
  obtain ⟨g, hg, hg0, hgb⟩ := low_regular_prefactor_nonzero_extension hlam hz
  exact fun he => hf (extension_cancel_locally_extended_factor hg hg0 hgb he)

end
end IsingBulk.AnisoF002.Physical
