import IsingBulk.AnisoF002.C03.PhysicalNegativeDomain

/-!
# Negative physical odd germs transfer to the original HT function

This is the physical transfer interface for the remaining full-series
Taylor noncancellation theorem.  Every spectral chart, physical-domain
membership and coefficient normalization is constructed.  The theorem
does not claim the still separate noncancellation argument.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open Set Filter IsingBulk.Anisotropic IsingBulk.Anisotropic.FormFactors
  IsingBulk.AnisoF002.Geometry IsingBulk.AnisoF002.NegativeHT
open scoped Topology BigOperators

theorem no_extension_of_negative_inward_correspondence
    {D : Set ℂ} {F Z H : ℂ → ℂ} {z σ : ℂ}
    (hD : IsOpen D) (hZ : AnalyticAt ℂ Z 0) (hZ0 : Z 0 = z) (hσ : σ ≠ 0)
    (hside : ∀ᶠ eps : ℝ in 𝓝[>] (0 : ℝ), Z (-(eps : ℂ)) ∈ D)
    (hcor : ∀ᶠ eps : ℝ in 𝓝[>] (0 : ℝ),
      (fun u => F (Z u)) =ᶠ[𝓝 (-(eps : ℂ))] fun u => σ * H u)
    (hno : ¬ ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧
      ∀ᶠ eps : ℝ in 𝓝[>] (0 : ℝ), H =ᶠ[𝓝 (-(eps : ℂ))] g) :
    ¬ HasDomainExtension D F z := by
  rintro ⟨U, hU, hzU, g, hg, heq⟩
  apply hno
  refine ⟨fun u => σ⁻¹ * g (Z u), analyticAt_const.mul ((hg z hzU).comp_of_eq hZ hZ0), ?_⟩
  have hp : Tendsto (fun eps : ℝ => -(eps : ℂ)) (𝓝 (0 : ℝ)) (𝓝 (0 : ℂ)) := by
    convert (show ContinuousAt (fun eps : ℝ => -(eps : ℂ)) 0 by fun_prop).tendsto using 1
    simp
  have hmem : ∀ᶠ y in 𝓝 (Z 0), y ∈ U := by
    rw [hZ0]
    exact hU.mem_nhds hzU
  have hZU : ∀ᶠ u in 𝓝 (0 : ℂ), Z u ∈ U := hZ.continuousAt.eventually hmem
  have hnear := hp.eventually (hZU.and hZ.eventually_analyticAt)
  filter_upwards [hside, hcor, hnear.filter_mono nhdsWithin_le_nhds] with eps heD hc he
  have hUD := he.2.continuousAt.eventually ((hU.inter hD).mem_nhds ⟨he.1, heD⟩)
  filter_upwards [hUD, hc] with u hu huc
  apply mul_left_cancel₀ hσ
  calc
    σ * H u = F (Z u) := huc.symm
    _ = g (Z u) := (heq hu).symm
    _ = σ * (σ⁻¹ * g (Z u)) := by rw [← mul_assoc, mul_inv_cancel₀ hσ, one_mul]

theorem exists_negative_original_high_transport {lam φ : ℝ} {z : ℂ}
    (hlam : 0 < lam) (hz : z ∈ regularBoundaryF002 lam (omegaH lam))
    (hφ : 0 < φ) (hπ : φ < Real.pi)
    (hinc : spectralA lam z = spectralS z * (Real.cos φ : ℂ) + spectralT lam z * (-1))
    (hdet : spectralDetF002 lam z < 0) :
    ∃ B : ℂ → ℂ, AnalyticAt ℂ B 0 ∧ B 0 = spectralT lam z / spectralS z ∧
      (B 0).im < 0 ∧
      ∀ b : ℂ → ℂ, AnalyticAt ℂ b 0 → (∀ t, b t ^ 2 = B t) →
        (¬ ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧
          ∀ᶠ eps : ℝ in 𝓝[>] (0 : ℝ), negativePhysicalOddSum b B φ =ᶠ[𝓝 (-(eps : ℂ))] g) →
        ¬ HasDomainExtension (omegaH lam) (highNormalizedBulk lam) z := by
  obtain ⟨Z, B, hZa, hZ0, hBa, hB0, hBi, _, hside, hcor⟩ :=
    exists_negative_original_odd_chart hlam hz hφ hπ hinc hdet
  refine ⟨B, hBa, hB0, hBi, ?_⟩
  intro b hba hbsq hno
  have hBn : B 0 ≠ 0 := Complex.slitPlane_ne_zero (Or.inr hBi.ne)
  have hσsq := physical_root_branch_sign_sq hBn (hbsq 0)
  have hσ : Complex.sqrt (B 0) / b 0 ≠ 0 := by
    intro he
    simp only [he, zero_pow two_ne_zero, zero_ne_one] at hσsq
  apply original_high_nonextension_of_canonical hlam hz hdet.ne
  exact no_extension_of_negative_inward_correspondence (isOpen_omegaHF002 hlam)
    hZa hZ0 hσ hside (hcor b hba hbsq) hno

end
end IsingBulk.AnisoF002.RegularTail.C03
