import IsingBulk.Tail.CompactRegularDensity
import IsingBulk.HT.Contour.SignedPiola

/-! The signed compact source has exactly the established regular numerator.
Only the frozen simple product kernel changes. Collision zeros and the full
coupled Jacobian are reused without division by a complete pair. -/
namespace IsingBulk.HT.Tail
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.Lie IsingBulk.HT.Contour Set
open scoped Topology ContDiff BigOperators
set_option backward.isDefEq.respectTransparency false

def signedMixedSimpleKernel {N : ℕ} (σ : ℂ) (f : SelectorFunctions) (r τ lam : ℝ)
    (s : ℂ) (θ : Fin N → ℝ) : ℂ :=
  (1-σ*coordinateProduct (fun i => globalRoot s (deformedPoint f r τ lam θ i)))⁻¹*
    (1-σ*coordinateProduct (deformedPoint f r τ lam θ))⁻¹

theorem signed_compactSource_kernel_smooth (σ : ℂ) (hσ : ‖σ‖ = 1) {N : ℕ} (hN : 0 < N)
    (f : SelectorFunctions) (hf : RegularSelector f) {r τ lam : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ) (hlam : 0 ≤ lam) :
    ParameterSmoothOn (compactSourceDomain N r) (signedMixedSimpleKernel σ f r τ lam) := by
  let Ω := compactSourceDomain N r
  have hZ := (ParameterSmoothOn.const Ω σ).mul (compactSource_Z_smooth hN f hf hr hr1 hτ hlam)
  have hY := (ParameterSmoothOn.const Ω σ).mul (compactSource_Y_smooth (N := N) f hf r τ lam)
  exact (((ParameterSmoothOn.const Ω 1).sub hZ).inv (fun p hp =>
    signed_product_gap_ne_zero hN σ hσ _ (fun i => interiorRoot_norm_lt_one
      (deformed_sourceW_upper_on_damping hN f hf hr hr1 hτ hlam hp.1 p.2 i)))).mul
    (((ParameterSmoothOn.const Ω 1).sub hY).inv (fun p _ =>
      signed_gap_ne_zero σ _ hσ
        (homotopy_y_product_lt_one hN f hr hr1 hτ hlam p.2 hf.p_nonneg hf.m_le_one)))

theorem signed_compact_pulledDensity_factorization {N : ℕ} (σ : ℂ) (f : SelectorFunctions)
    (r τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ) :
    signedPulledDensity σ f r τ lam s θ=
      signedMixedSimpleKernel σ f r τ lam s θ*compactRegularDensity f r τ lam s θ := by
  unfold signedPulledDensity signedCanceledDensity signedGlobalFactor
    signedMixedSimpleKernel compactRegularDensity mixedDensityNormalization
  simp only [Finset.prod_mul_distrib,div_eq_mul_inv,mul_inv_rev]
  ring

theorem signed_compactSource_density_smooth (σ : ℂ) (hσ : ‖σ‖ = 1) {N : ℕ} (hN : 0 < N)
    (f : SelectorFunctions) (hf : RegularSelector f) {r τ lam : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ) (hlam : 0 ≤ lam) :
    ParameterSmoothOn (compactSourceDomain N r) (signedPulledDensity σ f r τ lam) := by
  apply ((signed_compactSource_kernel_smooth σ hσ hN f hf hr hr1 hτ hlam).mul
    (compactRegularDensity_smooth hN f hf hr hr1 hτ hlam)).congr (compactSourceDomain_isOpen N r)
  intro p _
  exact signed_compact_pulledDensity_factorization σ f r τ lam p.1 p.2

end
end IsingBulk.HT.Tail
