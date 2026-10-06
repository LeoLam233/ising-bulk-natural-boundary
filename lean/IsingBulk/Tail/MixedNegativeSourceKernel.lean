import IsingBulk.Tail.MixedNegativeKernel
import IsingBulk.Tail.MixedPositiveKernel
import IsingBulk.Tail.MixedKernelTransport

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Jets
open scoped BigOperators

theorem mixed_actual_Y_kernel_floor {N : ℕ} (f : SelectorFunctions) {r : ℝ} (hr : 0<r)
    (τ lam : ℝ) (θ : Fin N → ℝ) {a : ℝ} (ha : 0<a)
    (hY : ‖coordinateProduct (deformedPoint f r τ lam θ)‖≤Real.exp (-a)) :
    ‖1-coordinateProduct (deformedPoint f r τ lam θ)‖⁻¹≤
      2*(phaseDenominator (Real.exp (-a)) (∑ i,θ i))⁻¹ := by
  rw [mixed_actual_Y_exp f hr τ lam θ] at hY ⊢
  have hh := allBranchExterior_exp_kernel_floor (mixedContourLogSum f r τ lam θ) ha hY
  have heq : (mixedContourLogSum f r τ lam θ).im=∑ i,θ i := by
    simp [mixedContourLogSum,logContour]
  rwa [heq] at hh

/-- The actual negative selected branch absorbs the Z pole while the
remaining Y pole is controlled by the genuine angular sum phase. -/
theorem mixed_negative_source_kernel_bound (d : LocalBranchData)
    (hcsmall : d.c₀<Real.sin d.theta/2) :
    ∃ C R e t₀ : ℝ,0<C ∧ 0<R ∧ 0<e ∧ 0<t₀ ∧
      ∀ (N : ℕ) (eps τ lam : ℝ) (f : SelectorFunctions) (θ : Fin N → ℝ) (j : Fin N),
      1≤N → 0<eps → eps<e → 0≤τ → τ<t₀ → 0≤lam → lam≤1 →
      RegularSelector f → (∀ x,f.p x≤1) → (∀ x,f.m x≤1) →
      f.p (θ j)=0 → f.m (θ j)=1 →
      θ j+d.thetaB-2*Real.pi≤0 → |θ j+d.thetaB-2*Real.pi|<R →
      let r := Real.exp (-d.c₀*eps)
      let s := radialParameter d.theta eps
      ‖mixedSourceSlope s (deformedPoint f r τ lam θ j)‖*‖mixedSimpleKernel f r τ lam s θ‖≤
        C*((phaseDenominator (Real.exp (-(d.c₀*eps))) (∑ i,θ i))⁻¹*
          (|θ j+d.thetaB-2*Real.pi|+eps)⁻¹) := by
  obtain ⟨C,R,t₀,hC,hR,ht,hNegative⟩ := mixed_actual_negative_Z_kernel d
  obtain ⟨c,e,hc,_hc1,he,_he1,hMargin⟩ := original_disk_trace_margin d.theta d.c₀
    (Real.sin_pos_of_pos_of_lt_pi d.theta_pos (by linarith [d.theta_lt,Real.pi_pos])) d.c₀_pos hcsmall
  refine ⟨2*C,R,min e R,t₀,by positivity,hR,lt_min he hR,ht,?_⟩
  intro N eps τ lam f θ j hN heps heSmall hτ hτlt hl0 hl1 hf hp1 hm1 hpj hmj hu huR
  let r := Real.exp (-d.c₀*eps)
  let s := radialParameter d.theta eps
  have hM := hMargin eps heps (heSmall.trans_le (min_le_left _ _)) s (by dsimp [s]; simp; positivity)
  have hZ := hNegative N eps τ lam f θ j (by omega) heps (heSmall.trans_le (min_le_right _ _))
    hτ hτlt hl0 hl1 hf hp1 (by simpa only [neg_mul,Real.exp_neg,inv_inv] using hM) hpj hmj hu huR
  have hY := original_current_y_product_bound hN f d.c₀_pos.le heps.le hτ hl0 θ hf.p_nonneg hm1
  have hYfloor := mixed_actual_Y_kernel_floor f (Real.exp_pos _) τ lam θ (mul_pos d.c₀_pos heps)
    (by simpa only [neg_mul] using hY)
  have hZeq : regularZProduct 0 (fun i => mixedSourcePhase s (deformedPoint f r τ lam θ i))=
      coordinateProduct (fun i => globalRoot s (deformedPoint f r τ lam θ i)) := by
    rw [mixed_actual_Z_exp]
    rfl
  dsimp only at hZ ⊢
  change ‖mixedSourceSlope s (deformedPoint f r τ lam θ j)‖/
    ‖1-regularZProduct 0 (fun i => mixedSourcePhase s (deformedPoint f r τ lam θ i))‖≤_ at hZ
  rw [hZeq] at hZ
  have hProd := mul_le_mul hZ hYfloor (inv_nonneg.mpr (norm_nonneg _))
    (div_nonneg hC.le (by positivity))
  simp only [mixedSimpleKernel,norm_mul,norm_inv] at ⊢
  calc
    _ = (‖mixedSourceSlope s (deformedPoint f r τ lam θ j)‖/
        ‖1-coordinateProduct (fun i => globalRoot s (deformedPoint f r τ lam θ i))‖)*
        ‖1-coordinateProduct (deformedPoint f r τ lam θ)‖⁻¹ := by dsimp [r,s]; rw [div_eq_mul_inv]; ring
    _ ≤ (C/(|θ j+d.thetaB-2*Real.pi|+eps))*
        (2*(phaseDenominator (Real.exp (-(d.c₀*eps))) (∑ i,θ i))⁻¹) := by simpa only [r,neg_mul] using hProd
    _ = _ := by rw [div_eq_mul_inv]; ring

end
end IsingBulk.Tail
