import IsingBulk.HT22.Geometry.SignedExtremeFiber
import IsingBulk.Preferred22.JacobianContinuity

namespace IsingBulk.HT22.Geometry
noncomputable section
open scoped BigOperators Topology ContDiff
open Set MeasureTheory IsingBulk.Preferred22

def signedJacobianResolvent {N : ℕ} (η : ℝ) (d : PreferredBranchData)
    (B : PreferredCoareaBump d) (ε τ : ℝ) (θ : Fin N → ℝ) : ℝ :=
  (∏ i, ‖actualBumpSlopeVector d B ε τ θ i+1‖)/‖1-signedActualZ η d B ε τ θ‖

theorem signedActualZ_equiv {N : ℕ} (η : ℝ) (d : PreferredBranchData)
    (B : PreferredCoareaBump d) (ε τ : ℝ) (θ : Fin N → ℝ) (e : Equiv.Perm (Fin N)) :
    signedActualZ η d B ε τ (θ ∘ e)=signedActualZ η d B ε τ θ := by
  simp only [signedActualZ,preferredActualZ_equiv]

theorem signedJacobianResolvent_equiv {N : ℕ} (η : ℝ) (d : PreferredBranchData)
    (B : PreferredCoareaBump d) (ε τ : ℝ) (θ : Fin N → ℝ) (e : Equiv.Perm (Fin N)) :
    signedJacobianResolvent η d B ε τ (θ ∘ e)=signedJacobianResolvent η d B ε τ θ := by
  unfold signedJacobianResolvent
  rw [signedActualZ_equiv]
  simp only [actualBumpSlopeVector_equiv]
  rw [Equiv.prod_comp e (fun i : Fin N => ‖actualBumpSlopeVector d B ε τ θ i+1‖)]

theorem signed_actual_denominator_ne_zero {N : ℕ} (η : ℝ) (hN : 0<N)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {ε τ : ℝ}
    (hε : 0<ε) (hτ : 0≤τ) (θ : Fin N → ℝ) : ‖1-signedActualZ η d B ε τ θ‖≠0 := by
  apply norm_ne_zero_iff.mpr
  rw [signedActualZ_eq_exp η d B hε hτ]
  apply preferred_phase_denominator_ne_zero
  let i : Fin N := ⟨0,hN⟩
  have hs : 0<Real.sin d.alpha := Real.sin_pos_of_pos_of_lt_pi d.alpha_pos
    (by linarith [d.alpha_lt,Real.pi_pos])
  have hW := (mul_pos hε hs).trans_le (preferredActualW_im_lower d B hε.le hτ θ i)
  have hneg := (IsingBulk.Branch.lowerArccos_sheet_of_upper hW).2.2.2
  have hsum := preferred_single_phase_attenuation_le_total d B hε hτ θ i
  change (preferredAngularPhase d ε (deformedAngles τ B.p B.m θ i)).im<0 at hneg
  simp only [Complex.add_im,Complex.ofReal_im,add_zero]
  linarith

theorem signedJacobianResolvent_continuous {N : ℕ} (η : ℝ) (hN : 0<N)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {ε τ : ℝ}
    (hε : 0<ε) (hτ : 0≤τ) :
    Continuous (fun θ : Fin N → ℝ => signedJacobianResolvent η d B ε τ θ) := by
  have hf (v : Fin N) : Continuous (fun θ : Fin N → ℝ => ‖actualBumpSlopeVector d B ε τ θ v+1‖) :=
    ((preferred_source_slope_continuous hN d B hε hτ v).add continuous_const).norm
  have hz : Continuous (fun θ : Fin N → ℝ => signedActualZ η d B ε τ θ) :=
    continuous_const.mul (preferred_actual_product_continuous d B hε hτ)
  unfold signedJacobianResolvent
  exact (continuous_finsetProd _ (fun v _ => hf v)).div ((continuous_const.sub hz).norm)
    (signed_actual_denominator_ne_zero η hN d B hε hτ)

/-- Reuse of the exactly identical non-extreme one-body numerator estimate.
Its unsigned nonzero denominator is canceled algebraically before restoring
the actual signed denominator; no signed bound is inferred from an unsigned
resolvent inequality. -/
theorem signed_geometric_fiber_jacobian_bound (d : PreferredBranchData) (B : PreferredCoareaBump d) :
    ∃ A ε₀ τ₀ δ₀ : ℝ, 0<A ∧ 0<ε₀ ∧ 0<τ₀ ∧ 0<δ₀ ∧ δ₀<B.delta ∧
      ∀ η : ℝ, ∀ n : ℕ, ∀ ε τ c r δB : ℝ, 0<ε → ε<ε₀ → 0≤τ → τ<τ₀ →
      δB≤δ₀ → ∀ z : Fin n → ℝ, ∀ m : ℝ,
      m∈extremeShellFiber (c-∑ i,z i) r (-d.b-δB) B.delta z →
      signedJacobianResolvent η d B ε τ (preferredFiberConfiguration c z m) ≤
        A^n*(∏ i,preferredOneBodyMajorant ε (z i+d.b))*
          (preferredExtremePair d B ε τ (preferredFiberConfiguration c z m) 0 (Fin.last (n+1))/
            ‖1-signedActualZ η d B ε τ (preferredFiberConfiguration c z m)‖) := by
  obtain ⟨A,e,t,δ,hA,he,ht,hδ,hδB,hbound⟩ := preferred_geometric_fiber_jacobian_bound d B
  refine ⟨A,e,t,δ,hA,he,ht,hδ,hδB,?_⟩
  intro η n ε τ c r δB hε hεr hτ hτr hδ z m hm
  let θ := preferredFiberConfiguration c z m
  have hh := hbound n ε τ c r δB hε hεr hτ hτr hδ z m hm
  have hden : 0<‖1-preferredActualZ d B ε τ θ‖ := lt_of_le_of_ne (norm_nonneg _)
    (Ne.symm (preferred_actual_denominator_ne_zero (by omega : 0<n+2) d B hε hτ θ))
  have hraw : (∏ i,‖actualBumpSlopeVector d B ε τ θ i+1‖) ≤
      A^n*(∏ i,preferredOneBodyMajorant ε (z i+d.b))*preferredExtremePair d B ε τ θ 0 (Fin.last (n+1)) := by
    apply (div_le_div_iff_of_pos_right hden).mp
    simpa only [preferredJacobianResolvent,mul_div_assoc,θ] using hh
  unfold signedJacobianResolvent
  simpa only [mul_div_assoc,θ] using div_le_div_of_nonneg_right hraw
    (norm_nonneg (1-signedActualZ η d B ε τ θ))

end
end IsingBulk.HT22.Geometry
