import IsingBulk.HT.Lie.OnsiteTransport

/-! The genuine mixed-coordinate volume has zero onsite Lie derivative.
This is proved from the actual scalar mixed derivatives and full contour,
not supplied as a transport or vanishing-divergence certificate. -/
namespace IsingBulk.HT.Lie
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Tail Set Filter
open scoped Topology BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

theorem onsiteBranchField_spatial_differentiable {N : ℕ}
    (J : Finset (Fin N)) (f : SelectorFunctions) {r : ℝ} (hr : 0<r)
    (τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m)
    (hg : ∀ i∈J,deformedPoint f r τ lam θ i-(deformedPoint f r τ lam θ i)⁻¹≠0)
    (i : Fin N) :
    DifferentiableAt ℝ (fun x => onsiteBranchField J f r τ lam s x i) θ := by
  by_cases hi : i∈J
  · simp only [onsiteBranchField,hi,ite_true,mixedSourceA]
    have hp' := hp.differentiable (by simp)
    have hm' := hm.differentiable (by simp)
    have hy : DifferentiableAt ℝ (fun x : Fin N → ℝ => deformedPoint f r τ lam x i) θ := by
      unfold deformedPoint retractionShift occupancy
      fun_prop
    have hd : DifferentiableAt ℝ (fun x : Fin N → ℝ =>
        -Complex.I*(deformedPoint f r τ lam x i-(deformedPoint f r τ lam x i)⁻¹)/2) θ := by
      simpa only [div_eq_mul_inv, Pi.sub_apply, Pi.inv_apply, Pi.mul_apply] using
        ((hy.sub (hy.inv (deformedPoint_nonzero f hr.ne' τ lam θ i))).const_mul
          (-Complex.I)).mul_const ((2:ℂ)⁻¹)
    have hden : -Complex.I*(deformedPoint f r τ lam θ i-
        (deformedPoint f r τ lam θ i)⁻¹)/2 ≠ 0 :=
      div_ne_zero (mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) (hg i hi)) (by norm_num)
    simpa only [div_eq_mul_inv, Pi.inv_apply] using
      (differentiableAt_const (1-(s^2)⁻¹)).fun_mul (hd.inv hden)
  · simp only [onsiteBranchField,hi,ite_false]
    exact differentiableAt_const _

/-- Differentiating the true identity b A = tau on its actual open domain
produces the scalar Jacobian cancellation. -/
theorem onsite_scalar_mixed_cancellation {N : ℕ}
    (J : Finset (Fin N)) (f : SelectorFunctions) {r : ℝ} (hr : 0<r)
    (τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ) (i : Fin N) (hi : i∈J)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m)
    (hpi : deriv f.p (θ i)=0) (hmi : deriv f.m (θ i)=0)
    (hW : 0<(sourceW s (deformedPoint f r τ lam θ i)).im)
    (hg : ∀ k∈J,deformedPoint f r τ lam θ k-(deformedPoint f r τ lam θ k)⁻¹≠0) :
    mixedSourceMixed s (deformedPoint f r τ lam θ i) =
      mixedSourceSpatialSlope s (deformedPoint f r τ lam θ i)*
        onsiteBranchField J f r τ lam s θ i +
      mixedSourceSlope s (deformedPoint f r τ lam θ i)*
        coordDeriv (fun x => onsiteBranchField J f r τ lam s x i) θ i := by
  have hp' := fun k => hp.differentiable (by simp) (θ k)
  have hm' := fun k => hm.differentiable (by simp) (θ k)
  have hτ := mixedSourceTau_active_coordinate f hr τ lam s θ i i hp' hm' hpi hmi hW
  have hb := mixedSourceSlope_active_coordinate f hr τ lam s θ i i hp' hm' hpi hmi hW
  have hA := (onsiteBranchField_spatial_differentiable J f hr τ lam s θ hp hm hg i).hasFDerivAt.comp_hasDerivAt_of_eq (θ i) (hasDerivAt_update θ i (θ i)) (by simp)
  have hy := mixed_deformedPoint_coordinate f hr τ lam θ i i hp' hm'
  have hcont : ContinuousAt (fun u => deformedPoint f r τ lam (Function.update θ i u) i-
      (deformedPoint f r τ lam (Function.update θ i u) i)⁻¹) (θ i) :=
    hy.continuousAt.sub (hy.continuousAt.inv₀ (by simpa using deformedPoint_nonzero f hr.ne' τ lam θ i))
  have hne : ∀ᶠ u in 𝓝 (θ i),deformedPoint f r τ lam (Function.update θ i u) i-
      (deformedPoint f r τ lam (Function.update θ i u) i)⁻¹≠0 :=
    hcont.eventually_ne (by simpa using hg i hi)
  have he : (fun u => mixedSourceSlope s (deformedPoint f r τ lam (Function.update θ i u) i)*
      onsiteBranchField J f r τ lam s (Function.update θ i u) i) =ᶠ[𝓝 (θ i)]
      (fun u => mixedSourceTau s (deformedPoint f r τ lam (Function.update θ i u) i)) := by
    filter_upwards [hne] with u hu
    simpa only [onsiteBranchField,hi,ite_true] using mixedSourceSlope_mul_A (s := s) hu
  have heq := he.deriv_eq
  have hprod := hb.fun_mul hA
  simp only [Function.comp_def] at hprod
  rw [hprod.deriv,hτ.deriv] at heq
  simp only [ite_true,Function.update_eq_self] at heq
  rw [show coordDeriv (fun x => onsiteBranchField J f r τ lam s x i) θ i =
    fderiv ℝ (fun x => onsiteBranchField J f r τ lam s x i) θ (Pi.single i 1) from
      coordDeriv_eq_fderiv _ θ (onsiteBranchField_spatial_differentiable J f hr τ lam s θ hp hm hg i) i]
  exact heq.symm

/-- Exact cancellation before integration, for every particle number. -/
theorem onsite_volume_coordinate_lie_zero {N : ℕ}
    (J : Finset (Fin N)) (f : SelectorFunctions) {r : ℝ} (hr : 0<r)
    (τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ) (hs : s≠0)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m)
    (hplateau : ∀ i∈J,deriv f.p (θ i)=0 ∧ deriv f.m (θ i)=0)
    (hW : ∀ i∈J,0<(sourceW s (deformedPoint f r τ lam θ i)).im)
    (hg : ∀ i∈J,deformedPoint f r τ lam θ i-(deformedPoint f r τ lam θ i)⁻¹≠0) :
    mixedCoordinateLie (onsiteBranchField J f r τ lam)
      (mixedHybridVolume J f r τ lam) s θ=0 := by
  have he (i : Fin N) :
      coordDeriv (fun x => onsiteBranchField J f r τ lam s x i*
        mixedHybridVolume J f r τ lam s x) θ i =
      if i∈J then (∏ k∈J.erase i,mixedSourceSlope s (deformedPoint f r τ lam θ k))*
        mixedSourceMixed s (deformedPoint f r τ lam θ i) else 0 := by
    by_cases hi : i∈J
    · have hA := (onsiteBranchField_spatial_differentiable J f hr τ lam s θ hp hm hg i).hasFDerivAt.comp_hasDerivAt_of_eq (θ i) (hasDerivAt_update θ i (θ i)) (by simp)
      have hE := mixedHybridVolume_active_coordinate J f hr τ lam s θ i
        (fun k => hp.differentiable (by simp) _) (fun k => hm.differentiable (by simp) _)
        (hplateau i hi).1 (hplateau i hi).2 hW
      have hc := onsite_scalar_mixed_cancellation J f hr τ lam s θ i hi hp hm
        (hplateau i hi).1 (hplateau i hi).2 (hW i hi) hg
      have hv : mixedHybridVolume J f r τ lam s θ=
          (∏ k∈J.erase i,mixedSourceSlope s (deformedPoint f r τ lam θ k))*
            mixedSourceSlope s (deformedPoint f r τ lam θ i) :=
        (Finset.prod_erase_mul _ _ hi).symm
      unfold coordDeriv
      have hprod := hA.fun_mul hE
      simp only [Function.comp_def] at hprod
      rw [hprod.deriv]
      simp only [hi,ite_true,Function.update_eq_self]
      rw [hc,hv,coordDeriv_eq_fderiv _ θ
        (onsiteBranchField_spatial_differentiable J f hr τ lam s θ hp hm hg i) i]
      ring
    · simp [onsiteBranchField,hi,coordDeriv]
  unfold mixedCoordinateLie
  rw [(mixedHybridVolume_parameter J f r τ lam s θ hs hW).deriv]
  simp_rw [he]
  simp

end
end IsingBulk.HT.Lie
