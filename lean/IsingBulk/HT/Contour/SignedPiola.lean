import IsingBulk.HT.Contour.SignedKernel

/-! Literal signed log-contour transport on the actual legal source sheet.
The sign changes only the global product gaps. The entire density and the
replacement-minor flux are transported before any homotopy split. -/
namespace IsingBulk.HT.Contour
noncomputable section
open IsingBulk.First IsingBulk.Tail
open scoped BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false

def signedLogDensity (σ : ℂ) (N : ℕ) (s : ℂ) (ℓ : Fin N → ℂ) : ℂ :=
  (N.factorial:ℂ)⁻¹*(2*(Real.pi:ℂ)*Complex.I)^(-(N:ℤ))*
    (∏ i, Complex.exp (ℓ i))*
    signedCanceledDensity σ (fun i => globalRoot s (Complex.exp (ℓ i)))
      (fun i => Complex.exp (ℓ i))

def signedPulledDensity {N : ℕ} (σ : ℂ) (f : SelectorFunctions) (r τ lam : ℝ)
    (s : ℂ) (θ : Fin N → ℝ) : ℂ :=
  (N.factorial:ℂ)⁻¹*(2*(Real.pi:ℂ)*Complex.I)^(-(N:ℤ))*
    (angularJacobian f τ lam θ).det*(∏ i, deformedPoint f r τ lam θ i)*
    signedCanceledDensity σ (fun i => globalRoot s (deformedPoint f r τ lam θ i))
      (deformedPoint f r τ lam θ)

def signedHomotopyFlux {N : ℕ} (σ : ℂ) (f : SelectorFunctions) (r τ lam : ℝ)
    (s : ℂ) (θ : Fin N → ℝ) (q : Fin N) : ℂ :=
  signedLogDensity σ N s (logContour f r τ lam θ)*
    ((angularJacobian f τ lam θ).updateCol q (complexShift f τ θ)).det

@[simp] theorem signedPulledDensity_one {N : ℕ} (f : SelectorFunctions) (r τ lam : ℝ)
    (s : ℂ) (θ : Fin N → ℝ) : signedPulledDensity 1 f r τ lam s θ =
      pulledDensity f r τ lam s θ := by
  simp only [signedPulledDensity,signedCanceledDensity_one,pulledDensity]

theorem signedPulledDensity_eq_log {N : ℕ} (σ : ℂ) (f : SelectorFunctions)
    {r : ℝ} (hr : 0 < r) (τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ) :
    signedPulledDensity σ f r τ lam s θ =
      signedLogDensity σ N s (logContour f r τ lam θ)*(angularJacobian f τ lam θ).det := by
  unfold signedPulledDensity signedLogDensity
  rw [show deformedPoint f r τ lam θ = (fun i => Complex.exp (logContour f r τ lam θ i)) from
    funext (deformedPoint_exp_log f hr τ lam θ)]
  ring

 theorem signedLogDensity_differentiableAt (σ : ℂ) (hσ : ‖σ‖ = 1) (N : ℕ) (hN : 0 < N) (s : ℂ) (ℓ : Fin N → ℂ)
    (hW : ∀ i, 0 < (sourceW s (Complex.exp (ℓ i))).im)
    (hY : 1-σ*coordinateProduct (fun i => Complex.exp (ℓ i)) ≠ 0) :
    DifferentiableAt ℂ (signedLogDensity σ N s) ℓ := by
  let y : (Fin N → ℂ) → Fin N → ℂ := fun x i => Complex.exp (x i)
  let z : (Fin N → ℂ) → Fin N → ℂ := fun x i => globalRoot s (y x i)
  have hy0 : ∀ i, y ℓ i ≠ 0 := fun i => Complex.exp_ne_zero _
  have hz0 : ∀ i, z ℓ i ≠ 0 := fun i => globalRoot_nonzero s _
  have hzn : ∀ i, ‖z ℓ i‖ < 1 := fun i => interiorRoot_norm_lt_one (hW i)
  have dy : ∀ i, DifferentiableAt ℂ (fun x => y x i) ℓ := by
    intro i
    exact Complex.differentiableAt_exp.comp ℓ (differentiableAt_apply i ℓ)
  have dz : ∀ i, DifferentiableAt ℂ (fun x => z x i) ℓ := by
    intro i
    have hzi := globalRoot_y_differentiableAt (hy0 i) (hW i)
    have hc := hzi.comp ℓ (dy i)
    exact hc
  have dY : DifferentiableAt ℂ (fun x => coordinateProduct (y x)) ℓ :=
    differentiableAt_finite_product Finset.univ (fun i x => y x i) ℓ (fun i _ => dy i)
  have dZ : DifferentiableAt ℂ (fun x => coordinateProduct (z x)) ℓ :=
    differentiableAt_finite_product Finset.univ (fun i x => z x i) ℓ (fun i _ => dz i)
  have hY0 : coordinateProduct (y ℓ) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hy0 i)
  have hZ0 : coordinateProduct (z ℓ) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hz0 i)
  have hZ1 := signed_product_gap_ne_zero hN σ hσ _ hzn
  have dpair : DifferentiableAt ℂ (fun x => canceledPairProduct (z x) (y x)) ℓ := by
    unfold canceledPairProduct
    apply differentiableAt_finite_product
    intro i _
    apply differentiableAt_finite_product
    intro j _
    exact differentiableAt_quotient (((((dy i).sub (dy j)).pow 2).neg.mul (dz i)).mul (dz j))
      (((dy i).mul (dy j)).mul (((differentiableAt_const (1:ℂ)).sub ((dz i).mul (dz j))).pow 2))
      (mul_ne_zero (mul_ne_zero (hy0 i) (hy0 j))
        (pow_ne_zero 2 (one_sub_mul_ne_zero_of_norm_lt_one (hzn i) (hzn j))))
  have dres : DifferentiableAt ℂ (fun x => ∏ i, residueFactor (z x i)) ℓ := by
    apply differentiableAt_finite_product
    intro i _
    exact differentiableAt_quotient ((differentiableAt_const (2:ℂ)).mul ((dz i).pow 2))
      ((differentiableAt_const (1:ℂ)).sub ((dz i).pow 2))
      (by simpa [pow_two] using one_sub_mul_ne_zero_of_norm_lt_one (hzn i) (hzn i))
  have ddensity : DifferentiableAt ℂ (fun x => signedCanceledDensity σ (z x) (y x)) ℓ :=
    (((differentiableAt_quotient ((dZ.inv hZ0).add (dY.inv hY0))
      (((differentiableAt_const (1:ℂ)).sub (dZ.const_mul σ)).mul ((differentiableAt_const (1:ℂ)).sub (dY.const_mul σ)))
      (mul_ne_zero hZ1 hY)).mul dpair).mul dres)
  exact ((dY.const_mul ((N.factorial:ℂ)⁻¹*(2*(Real.pi:ℂ)*Complex.I)^(-(N:ℤ)))).mul ddensity)

 theorem signedLogDensity_on_source_differentiable (σ : ℂ) (hσ : ‖σ‖ = 1) {N : ℕ} (hN : 0 < N)
    (f : SelectorFunctions) {r τ lam : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hτ : 0 ≤ τ) (hlam : 0 ≤ lam) (s : ℂ)
    (hmargin : r⁻¹-r < (sourceS s).im)
    (hp : ∀ x, 0 ≤ f.p x) (hm0 : ∀ x, 0 ≤ f.m x) (hm1 : ∀ x, f.m x ≤ 1)
    (hps : ∀ x, Real.sin x ≤ 0 → f.p x=0)
    (hms : ∀ x, 0 ≤ Real.sin x → f.m x=0) (θ : Fin N → ℝ) :
    DifferentiableAt ℂ (signedLogDensity σ N s) (logContour f r τ lam θ) := by
  apply signedLogDensity_differentiableAt σ hσ N hN s
  · intro i
    rw [← deformedPoint_exp_log f hr]
    exact (sourceW_upper_of_margin hr hr1 hmargin (deformedPoint_zero_norm f hr.le τ θ i)).trans_le
      (deformed_sourceW_im_ge hN f hr hτ hlam θ s hp hm0 hps hms i)
  · have hY := signed_gap_ne_zero σ _ hσ
      (homotopy_y_product_lt_one hN f hr hr1 hτ hlam θ hp hm1)
    rwa [show deformedPoint f r τ lam θ = (fun i => Complex.exp (logContour f r τ lam θ i)) from
      funext (deformedPoint_exp_log f hr τ lam θ)] at hY

 theorem signed_source_pointwise_conservation (σ : ℂ) (hσ : ‖σ‖ = 1) {N : ℕ} (hN : 0 < N)
    (f : SelectorFunctions) {r τ lam : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hτ : 0 ≤ τ) (hlam : 0 ≤ lam) (s : ℂ)
    (hmargin : r⁻¹-r < (sourceS s).im)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m)
    (hp0 : ∀ x, 0 ≤ f.p x) (hm0 : ∀ x, 0 ≤ f.m x) (hm1 : ∀ x, f.m x ≤ 1)
    (hps : ∀ x, Real.sin x ≤ 0 → f.p x=0)
    (hms : ∀ x, 0 ≤ Real.sin x → f.m x=0) (θ : Fin N → ℝ) :
    deriv (fun u => signedPulledDensity σ f r τ u s θ) lam =
      ∑ i, deriv (fun u => signedHomotopyFlux σ f r τ lam s (Function.update θ i u) i) (θ i) := by
  have hF := signedLogDensity_on_source_differentiable σ hσ hN f hr hr1 hτ hlam s hmargin hp0 hm0 hm1 hps hms θ
  rw [logContour_eq_affine] at hF
  have hc := smooth_affine_homotopy_conservation (fun _ => (Real.log r:ℂ))
    (complexShift f τ) (complexShift_contDiff f τ hp hm) (signedLogDensity σ N s) lam θ hF
  simp_rw [← logContour_eq_affine f r τ] at hc
  simp_rw [← angularJacobian_eq_affine f r τ _ hp hm] at hc
  simp_rw [signedPulledDensity_eq_log σ f hr]
  exact hc

 theorem signedHomotopyFlux_named {N : ℕ} (σ : ℂ) (f : SelectorFunctions) {r : ℝ} (hr : 0 < r)
    (τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ) (q : Fin N)
    (hp : f.p (θ q)=1) (hp' : deriv f.p (θ q)=0)
    (hm : f.m (θ q)=0) (hm' : deriv f.m (θ q)=0) :
    signedHomotopyFlux σ f r τ lam s θ q = 2*Complex.I*(τ:ℂ)*signedPulledDensity σ f r τ lam s θ := by
  rw [signedPulledDensity_eq_log σ f hr]
  unfold signedHomotopyFlux angularJacobian complexShift shiftMap
  rw [retraction_named_minor lam τ _ _ _ _ q hp hp' hm hm']
  ring

end
end IsingBulk.HT.Contour
