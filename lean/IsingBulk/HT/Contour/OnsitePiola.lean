import IsingBulk.HT.Contour.OnsiteDensity
import IsingBulk.HT.Contour.SignedPiola

/-! Actual onsite Cartan/Piola transport, from its physical analytic density. -/
namespace IsingBulk.HT.Contour
noncomputable section
open IsingBulk.First IsingBulk.Tail
open scoped BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false

theorem onsitePulledDensity_eq_log {N : ℕ} (f : SelectorFunctions)
    {r : ℝ} (hr : 0 < r) (τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ) :
    onsitePulledDensity f r τ lam s θ =
      onsiteLogDensity N s (logContour f r τ lam θ)*(angularJacobian f τ lam θ).det := by
  unfold onsitePulledDensity onsiteLogDensity
  rw [show deformedPoint f r τ lam θ = (fun i => Complex.exp (logContour f r τ lam θ i)) from
    funext (deformedPoint_exp_log f hr τ lam θ)]
  ring

 theorem onsiteLogDensity_differentiableAt (N : ℕ) (_hN : 0 < N) (s : ℂ) (ℓ : Fin N → ℂ)
    (hW : ∀ i, 0 < (sourceW s (Complex.exp (ℓ i))).im) :
    DifferentiableAt ℂ (onsiteLogDensity N s) ℓ := by
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
  have ddensity : DifferentiableAt ℂ (fun x => onsiteCanceledDensity (z x) (y x)) ℓ :=
    (((dZ.mul dY).inv (mul_ne_zero hZ0 hY0)).mul dpair).mul dres
  exact ((dY.const_mul ((N.factorial:ℂ)⁻¹*(2*(Real.pi:ℂ)*Complex.I)^(-(N:ℤ)))).mul ddensity)

 theorem onsiteLogDensity_on_source_differentiable {N : ℕ} (hN : 0 < N)
    (f : SelectorFunctions) {r τ lam : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hτ : 0 ≤ τ) (hlam : 0 ≤ lam) (s : ℂ)
    (hmargin : r⁻¹-r < (sourceS s).im)
    (hp : ∀ x, 0 ≤ f.p x) (hm0 : ∀ x, 0 ≤ f.m x) (_hm1 : ∀ x, f.m x ≤ 1)
    (hps : ∀ x, Real.sin x ≤ 0 → f.p x=0)
    (hms : ∀ x, 0 ≤ Real.sin x → f.m x=0) (θ : Fin N → ℝ) :
    DifferentiableAt ℂ (onsiteLogDensity N s) (logContour f r τ lam θ) := by
  apply onsiteLogDensity_differentiableAt N hN s
  · intro i
    rw [← deformedPoint_exp_log f hr]
    exact (sourceW_upper_of_margin hr hr1 hmargin (deformedPoint_zero_norm f hr.le τ θ i)).trans_le
      (deformed_sourceW_im_ge hN f hr hτ hlam θ s hp hm0 hps hms i)


 theorem onsite_source_pointwise_conservation {N : ℕ} (hN : 0 < N)
    (f : SelectorFunctions) {r τ lam : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hτ : 0 ≤ τ) (hlam : 0 ≤ lam) (s : ℂ)
    (hmargin : r⁻¹-r < (sourceS s).im)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m)
    (hp0 : ∀ x, 0 ≤ f.p x) (hm0 : ∀ x, 0 ≤ f.m x) (hm1 : ∀ x, f.m x ≤ 1)
    (hps : ∀ x, Real.sin x ≤ 0 → f.p x=0)
    (hms : ∀ x, 0 ≤ Real.sin x → f.m x=0) (θ : Fin N → ℝ) :
    deriv (fun u => onsitePulledDensity f r τ u s θ) lam =
      ∑ i, deriv (fun u => onsiteHomotopyFlux f r τ lam s (Function.update θ i u) i) (θ i) := by
  have hF := onsiteLogDensity_on_source_differentiable hN f hr hr1 hτ hlam s hmargin hp0 hm0 hm1 hps hms θ
  rw [logContour_eq_affine] at hF
  have hc := smooth_affine_homotopy_conservation (fun _ => (Real.log r:ℂ))
    (complexShift f τ) (complexShift_contDiff f τ hp hm) (onsiteLogDensity N s) lam θ hF
  simp_rw [← logContour_eq_affine f r τ] at hc
  simp_rw [← angularJacobian_eq_affine f r τ _ hp hm] at hc
  simp_rw [onsitePulledDensity_eq_log f hr]
  exact hc

 theorem onsiteHomotopyFlux_named {N : ℕ} (f : SelectorFunctions) {r : ℝ} (hr : 0 < r)
    (τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ) (q : Fin N)
    (hp : f.p (θ q)=1) (hp' : deriv f.p (θ q)=0)
    (hm : f.m (θ q)=0) (hm' : deriv f.m (θ q)=0) :
    onsiteHomotopyFlux f r τ lam s θ q = 2*Complex.I*(τ:ℂ)*onsitePulledDensity f r τ lam s θ := by
  rw [onsitePulledDensity_eq_log f hr]
  unfold onsiteHomotopyFlux angularJacobian complexShift shiftMap
  rw [retraction_named_minor lam τ _ _ _ _ q hp hp' hm hm']
  ring

end
end IsingBulk.HT.Contour
