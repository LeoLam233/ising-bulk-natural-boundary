import IsingBulk.Tail.SelectorSmoothPiola
import IsingBulk.Tail.SelectorDifferential
import IsingBulk.Tail.SelectorRegularity
import IsingBulk.Tail.SelectorCurrentMinor

/-! Actual source log-contour attachment to the proven pointwise Piola
identity. The real occupancy functions remain real and fixed in s. -/
namespace IsingBulk.Tail
noncomputable section
open scoped BigOperators ContDiff
open IsingBulk.First
set_option backward.isDefEq.respectTransparency false

 def complexShift {N : ℕ} (f : SelectorFunctions) (τ : ℝ) (θ : Fin N → ℝ) : Fin N → ℂ :=
  fun i => (shiftMap f τ θ i:ℂ)

 theorem complexShift_contDiff {N : ℕ} (f : SelectorFunctions) (τ : ℝ)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m) :
    ContDiff ℝ 2 (complexShift (N := N) f τ) := by
  apply contDiff_pi.mpr
  intro i
  exact Complex.ofRealCLM.contDiff.comp
    (((contDiff_apply ℝ ℝ i).comp (shiftMap_contDiff f τ hp hm)).of_le (by simp))

 theorem logContour_eq_affine {N : ℕ} (f : SelectorFunctions) (r τ lam : ℝ)
    (θ : Fin N → ℝ) :
    logContour f r τ lam θ = affineLogMap (fun _ => (Real.log r:ℂ)) (complexShift f τ) lam θ := by
  funext i
  simp only [logContour,affineLogMap,complexShift,Complex.ofReal_mul]

 theorem angularJacobian_eq_affine {N : ℕ} (f : SelectorFunctions) (r τ lam : ℝ)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m) (θ : Fin N → ℝ) :
    angularJacobian f τ lam θ = affineShiftJacobian (complexShift f τ) lam θ := by
  ext k i
  have hs := logContour_coordinate_deriv f r τ lam θ i k
    (fun j => hp.differentiable (by simp) (θ j)) (fun j => hm.differentiable (by simp) (θ j))
  simp_rw [logContour_eq_affine] at hs
  have hg := hasDerivAt_pi.mp (affineLogMap_coordinate (fun _ => (Real.log r:ℂ))
    (complexShift f τ) (complexShift_contDiff f τ hp hm) lam θ i) k
  exact hs.unique hg

 def logDensity (N : ℕ) (s : ℂ) (ℓ : Fin N → ℂ) : ℂ :=
  (N.factorial:ℂ)⁻¹*(2*(Real.pi:ℂ)*Complex.I)^(-(N:ℤ))*
    (∏ i, Complex.exp (ℓ i))*
    canceledReducedDensity (fun i => globalRoot s (Complex.exp (ℓ i))) (fun i => Complex.exp (ℓ i))

 theorem deformedPoint_exp_log {N : ℕ} (f : SelectorFunctions) {r : ℝ} (hr : 0 < r)
    (τ lam : ℝ) (θ : Fin N → ℝ) (i : Fin N) :
    deformedPoint f r τ lam θ i = Complex.exp (logContour f r τ lam θ i) := by
  rw [deformedPoint_polar f hr]
  congr 1
  simp only [logContour,shiftMap,Complex.ofReal_add,Complex.ofReal_mul]
  ring

 theorem pulledDensity_eq_log {N : ℕ} (f : SelectorFunctions) {r : ℝ} (hr : 0 < r)
    (τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ) :
    pulledDensity f r τ lam s θ =
      logDensity N s (logContour f r τ lam θ)*(angularJacobian f τ lam θ).det := by
  unfold pulledDensity logDensity
  rw [show deformedPoint f r τ lam θ = (fun i => Complex.exp (logContour f r τ lam θ i)) from
    funext (deformedPoint_exp_log f hr τ lam θ)]
  ring

 theorem differentiableAt_quotient {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {g h : E → ℂ} {x : E} (hg : DifferentiableAt ℂ g x) (hh : DifferentiableAt ℂ h x)
    (hx : h x ≠ 0) : DifferentiableAt ℂ (fun y => g y/h y) x := by
  simpa only [div_eq_mul_inv,Pi.inv_apply] using hg.fun_mul (hh.inv hx)

 theorem differentiableAt_finite_product {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (g : ι → E → ℂ) (x : E)
    (hg : ∀ i ∈ S, DifferentiableAt ℂ (g i) x) :
    DifferentiableAt ℂ (fun y => ∏ i ∈ S, g i y) x := by
  exact (HasFDerivAt.finsetProd (fun i hi => (hg i hi).hasFDerivAt)).differentiableAt

 theorem logDensity_differentiableAt (N : ℕ) (hN : 0 < N) (s : ℂ) (ℓ : Fin N → ℂ)
    (hW : ∀ i, 0 < (sourceW s (Complex.exp (ℓ i))).im)
    (hY : 1-coordinateProduct (fun i => Complex.exp (ℓ i)) ≠ 0) :
    DifferentiableAt ℂ (logDensity N s) ℓ := by
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
  have hZ1 := one_sub_coordinateProduct_ne_zero hN hzn
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
  have ddensity : DifferentiableAt ℂ (fun x => canceledReducedDensity (z x) (y x)) ℓ :=
    (((differentiableAt_quotient ((dZ.inv hZ0).add (dY.inv hY0))
      (((differentiableAt_const (1:ℂ)).sub dZ).mul ((differentiableAt_const (1:ℂ)).sub dY))
      (mul_ne_zero hZ1 hY)).mul dpair).mul dres)
  exact ((dY.const_mul ((N.factorial:ℂ)⁻¹*(2*(Real.pi:ℂ)*Complex.I)^(-(N:ℤ)))).mul ddensity)

 theorem logDensity_on_source_differentiable {N : ℕ} (hN : 0 < N)
    (f : SelectorFunctions) {r τ lam : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hτ : 0 ≤ τ) (hlam : 0 ≤ lam) (s : ℂ)
    (hmargin : r⁻¹-r < (sourceS s).im)
    (hp : ∀ x, 0 ≤ f.p x) (hm0 : ∀ x, 0 ≤ f.m x) (hm1 : ∀ x, f.m x ≤ 1)
    (hps : ∀ x, Real.sin x ≤ 0 → f.p x=0)
    (hms : ∀ x, 0 ≤ Real.sin x → f.m x=0) (θ : Fin N → ℝ) :
    DifferentiableAt ℂ (logDensity N s) (logContour f r τ lam θ) := by
  apply logDensity_differentiableAt N hN s
  · intro i
    rw [← deformedPoint_exp_log f hr]
    exact (sourceW_upper_of_margin hr hr1 hmargin (deformedPoint_zero_norm f hr.le τ θ i)).trans_le
      (deformed_sourceW_im_ge hN f hr hτ hlam θ s hp hm0 hps hms i)
  · have hY := homotopy_y_gap_nonzero hN f hr hr1 hτ hlam θ hp hm1
    rwa [show deformedPoint f r τ lam θ = (fun i => Complex.exp (logContour f r τ lam θ i)) from
      funext (deformedPoint_exp_log f hr τ lam θ)] at hY

 def homotopyFlux {N : ℕ} (f : SelectorFunctions) (r τ lam : ℝ) (s : ℂ)
    (θ : Fin N → ℝ) (q : Fin N) : ℂ :=
  logDensity N s (logContour f r τ lam θ)*
    ((angularJacobian f τ lam θ).updateCol q (complexShift f τ θ)).det

 theorem source_pointwise_conservation {N : ℕ} (hN : 0 < N)
    (f : SelectorFunctions) {r τ lam : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hτ : 0 ≤ τ) (hlam : 0 ≤ lam) (s : ℂ)
    (hmargin : r⁻¹-r < (sourceS s).im)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m)
    (hp0 : ∀ x, 0 ≤ f.p x) (hm0 : ∀ x, 0 ≤ f.m x) (hm1 : ∀ x, f.m x ≤ 1)
    (hps : ∀ x, Real.sin x ≤ 0 → f.p x=0)
    (hms : ∀ x, 0 ≤ Real.sin x → f.m x=0) (θ : Fin N → ℝ) :
    deriv (fun u => pulledDensity f r τ u s θ) lam =
      ∑ i, deriv (fun u => homotopyFlux f r τ lam s (Function.update θ i u) i) (θ i) := by
  have hF := logDensity_on_source_differentiable hN f hr hr1 hτ hlam s hmargin hp0 hm0 hm1 hps hms θ
  rw [logContour_eq_affine] at hF
  have hc := smooth_affine_homotopy_conservation (fun _ => (Real.log r:ℂ))
    (complexShift f τ) (complexShift_contDiff f τ hp hm) (logDensity N s) lam θ hF
  simp_rw [← logContour_eq_affine f r τ] at hc
  simp_rw [← angularJacobian_eq_affine f r τ _ hp hm] at hc
  simp_rw [pulledDensity_eq_log f hr]
  exact hc

 theorem homotopyFlux_named {N : ℕ} (f : SelectorFunctions) {r : ℝ} (hr : 0 < r)
    (τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ) (q : Fin N)
    (hp : f.p (θ q)=1) (hp' : deriv f.p (θ q)=0)
    (hm : f.m (θ q)=0) (hm' : deriv f.m (θ q)=0) :
    homotopyFlux f r τ lam s θ q = 2*Complex.I*(τ:ℂ)*pulledDensity f r τ lam s θ := by
  rw [pulledDensity_eq_log f hr]
  unfold homotopyFlux angularJacobian complexShift shiftMap
  rw [retraction_named_minor lam τ _ _ _ _ q hp hp' hm hm']
  ring

end
end IsingBulk.Tail
