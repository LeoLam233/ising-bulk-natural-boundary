import IsingBulk.Tail.OriginalCurrentRootModulus
import IsingBulk.Tail.AllBranchExteriorKernelFloor
import IsingBulk.Tail.CompactPhaseSymmetry

/-! Full N-dependent attenuation floors for the actual coupled unwrapped
phase, before any angular integration or differentiation. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch
open scoped BigOperators
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

theorem original_current_y_product_full_attenuation {N : ℕ} (hN : 0<N) (f : SelectorFunctions)
    {c eps τ lam : ℝ} (hτ : 0≤τ) (hl : 0≤lam) (θ : Fin N → ℝ)
    (hp : ∀ x, 0≤f.p x) (hm : ∀ x, f.m x≤1) :
    ‖coordinateProduct (deformedPoint f (Real.exp (-c*eps)) τ lam θ)‖≤Real.exp (-c*(N:ℝ)*eps) := by
  have hsum := sum_retractionShift_le hN hτ (fun i => hp (θ i)) (fun i => hm (θ i))
  have hP := occupancy_nonneg (fun i => hp (θ i))
  have hsum0 : (∑ i, retractionShift τ (fun j => f.p (θ j)) (fun j => f.m (θ j)) i)≤0 := by
    nlinarith [mul_nonneg hτ hP]
  rw [deformed_product_norm f (Real.exp_nonneg _),← Real.exp_nat_mul,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonpos_of_nonneg_of_nonpos hl hsum0]

theorem unwrappedLogY_im {N : ℕ} (f : SelectorFunctions) (r τ lam : ℝ) (θ : Fin N → ℝ) :
    (unwrappedLogY f r τ lam θ).im=∑ i, θ i := by
  simp [unwrappedLogY]

def currentGlobalCayley {N : ℕ} (f : SelectorFunctions) (r τ lam : ℝ) (s : ℂ)
    (θ : Fin N → ℝ) : ℂ :=
  let Y := coordinateProduct (deformedPoint f r τ lam θ)
  let Z := coordinateProduct (fun i => selectedContinuedRoot s (deformedPoint f r τ lam θ i))
  ((1+Y)/(1-Y))*((1+Z)/(1-Z))

theorem current_global_cayley_phase_floor {N : ℕ} (f : SelectorFunctions) {r : ℝ}
    (hr : 0<r) (τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ) {a b : ℝ} (ha : 0<a) (hb : 0<b)
    (hY : ‖coordinateProduct (deformedPoint f r τ lam θ)‖≤Real.exp (-a))
    (hZ : ‖coordinateProduct (fun i => selectedContinuedRoot s (deformedPoint f r τ lam θ i))‖≤Real.exp (-b)) :
    ‖currentGlobalCayley f r τ lam s θ‖≤
      16*twoPhaseKernel a b ((∑ i, θ i),currentUnwrappedPhase f r τ lam s θ) := by
  let Y := coordinateProduct (deformedPoint f r τ lam θ)
  let Z := coordinateProduct (fun i => selectedContinuedRoot s (deformedPoint f r τ lam θ i))
  have hyexp : Complex.exp (unwrappedLogY f r τ lam θ)=Y := unwrappedLogY_exp f hr τ lam θ
  have hzexp : Complex.exp (-Complex.I*currentComplexPhase f r τ lam s θ)=Z :=
    (product_root_unwrapped_phase (fun i => sourceW s (deformedPoint f r τ lam θ i))).symm
  have hy := allBranchExterior_exp_kernel_floor (unwrappedLogY f r τ lam θ) ha (by rwa [hyexp])
  have hz := allBranchExterior_exp_kernel_floor (-Complex.I*currentComplexPhase f r τ lam s θ) hb (by rwa [hzexp])
  rw [hyexp,unwrappedLogY_im] at hy
  have hzIm : (-Complex.I*currentComplexPhase f r τ lam s θ).im= -currentUnwrappedPhase f r τ lam s θ := by
    rw [currentUnwrappedPhase_eq_re]
    simp [Complex.mul_im]
  rw [hzexp,hzIm,phaseDenominator_neg] at hz
  have hY1 : ‖Y‖≤1 := hY.trans (Real.exp_le_one_iff.mpr (by linarith))
  have hZ1 : ‖Z‖≤1 := hZ.trans (Real.exp_le_one_iff.mpr (by linarith))
  have hny : ‖1+Y‖≤2 := (norm_add_le _ _).trans (by simp only [norm_one]; linarith)
  have hnz : ‖1+Z‖≤2 := (norm_add_le _ _).trans (by simp only [norm_one]; linarith)
  change ‖((1+Y)/(1-Y))*((1+Z)/(1-Z))‖≤_
  rw [norm_mul,norm_div,norm_div,div_eq_mul_inv,div_eq_mul_inv]
  have hya : 0≤(phaseDenominator (Real.exp (-a)) (∑ i, θ i))⁻¹ := inv_nonneg.mpr (norm_nonneg _)
  have hza : 0≤(phaseDenominator (Real.exp (-b)) (currentUnwrappedPhase f r τ lam s θ))⁻¹ := inv_nonneg.mpr (norm_nonneg _)
  calc
    _ ≤ (2*(2*(phaseDenominator (Real.exp (-a)) (∑ i, θ i))⁻¹))*
        (2*(2*(phaseDenominator (Real.exp (-b)) (currentUnwrappedPhase f r τ lam s θ))⁻¹)) :=
      mul_le_mul (mul_le_mul hny hy (inv_nonneg.mpr (norm_nonneg _)) (by norm_num))
        (mul_le_mul hnz hz (inv_nonneg.mpr (norm_nonneg _)) (by norm_num)) (by positivity) (by positivity)
    _ = _ := by unfold twoPhaseKernel; ring

end
end IsingBulk.Tail
