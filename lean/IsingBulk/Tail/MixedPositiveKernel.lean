import IsingBulk.Tail.OriginalCurrentGlobalFactors
import IsingBulk.Tail.MixedFrozenPhase
import IsingBulk.Tail.AllBranchExteriorKernelFloor

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch
open scoped BigOperators

/-- Actual coupled-contour product floors, uniform in dimension and occupancy. -/
theorem mixed_actual_product_floors (theta c τ : ℝ)
    (hθ : 0 < Real.sin theta) (hc : 0 < c) (hcs : c < Real.sin theta/2) (hτ : 0 ≤ τ)
    (f : SelectorFunctions) (hp : ∀ x, 0 ≤ f.p x) (hp1 : ∀ x, f.p x ≤ 1)
    (hm : ∀ x, 0 ≤ f.m x) (hm1 : ∀ x, f.m x ≤ 1)
    (hps : ∀ x, Real.sin x ≤ 0 → f.p x=0)
    (hms : ∀ x, 0 ≤ Real.sin x → f.m x=0) :
    ∃ δ e a : ℝ, 0 < δ ∧ δ ≤ 1/16 ∧ 0 < e ∧ e ≤ 1 ∧ 0 < a ∧
      ∀ N : ℕ, 1 ≤ N → ∀ eps lam : ℝ, 0 < eps → eps < e →
      0 ≤ lam → lam ≤ 1 → ∀ θ : Fin N → ℝ, ∀ s : ℂ,
      ‖s-radialParameter theta eps‖ ≤ δ*eps →
      ‖coordinateProduct (deformedPoint f (Real.exp (-c*eps)) τ lam θ)‖ ≤ Real.exp (-c*eps) ∧
      ‖coordinateProduct (fun i => globalRoot s (deformedPoint f (Real.exp (-c*eps)) τ lam θ i))‖ ≤ Real.exp (-a*eps) := by
  obtain ⟨δ,e,hδ,hδs,he,he1,hmargin⟩ := original_disk_trace_margin theta c hθ hc hcs
  let E := Real.exp (c+2*τ)
  let M := 5+E
  let a := c/(2*M+1)
  have hE : 0 < E := Real.exp_pos _
  have hM : 0 < M := by dsimp [M]; positivity
  have ha : 0 < a := by dsimp [a]; positivity
  refine ⟨δ,e,a,hδ,hδs,he,he1,ha,?_⟩
  intro N hN eps lam heps hepslt hl hl1 θ s hs
  have heps1 : eps ≤ 1 := hepslt.le.trans he1
  have hmar := hmargin eps heps hepslt s hs
  let y := deformedPoint f (Real.exp (-c*eps)) τ lam θ
  have hys := current_y_norm_envelope (by omega : 0<N) f hc.le hτ heps.le heps1 hl hl1 hp hp1 hm hm1 θ
  have hsn : 1/2 ≤ ‖s‖ := norm_ge_half_of_near_unit (t := radialParameter theta eps)
    (by rw [radialParameter_norm heps.le]; linarith) (by nlinarith)
  have hs3 : ‖s‖ ≤ 3 := by
    have hh := norm_le_norm_add_norm_sub (radialParameter theta eps) s
    rw [radialParameter_norm heps.le,norm_sub_rev] at hh
    nlinarith
  have hWnorm (i : Fin N) : ‖sourceW s (y i)‖ ≤ M :=
    selected_sourceW_envelope hsn hs3 (hys i).1 (hys i).2
  have hWmargin (i : Fin N) : c*eps ≤ (sourceW s (y i)).im :=
    original_current_dispersion_margin (by omega) f hc heps hτ hl θ hp hm hps hms hmar i
  have hWpos (i : Fin N) : 0 < (sourceW s (y i)).im := (mul_pos hc heps).trans_le (hWmargin i)
  have hz1 (i : Fin N) : ‖globalRoot s (y i)‖ ≤ 1 := (interiorRoot_norm_lt_one (hWpos i)).le
  have hzexp (i : Fin N) : ‖globalRoot s (y i)‖ ≤ Real.exp (-a*eps) := by
    have hh := interiorRoot_exponential_attenuation (hWpos i) (hWnorm i) (hWmargin i)
    change ‖interiorRoot (sourceW s (y i))‖ ≤ _
    convert hh using 1
    dsimp [a]
    congr 1
    ring
  exact ⟨original_current_y_product_bound hN f hc.le heps.le hτ hl θ hp hm1,
    (coordinateProduct_norm_le_anchor _ ⟨0,by omega⟩ hz1).trans (hzexp _)⟩

/-- The actual two phases, with no frozen occupancy, control both simple poles. -/
theorem mixed_actual_positive_kernel {N : ℕ} (f : SelectorFunctions)
    {r : ℝ} (hr : 0 < r) (τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hy : ‖coordinateProduct (deformedPoint f r τ lam θ)‖ ≤ Real.exp (-a))
    (hz : ‖coordinateProduct (fun i => globalRoot s (deformedPoint f r τ lam θ i))‖ ≤ Real.exp (-b)) :
    ‖(1-coordinateProduct (deformedPoint f r τ lam θ))*
      (1-coordinateProduct (fun i => globalRoot s (deformedPoint f r τ lam θ i)))‖⁻¹ ≤
      4*twoPhaseKernel a b (∑ i, θ i, (mixedContourPhaseSum f r τ lam s θ).re) := by
  rw [mixed_actual_Y_exp f hr τ lam θ] at hy ⊢
  rw [mixed_actual_Z_exp f r τ lam s θ] at hz ⊢
  have hY := allBranchExterior_exp_kernel_floor (mixedContourLogSum f r τ lam θ) ha hy
  have hZ := allBranchExterior_exp_kernel_floor (-Complex.I*mixedContourPhaseSum f r τ lam s θ) hb hz
  have hiY : (mixedContourLogSum f r τ lam θ).im = ∑ i, θ i := by
    simp [mixedContourLogSum, logContour]
  have hiZ : (-Complex.I*mixedContourPhaseSum f r τ lam s θ).im =
      -(mixedContourPhaseSum f r τ lam s θ).re := by simp [Complex.mul_im]
  rw [hiY] at hY
  rw [hiZ,phaseDenominator_neg] at hZ
  have hh := mul_le_mul hY hZ (inv_nonneg.mpr (norm_nonneg _)) (by
    unfold phaseDenominator
    positivity)
  rw [norm_mul,mul_inv_rev]
  unfold twoPhaseKernel
  convert hh using 1 <;> ring

end
end IsingBulk.Tail
