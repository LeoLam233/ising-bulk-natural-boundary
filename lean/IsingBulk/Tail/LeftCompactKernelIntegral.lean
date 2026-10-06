import IsingBulk.Tail.AngularOnePhaseIntegral
import IsingBulk.Tail.MixedNegativeSourceKernel
import IsingBulk.Tail.MixedKernelRadialBudget

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First Set MeasureTheory
open scoped BigOperators

theorem onePhaseSum_det_all {N : ℕ} (p : Fin N) : (onePhaseSumDerivative p).det=1 := by
  classical
  by_cases h : ∃ q : Fin N,p≠q
  · obtain ⟨q,hq⟩ := h
    exact onePhaseSum_det p q hq
  have hall (q : Fin N) : q=p := by by_contra hq; exact h ⟨q,Ne.symm hq⟩
  have he : onePhaseSumDerivative p=ContinuousLinearMap.id ℝ (Fin N → ℝ) := by
    ext u i
    rw [hall i]
    simp only [onePhaseSumDerivative,ContinuousLinearMap.pi_apply,ite_true,
      coordinateSumLinear_apply,ContinuousLinearMap.id_apply]
    exact Finset.sum_eq_single p (fun j _ hj => False.elim (hj (hall j))) (by simp)
  rw [he]
  change (LinearMap.id : (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ)).det=1
  exact LinearMap.det_id

theorem angular_sum_phase_integral {N : ℕ} (q : Fin N) {a : ℝ} (ha : 0<a) (ha1 : a≤1) :
    IntegrableOn (fun θ : Fin N → ℝ => (phaseDenominator (Real.exp (-a)) (∑ i,θ i))⁻¹) (angleBox N) ∧
      (∫ θ in angleBox N,(phaseDenominator (Real.exp (-a)) (∑ i,θ i))⁻¹)≤
        ((N:ℝ)*simpleKernelConstant*(1+|Real.log a|))*(2*Real.pi)^(N-1) := by
  let L : Fin N → ℝ → ℝ := fun _ _ => 1
  let C : Fin N → ℝ := fun _ => 2*Real.pi
  have hLint (i : Fin N) : (∫ t in Icc 0 (2*Real.pi),L i t)≤C i := by
    simp [L,C,Real.volume_real_Icc_of_le (by positivity : (0:ℝ)≤2*Real.pi)]
  have hk := angular_one_phase_product_integral q L C (fun _ _ => zero_le_one) ha ha1
    (fun _ => continuousOn_const) hLint
  have hh := injective_coordinate_weighted_coarea_on (S := angleBox N) measurableSet_Icc
    (onePhaseSumMap q 0) (fun _ => onePhaseSumDerivative q)
    (fun θ _ => (onePhaseSum_hasFDerivAt q 0 θ).hasFDerivWithinAt)
    (onePhaseSum_injective q 0).injOn (angularOnePhaseMap_image q)
    (fun _ => 1) (onePhaseSpectatorKernel q a L) continuousOn_const
    (angularOnePhaseKernel_continuousOn q ha L (fun _ => continuousOn_const))
    (onePhaseSpectatorKernel_nonneg q a L (fun _ _ => zero_le_one)) hk.1 (C := 1) zero_le_one
    (fun _ _ => zero_le_one) (fun _ _ => by rw [onePhaseSum_det_all]; norm_num)
  simp only [one_mul,onePhaseSum_kernel_eq,mul_zero,sub_zero,L,Finset.prod_const_one,mul_one] at hh
  refine ⟨hh.1,hh.2.trans ?_⟩
  simpa only [C,Finset.prod_const,Finset.card_erase_of_mem (Finset.mem_univ q),
    Finset.card_univ,Fintype.card_fin] using hk.2

def leftCompactIntegralBudget (N : ℕ) (a : ℝ) : ℝ :=
  2*((N:ℝ)*simpleKernelConstant*(1+|Real.log a|))*(2*Real.pi)^(N-1)

theorem left_compact_source_kernel_integral {N : ℕ} (hN : 1≤N) (q : Fin N)
    (f : SelectorFunctions) {c eps τ lam : ℝ} (hc : 0<c) (he : 0<eps) (ha1 : c*eps≤1)
    (hτ : 0≤τ) (hl : 0≤lam) (hp : ∀ x,0≤f.p x) (hm : ∀ x,f.m x≤1)
    (F : (Fin N → ℝ) → ℂ) (hF : IntegrableOn F (angleBox N)) {D : ℝ} (hD : 0≤D)
    (hpoint : ∀ θ∈angleBox N,‖F θ‖≤D*
      ‖(1-coordinateProduct (deformedPoint f (Real.exp (-c*eps)) τ lam θ))⁻¹‖) :
    ‖∫ θ in angleBox N,F θ‖≤D*leftCompactIntegralBudget N (c*eps) := by
  have hk := angular_sum_phase_integral q (mul_pos hc he) ha1
  have hbound (θ : Fin N → ℝ) (hθ : θ∈angleBox N) :
      ‖F θ‖≤(D*2)*(phaseDenominator (Real.exp (-(c*eps))) (∑ i,θ i))⁻¹ := by
    have hY := original_current_y_product_bound hN f hc.le he.le hτ hl θ hp hm
    have hh := mixed_actual_Y_kernel_floor f (Real.exp_pos _) τ lam θ (mul_pos hc he)
      (by simpa only [neg_mul] using hY)
    have hh' := mul_le_mul_of_nonneg_left hh hD
    have hpoint' := hpoint θ hθ
    rw [norm_inv] at hpoint'
    simp only [neg_mul] at hpoint'
    exact hpoint'.trans (hh'.trans_eq (by ring))
  calc
    _ ≤ ∫ θ in angleBox N,‖F θ‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ θ in angleBox N,(D*2)*(phaseDenominator (Real.exp (-(c*eps))) (∑ i,θ i))⁻¹ :=
      setIntegral_mono_on hF.norm (hk.1.const_mul _) measurableSet_Icc hbound
    _ = (D*2)*(∫ θ in angleBox N,(phaseDenominator (Real.exp (-(c*eps))) (∑ i,θ i))⁻¹) := integral_const_mul _ _
    _ ≤ (D*2)*(((N:ℝ)*simpleKernelConstant*(1+|Real.log (c*eps)|))*(2*Real.pi)^(N-1)) :=
      mul_le_mul_of_nonneg_left hk.2 (by positivity)
    _ = _ := by unfold leftCompactIntegralBudget; ring

theorem left_compact_kernel_radial_budget (c : ℝ) (hc : 0<c) :
    ∃ K : ℝ,0<K ∧ ∀ (N : ℕ) (H : ℝ),1≤N → 0≤H →
      leftCompactIntegralBudget N (c*Real.exp (-H))≤K^N*(N:ℝ)^2*(H+1)^2 := by
  let A := 2*simpleKernelConstant*(1+|Real.log c|)
  let P := max 1 (2*Real.pi)
  have hsk := simpleKernelConstant_pos
  have hA : 0≤A := by dsimp [A]; positivity
  refine ⟨max 1 A*P,mul_pos (zero_lt_one.trans_le (le_max_left _ _))
    (zero_lt_one.trans_le (le_max_left _ _)),?_⟩
  intro N H hN hH
  have hn : (1:ℝ)≤N := by exact_mod_cast hN
  have hLog := allBranchExterior_radial_log_factor c H hc hH
  have hPow : (2*Real.pi)^(N-1)≤P^N :=
    (pow_le_pow_left₀ (by positivity) (le_max_right _ _) _).trans
      (pow_le_pow_right₀ (le_max_left _ _) (Nat.sub_le _ _))
  have hConst := mixed_constant_le_exponential A hN
  calc
    _ ≤ 2*((N:ℝ)*simpleKernelConstant*((1+|Real.log c|)*(H+1)))*P^N := by
      unfold leftCompactIntegralBudget
      gcongr
    _ = A*(N:ℝ)*(H+1)*P^N := by dsimp [A]; ring
    _ ≤ A*(N:ℝ)^2*(H+1)^2*P^N := by gcongr <;> nlinarith
    _ ≤ (max 1 A)^N*(N:ℝ)^2*(H+1)^2*P^N := by gcongr
    _ = _ := by rw [mul_pow]; ring

end
end IsingBulk.Tail
