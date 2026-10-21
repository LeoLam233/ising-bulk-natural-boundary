import IsingBulk.Tail.LeftCompactKernelIntegral
import IsingBulk.HT.Lie.SignedBranchKernel

/-! True angular sum-phase integration for the remaining signed Y kernel,
with explicit spectator volume and all N including one. -/
namespace IsingBulk.HT.Contour
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.HT.Lie Set MeasureTheory
open scoped BigOperators

def shiftedOnePhaseSpectatorKernel {N : ℕ} (ξ : ℝ) (p : Fin N) (a : ℝ)
    (L : Fin N → ℝ → ℝ) (u : Fin N → ℝ) : ℝ :=
  ∏ i, if i=p then shiftedPhaseKernel a ξ (u i) else L i (u i)

theorem shiftedOnePhaseSpectatorKernel_nonneg {N : ℕ} (ξ : ℝ) (p : Fin N) (a : ℝ)
    (L : Fin N → ℝ → ℝ) (hL : ∀ i t,0≤L i t) (u : Fin N → ℝ) :
    0≤shiftedOnePhaseSpectatorKernel ξ p a L u := by
  apply Finset.prod_nonneg
  intro i _
  split_ifs
  · exact shiftedPhaseKernel_nonneg a ξ (u i)
  · exact hL i (u i)

theorem shiftedOnePhaseSum_kernel_eq {N : ℕ} (ξ : ℝ) (p : Fin N) (b a : ℝ)
    (L : Fin N → ℝ → ℝ) (u : Fin N → ℝ) :
    shiftedOnePhaseSpectatorKernel ξ p a L (onePhaseSumMap p b u)=
      shiftedPhaseKernel a ξ ((∑ i,u i)-(N:ℝ)*b)*∏ i∈Finset.univ.erase p,L i (u i) := by
  unfold shiftedOnePhaseSpectatorKernel
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ p)]
  simp only [ite_true,onePhaseSumMap]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  simp [(Finset.mem_erase.mp hi).1]

theorem shiftedAngularOnePhaseKernel_continuousOn (ξ : ℝ) {N : ℕ} (p : Fin N) {a : ℝ}
    (ha : 0<a) (L : Fin N → ℝ → ℝ) (hL : ∀ i,ContinuousOn (L i) (Icc 0 (2*Real.pi))) :
    ContinuousOn (shiftedOnePhaseSpectatorKernel ξ p a L) (angularOnePhaseBox p) := by
  apply continuousOn_finsetProd
  intro i _
  by_cases hip : i=p
  · simp only [hip,ite_true]
    exact ((shiftedPhaseKernel_continuous ha ξ).comp (continuous_apply p)).continuousOn
  · simp only [hip,ite_false]
    apply (hL i).comp (continuous_apply i).continuousOn
    intro θ hθ
    exact ⟨hθ.1 i,by simpa [angularOnePhaseBox,hip] using hθ.2 i⟩

theorem shifted_angular_one_phase_product_integral (ξ : ℝ) {N : ℕ} (p : Fin N)
    (L : Fin N → ℝ → ℝ) (C : Fin N → ℝ) (hL0 : ∀ i t,0≤L i t)
    {a : ℝ} (ha : 0<a) (ha1 : a≤1)
    (hL : ∀ i,ContinuousOn (L i) (Icc 0 (2*Real.pi)))
    (hLint : ∀ i,(∫ t in Icc 0 (2*Real.pi),L i t)≤C i) :
    IntegrableOn (shiftedOnePhaseSpectatorKernel ξ p a L) (angularOnePhaseBox p) ∧
      (∫ θ in angularOnePhaseBox p,shiftedOnePhaseSpectatorKernel ξ p a L θ)≤
        ((N:ℝ)*simpleKernelConstant*(1+|Real.log a|))*(∏ i∈Finset.univ.erase p,C i) := by
  refine ⟨(shiftedAngularOnePhaseKernel_continuousOn ξ p ha L hL).integrableOn_compact isCompact_Icc,?_⟩
  let h := fun i : Fin N => if i=p then (N:ℝ)*(2*Real.pi) else 2*Real.pi
  let w := fun i t => if i=p then shiftedPhaseKernel a ξ t else L i t
  let A := (N:ℝ)*simpleKernelConstant*(1+|Real.log a|)
  have hmeasure : volume.restrict (angularOnePhaseBox p)=
      Measure.pi (fun i => volume.restrict (Icc 0 (h i))) := by
    rw [angularOnePhaseBox,← Set.pi_univ_Icc,volume_pi,Measure.restrict_pi_pi]
  change (∫ θ in angularOnePhaseBox p,∏ i,w i (θ i))≤_
  rw [hmeasure,integral_fintype_prod_eq_prod]
  have hphase : (∫ t in Icc 0 ((N:ℝ)*(2*Real.pi)),shiftedPhaseKernel a ξ t)≤A := by
    have hh := shifted_kernel_interval_integral ha ha1 ξ N (show 0≤(N:ℝ)*(2*Real.pi) by positivity)
      (by ring_nf; rfl)
    rwa [intervalIntegral.integral_of_le (by positivity),← integral_Icc_eq_integral_Ioc] at hh
  calc
    _ ≤ ∏ i : Fin N,if i=p then A else C i := by
      apply Finset.prod_le_prod₀
      · intro i _
        apply integral_nonneg
        intro t
        dsimp [w]
        split_ifs
        · exact shiftedPhaseKernel_nonneg a ξ t
        · exact hL0 i t
      · intro i _
        by_cases hip : i=p
        · subst i; simpa [w,h] using hphase
        · simpa [w,h,hip] using hLint i
    _ = _ := by
      rw [← Finset.mul_prod_erase Finset.univ (fun i => if i=p then A else C i) (Finset.mem_univ p)]
      simp only [ite_true]
      congr 1
      apply Finset.prod_congr rfl
      intro i hi
      simp [(Finset.mem_erase.mp hi).1]

theorem shifted_angular_sum_phase_integral (ξ : ℝ) {N : ℕ} (q : Fin N) {a : ℝ} (ha : 0<a) (ha1 : a≤1) :
    IntegrableOn (fun θ : Fin N → ℝ => shiftedPhaseKernel a ξ (∑ i,θ i)) (angleBox N) ∧
      (∫ θ in angleBox N,shiftedPhaseKernel a ξ (∑ i,θ i))≤
        ((N:ℝ)*simpleKernelConstant*(1+|Real.log a|))*(2*Real.pi)^(N-1) := by
  let L : Fin N → ℝ → ℝ := fun _ _ => 1
  let C : Fin N → ℝ := fun _ => 2*Real.pi
  have hLint (i : Fin N) : (∫ t in Icc 0 (2*Real.pi),L i t)≤C i := by
    simp [L,C,Real.volume_real_Icc_of_le (by positivity : (0:ℝ)≤2*Real.pi)]
  have hk := shifted_angular_one_phase_product_integral ξ q L C (fun _ _ => zero_le_one) ha ha1
    (fun _ => continuousOn_const) hLint
  have hh := injective_coordinate_weighted_coarea_on (S := angleBox N) measurableSet_Icc
    (onePhaseSumMap q 0) (fun _ => onePhaseSumDerivative q)
    (fun θ _ => (onePhaseSum_hasFDerivAt q 0 θ).hasFDerivWithinAt)
    (onePhaseSum_injective q 0).injOn (angularOnePhaseMap_image q)
    (fun _ => 1) (shiftedOnePhaseSpectatorKernel ξ q a L) continuousOn_const
    (shiftedAngularOnePhaseKernel_continuousOn ξ q ha L (fun _ => continuousOn_const))
    (shiftedOnePhaseSpectatorKernel_nonneg ξ q a L (fun _ _ => zero_le_one)) hk.1 (C := 1) zero_le_one
    (fun _ _ => zero_le_one) (fun _ _ => by rw [onePhaseSum_det_all]; norm_num)
  simp only [one_mul,shiftedOnePhaseSum_kernel_eq,mul_zero,sub_zero,L,Finset.prod_const_one,mul_one] at hh
  refine ⟨hh.1,hh.2.trans ?_⟩
  simpa only [C,Finset.prod_const,Finset.card_erase_of_mem (Finset.mem_univ q),
    Finset.card_univ,Fintype.card_fin] using hk.2

theorem signed_mixed_actual_Y_kernel_floor (ξ : ℝ) {N : ℕ} (f : SelectorFunctions) {r : ℝ} (hr : 0<r)
    (τ lam : ℝ) (θ : Fin N → ℝ) {a : ℝ} (ha : 0<a)
    (hY : ‖coordinateProduct (deformedPoint f r τ lam θ)‖≤Real.exp (-a)) :
    ‖1-Complex.exp (Complex.I*(ξ:ℂ))*coordinateProduct (deformedPoint f r τ lam θ)‖⁻¹≤
      2*shiftedPhaseKernel a ξ (∑ i,θ i) := by
  rw [mixed_actual_Y_exp f hr τ lam θ] at hY ⊢
  have hh := signed_exp_kernel_floor (mixedContourLogSum f r τ lam θ) ξ ha hY
  have heq : (mixedContourLogSum f r τ lam θ).im=∑ i,θ i := by
    simp [mixedContourLogSum,logContour]
  rwa [heq] at hh

theorem signed_left_compact_source_kernel_integral (ξ : ℝ) {N : ℕ} (hN : 1≤N) (q : Fin N)
    (f : SelectorFunctions) {c eps τ lam : ℝ} (hc : 0<c) (he : 0<eps) (ha1 : c*eps≤1)
    (hτ : 0≤τ) (hl : 0≤lam) (hp : ∀ x,0≤f.p x) (hm : ∀ x,f.m x≤1)
    (F : (Fin N → ℝ) → ℂ) (hF : IntegrableOn F (angleBox N)) {D : ℝ} (hD : 0≤D)
    (hpoint : ∀ θ∈angleBox N,‖F θ‖≤D*
      ‖(1-Complex.exp (Complex.I*(ξ:ℂ))*coordinateProduct (deformedPoint f (Real.exp (-c*eps)) τ lam θ))⁻¹‖) :
    ‖∫ θ in angleBox N,F θ‖≤D*leftCompactIntegralBudget N (c*eps) := by
  have hk := shifted_angular_sum_phase_integral ξ q (mul_pos hc he) ha1
  have hbound (θ : Fin N → ℝ) (hθ : θ∈angleBox N) :
      ‖F θ‖≤(D*2)*shiftedPhaseKernel (c*eps) ξ (∑ i,θ i) := by
    have hY := original_current_y_product_bound hN f hc.le he.le hτ hl θ hp hm
    have hh := signed_mixed_actual_Y_kernel_floor ξ f (Real.exp_pos _) τ lam θ (mul_pos hc he)
      (by simpa only [neg_mul] using hY)
    have hh' := mul_le_mul_of_nonneg_left hh hD
    have hpoint' := hpoint θ hθ
    rw [norm_inv] at hpoint'
    simp only [neg_mul] at hpoint'
    exact hpoint'.trans (hh'.trans_eq (by ring))
  calc
    _ ≤ ∫ θ in angleBox N,‖F θ‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ θ in angleBox N,(D*2)*shiftedPhaseKernel (c*eps) ξ (∑ i,θ i) :=
      setIntegral_mono_on hF.norm (hk.1.const_mul _) measurableSet_Icc hbound
    _ = (D*2)*(∫ θ in angleBox N,shiftedPhaseKernel (c*eps) ξ (∑ i,θ i)) := integral_const_mul _ _
    _ ≤ (D*2)*(((N:ℝ)*simpleKernelConstant*(1+|Real.log (c*eps)|))*(2*Real.pi)^(N-1)) :=
      mul_le_mul_of_nonneg_left hk.2 (by positivity)
    _ = _ := by unfold leftCompactIntegralBudget; ring


end
end IsingBulk.HT.Contour
