import IsingBulk.Tail.OnePhaseSumIntegral
import IsingBulk.Tail.MixedPositiveGlobalIntegral

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First Set MeasureTheory
open scoped BigOperators

def angularOnePhaseBox {N : ℕ} (p : Fin N) : Set (Fin N → ℝ) :=
  Icc (fun _ => 0) (fun i => if i=p then (N:ℝ)*(2*Real.pi) else 2*Real.pi)

theorem angularOnePhaseKernel_continuousOn {N : ℕ} (p : Fin N) {a : ℝ}
    (ha : 0<a) (L : Fin N → ℝ → ℝ) (hL : ∀ i,ContinuousOn (L i) (Icc 0 (2*Real.pi))) :
    ContinuousOn (onePhaseSpectatorKernel p a L) (angularOnePhaseBox p) := by
  apply continuousOn_finsetProd
  intro i _
  by_cases hip : i=p
  · simp only [hip,ite_true]
    exact ((simple_kernel_continuous ha).comp (continuous_apply p)).continuousOn
  · simp only [hip,ite_false]
    apply (hL i).comp (continuous_apply i).continuousOn
    intro θ hθ
    exact ⟨hθ.1 i,by simpa [angularOnePhaseBox,hip] using hθ.2 i⟩

theorem angular_one_phase_product_integral {N : ℕ} (p : Fin N)
    (L : Fin N → ℝ → ℝ) (C : Fin N → ℝ) (hL0 : ∀ i t,0≤L i t)
    {a : ℝ} (ha : 0<a) (ha1 : a≤1)
    (hL : ∀ i,ContinuousOn (L i) (Icc 0 (2*Real.pi)))
    (hLint : ∀ i,(∫ t in Icc 0 (2*Real.pi),L i t)≤C i) :
    IntegrableOn (onePhaseSpectatorKernel p a L) (angularOnePhaseBox p) ∧
      (∫ θ in angularOnePhaseBox p,onePhaseSpectatorKernel p a L θ)≤
        ((N:ℝ)*simpleKernelConstant*(1+|Real.log a|))*(∏ i∈Finset.univ.erase p,C i) := by
  refine ⟨(angularOnePhaseKernel_continuousOn p ha L hL).integrableOn_compact isCompact_Icc,?_⟩
  let h := fun i : Fin N => if i=p then (N:ℝ)*(2*Real.pi) else 2*Real.pi
  let w := fun i t => if i=p then (phaseDenominator (Real.exp (-a)) t)⁻¹ else L i t
  let A := (N:ℝ)*simpleKernelConstant*(1+|Real.log a|)
  have hmeasure : volume.restrict (angularOnePhaseBox p)=
      Measure.pi (fun i => volume.restrict (Icc 0 (h i))) := by
    rw [angularOnePhaseBox,← Set.pi_univ_Icc,volume_pi,Measure.restrict_pi_pi]
  change (∫ θ in angularOnePhaseBox p,∏ i,w i (θ i))≤_
  rw [hmeasure,integral_fintype_prod_eq_prod]
  have hphase : (∫ t in Icc 0 ((N:ℝ)*(2*Real.pi)),(phaseDenominator (Real.exp (-a)) t)⁻¹)≤A := by
    have hh := simple_kernel_interval_integral ha ha1 N (show 0≤(N:ℝ)*(2*Real.pi) by positivity)
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
        · exact inv_nonneg.mpr (norm_nonneg _)
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

theorem angularOnePhaseMap_image {N : ℕ} (p : Fin N) :
    onePhaseSumMap p 0 '' angleBox N⊆angularOnePhaseBox p := by
  rintro _ ⟨θ,hθ,rfl⟩
  have hlo : 0≤∑ i,θ i := Finset.sum_nonneg (fun i _ => hθ.1 i)
  have hhi : (∑ i,θ i)≤(N:ℝ)*(2*Real.pi) := by
    simpa using Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => hθ.2 i)
  constructor <;> intro i
  all_goals
    by_cases hip : i=p
    · first | simpa [angularOnePhaseBox,onePhaseSumMap,hip] using hlo
            | simpa [angularOnePhaseBox,onePhaseSumMap,hip] using hhi
    · first | simpa [angularOnePhaseBox,onePhaseSumMap,hip] using hθ.1 i
            | simpa [angularOnePhaseBox,onePhaseSumMap,hip] using hθ.2 i

/-- The complete angular box admits the actual sum-phase integration,
with every other coordinate carrying its own scalar integrable weight. -/
theorem angular_one_phase_weighted_integral {N : ℕ} (p q : Fin N) (hpq : p≠q)
    (L : Fin N → ℝ → ℝ) (C : Fin N → ℝ) (hL0 : ∀ i t,0≤L i t)
    {a : ℝ} (ha : 0<a) (ha1 : a≤1)
    (hL : ∀ i,ContinuousOn (L i) (Icc 0 (2*Real.pi)))
    (hLint : ∀ i,(∫ t in Icc 0 (2*Real.pi),L i t)≤C i) :
    let f := fun θ : Fin N → ℝ => (phaseDenominator (Real.exp (-a)) (∑ i,θ i))⁻¹*
      ∏ i∈Finset.univ.erase p,L i (θ i)
    IntegrableOn f (angleBox N) ∧ (∫ θ in angleBox N,f θ)≤
      ((N:ℝ)*simpleKernelConstant*(1+|Real.log a|))*(∏ i∈Finset.univ.erase p,C i) := by
  have hk := angular_one_phase_product_integral p L C hL0 ha ha1 hL hLint
  have hh := injective_coordinate_weighted_coarea_on (S := angleBox N) measurableSet_Icc
    (onePhaseSumMap p 0) (fun _ => onePhaseSumDerivative p)
    (fun θ _ => (onePhaseSum_hasFDerivAt p 0 θ).hasFDerivWithinAt)
    (onePhaseSum_injective p 0).injOn (angularOnePhaseMap_image p)
    (fun _ => 1) (onePhaseSpectatorKernel p a L) continuousOn_const
    (angularOnePhaseKernel_continuousOn p ha L hL)
    (onePhaseSpectatorKernel_nonneg p a L hL0) hk.1 (C := 1) zero_le_one
    (fun _ _ => zero_le_one) (fun _ _ => by rw [onePhaseSum_det p q hpq]; norm_num)
  simp only [one_mul,onePhaseSum_kernel_eq,mul_zero,sub_zero] at hh
  exact ⟨hh.1,hh.2.trans hk.2⟩

end
end IsingBulk.Tail
