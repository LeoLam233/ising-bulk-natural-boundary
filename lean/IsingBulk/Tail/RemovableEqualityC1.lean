import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Tactic

namespace IsingBulk.Tail
noncomputable section
open Set Filter Asymptotics Metric
open scoped Topology
variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Quadratic vanishing proves the actual derivative zero on the equality set. -/
lemma equality_quadratic_hasFDerivAt_zero (f : E → G) (d : E → ℝ)
    {U Z : Set E} (hU : IsOpen U) (C : ℝ) (hC : 0 ≤ C)
    (hzero : ∀ x ∈ U ∩ Z, f x=0)
    (hd0 : ∀ x ∈ U, 0 ≤ d x)
    (hquad : ∀ x ∈ U \ Z, ‖f x‖ ≤ C*(d x)^2)
    (hdist : ∀ a ∈ U ∩ Z, ∀ x ∈ U, d x ≤ 2*‖x-a‖)
    {a : E} (ha : a ∈ U ∩ Z) : HasFDerivAt f (0 : E →L[ℝ] G) a := by
  rw [hasFDerivAt_iff_isLittleO]
  apply Asymptotics.isLittleO_iff.mpr
  intro c hc
  have hden : 0 < 4*C+1 := by positivity
  have hrad : 0 < c/(4*C+1) := div_pos hc hden
  filter_upwards [hU.mem_nhds ha.1,ball_mem_nhds a hrad] with x hx hball
  simp only [hzero a ha,sub_zero,zero_apply]
  have hnorm : ‖x-a‖ < c/(4*C+1) := by simpa only [mem_ball,dist_eq_norm] using hball
  by_cases hz : x ∈ Z
  · rw [hzero x ⟨hx,hz⟩,norm_zero]
    positivity
  · have hf := hquad x ⟨hx,hz⟩
    have hd := hdist a ha x hx
    have hdsq : (d x)^2 ≤ (2*‖x-a‖)^2 := pow_le_pow_left₀ (hd0 x hx) hd 2
    have hc1 : (4*C+1)*‖x-a‖ ≤ c := by
      have hh := (lt_div_iff₀ hden).mp hnorm
      nlinarith
    have hmul := mul_le_mul_of_nonneg_left hdsq hC
    have hfinal := mul_le_mul_of_nonneg_right hc1 (norm_nonneg (x-a))
    nlinarith [norm_nonneg (x-a)]

/-- C1 removal across a closed equality set from actual quadratic function
and linear derivative bounds. No flux cancellation is a premise. -/
theorem removable_equality_C1 (f : E → G) (d : E → ℝ)
    {U Z : Set E} (hU : IsOpen U) (_hZ : IsClosed Z) (C : ℝ) (hC : 0 ≤ C)
    (hzero : ∀ x ∈ U ∩ Z, f x=0)
    (hd : ContinuousOn d U) (hd0 : ∀ x ∈ U, 0 ≤ d x)
    (hdzero : ∀ x ∈ U ∩ Z, d x=0)
    (hreg : ∀ x ∈ U \ Z, ContDiffAt ℝ 1 f x)
    (hquad : ∀ x ∈ U \ Z, ‖f x‖ ≤ C*(d x)^2)
    (hlinear : ∀ x ∈ U \ Z, ‖fderiv ℝ f x‖ ≤ C*d x)
    (hdist : ∀ a ∈ U ∩ Z, ∀ x ∈ U, d x ≤ 2*‖x-a‖) :
    (∀ a ∈ U ∩ Z, HasFDerivAt f (0 : E →L[ℝ] G) a) ∧
      ContinuousOn (fderiv ℝ f) U ∧ ∀ a ∈ U, ContDiffAt ℝ 1 f a := by
  have hder0 : ∀ a ∈ U ∩ Z, HasFDerivAt f (0 : E →L[ℝ] G) a :=
    fun a ha => equality_quadratic_hasFDerivAt_zero f d hU C hC hzero hd0 hquad hdist ha
  have hder : ∀ a ∈ U, HasFDerivAt f (fderiv ℝ f a) a := by
    intro a ha
    by_cases hz : a ∈ Z
    · have hh := hder0 a ⟨ha,hz⟩
      rw [hh.fderiv]
      exact hh
    · exact ((hreg a ⟨ha,hz⟩).differentiableAt (by norm_num)).hasFDerivAt
  have hbound : ∀ x ∈ U, ‖fderiv ℝ f x‖ ≤ C*d x := by
    intro x hx
    by_cases hz : x ∈ Z
    · rw [(hder0 x ⟨hx,hz⟩).fderiv,norm_zero]
      exact mul_nonneg hC (hd0 x hx)
    · exact hlinear x ⟨hx,hz⟩
  have hc : ∀ a ∈ U, ContinuousAt (fderiv ℝ f) a := by
    intro a ha
    by_cases hz : a ∈ Z
    · have hda : ContinuousAt d a := (hd a ha).continuousAt (hU.mem_nhds ha)
      have hlim : Tendsto (fun x => C*d x) (𝓝 a) (𝓝 0) := by
        simpa only [hdzero a ⟨ha,hz⟩,mul_zero] using hda.tendsto.const_mul C
      have hn : Tendsto (fun x => ‖fderiv ℝ f x‖) (𝓝 a) (𝓝 0) :=
        squeeze_zero' (Filter.Eventually.of_forall (fun x => norm_nonneg _))
          ((show ∀ᶠ x in 𝓝 a, x ∈ U from hU.mem_nhds ha).mono (fun x hx => hbound x hx)) hlim
      change Tendsto (fderiv ℝ f) (𝓝 a) (𝓝 (fderiv ℝ f a))
      rw [(hder0 a ⟨ha,hz⟩).fderiv]
      exact tendsto_zero_iff_norm_tendsto_zero.mpr hn
    · exact (hreg a ⟨ha,hz⟩).continuousAt_fderiv (by norm_num)
  have hcU : ContinuousOn (fderiv ℝ f) U := fun a ha => (hc a ha).continuousWithinAt
  refine ⟨hder0,hcU,?_⟩
  intro a ha
  exact contDiffAt_one_iff.mpr ⟨fderiv ℝ f,U,hU.mem_nhds ha,hcU,hder⟩

end
end IsingBulk.Tail
