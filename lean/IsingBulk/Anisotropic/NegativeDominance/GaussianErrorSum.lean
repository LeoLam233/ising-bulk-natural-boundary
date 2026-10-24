import IsingBulk.Anisotropic.NegativeDominance.GaussianMoment
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section

/-- The actual finite winding count costs only a fixed reduction of Gaussian
strength; it does not increase the coefficient of j log N. -/
theorem gaussian_winding_count {a : ℝ} (ha : 0<a) (C : ℝ) (N j : ℕ) :
    ((N : ℝ)+1)*Real.exp (-a*(N : ℝ)^2+((j : ℝ)+1)*Real.log N+C*((j : ℝ)+1))≤
      Real.exp (-(a/2)*(N : ℝ)^2+((j : ℝ)+1)*Real.log N+(C+1/(2*a))*((j : ℝ)+1)) := by
  have hN : (0 : ℝ)≤N := Nat.cast_nonneg N
  have hp : 0<(N : ℝ)+1 := by positivity
  have hl := Real.log_le_sub_one_of_pos hp
  have he : (2*a)*(1/(2*a))=1 := by field_simp
  have hs := sq_nonneg (a*(N : ℝ)-1)
  have hquad : (N : ℝ)≤a/2*(N : ℝ)^2+1/(2*a) := by
    nlinarith only [hs,he,ha]
  have hj : 0≤(1/(2*a))*(j : ℝ) := by positivity
  rw [←Real.exp_log hp,←Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith only [hl,hquad,hj]

/-- Full norm-sum control on any injectively selected particle progression.
This applies to actual resonant, nonresonant, and parity subseries. -/
theorem gaussian_selected_norm_sum {a : ℝ} (ha : 0<a) (C : ℝ)
    {ι : Type*} (idx : ι→ℕ) (hi : Function.Injective idx) :
    ∃D : ℝ,0<D ∧ ∀j : ℕ,∀f : ι→ℂ,
      (∀i,‖f i‖≤Real.exp (-a*(idx i : ℝ)^2+((j : ℝ)+1)*Real.log (idx i)+C*((j : ℝ)+1))) →
      Summable f ∧ Summable (fun i => ‖f i‖) ∧
      (∑' i,‖f i‖)≤D*Real.exp (((j : ℝ)+1)/2*Real.log ((j : ℝ)+2)+(C+|Real.log a|/2)*((j : ℝ)+1)) := by
  obtain ⟨D,hD,hb⟩ := gaussian_log_moment_sum ha C
  refine ⟨D,hD,fun j f hf => ?_⟩
  have hmaj := (hb j).1.comp_injective hi
  have hnorm := hmaj.of_nonneg_of_le (fun i => norm_nonneg (f i)) hf
  refine ⟨hnorm.of_norm,hnorm,?_⟩
  apply (hnorm.tsum_le_tsum hf hmaj).trans
  exact (tsum_comp_le_tsum_of_inj (hb j).1 (fun _ => (Real.exp_pos _).le) hi).trans (hb j).2

end
end IsingBulk.Anisotropic.NegativeDominance
