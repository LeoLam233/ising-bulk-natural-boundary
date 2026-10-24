import IsingBulk.Anisotropic.NegativeDominance.ActualHigherWinding

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open Filter
open scoped Topology

/-- Explicit exponential suppression after the quadratic scalar loss. -/
theorem higher_winding_envelope_decay (C : ℝ) (N j : ℕ) (hj : 8≤j)
    (hsize : C*(N : ℝ)^2≤(j : ℝ)*Real.log 2/8) :
    Real.exp (C*(N : ℝ)^2)*(1/2 : ℝ)^(j/2)≤Real.exp (-(j : ℝ)*Real.log 2/4) := by
  have hhalf : (j : ℝ)≤2*((j/2 : ℕ) : ℝ)+1 := by exact_mod_cast (show j≤2*(j/2)+1 by omega)
  have hjR : (8 : ℝ)≤j := by exact_mod_cast hj
  have hl : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
  have hh := mul_le_mul_of_nonneg_right hhalf hl
  have h8 := mul_le_mul_of_nonneg_right hjR hl
  apply (Real.log_le_iff_le_exp (by positivity)).mp
  rw [Real.log_mul (Real.exp_ne_zero _) (by positivity),Real.log_exp,Real.log_pow]
  have hlog : Real.log (1/2 : ℝ)= -Real.log 2 := by rw [one_div,Real.log_inv]
  rw [hlog]
  nlinarith only [hsize,hh,h8,hl]

/-- The genuine governing middle cutoff makes the higher-winding suppression
uniform in every index, including the top of the middle range. -/
theorem eventually_higher_winding_middle (C : ℝ) (_hC : 0<C) :
    ∀ᶠ j : ℕ in atTop,∀N : ℕ,
      (N : ℝ)^2≤(j : ℝ)/Real.sqrt (Real.log j) →
      4*alpha N≤j ∧ Real.exp (C*(N : ℝ)^2)*(1/2 : ℝ)^(j/2)≤
        Real.exp (-(j : ℝ)*Real.log 2/4) := by
  have hs : Tendsto (fun j : ℕ=>Real.sqrt (Real.log j)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hl : 0<Real.log 2 := Real.log_pos (by norm_num)
  filter_upwards [hs.eventually_ge_atTop (max 4 (8*C/Real.log 2)),eventually_ge_atTop (8 : ℕ)]
    with j hjS hj
  intro N hcut
  have hS4 : 4≤Real.sqrt (Real.log j) := (le_max_left _ _).trans hjS
  have hSC : 8*C/Real.log 2≤Real.sqrt (Real.log j) := (le_max_right _ _).trans hjS
  have hSp : 0<Real.sqrt (Real.log j) := by linarith
  have hcut' := (le_div_iff₀ hSp).mp hcut
  have haNat : alpha N≤N*N := (Nat.div_le_self _ _).trans (Nat.sub_le _ _)
  have ha : (alpha N : ℝ)≤(N : ℝ)^2 := by exact_mod_cast (show alpha N≤N^2 by simpa only [pow_two] using haNat)
  have hfour := mul_le_mul_of_nonneg_left hS4 (sq_nonneg (N : ℝ))
  have haj : (4 : ℝ)*alpha N≤j := by nlinarith only [ha,hfour,hcut']
  refine ⟨by exact_mod_cast haj,higher_winding_envelope_decay C N j hj ?_⟩
  have hc := mul_le_mul_of_nonneg_left ((div_le_iff₀ hl).mp hSC) (sq_nonneg (N : ℝ))
  have hj' := mul_le_mul_of_nonneg_right hcut' hl.le
  nlinarith only [hc,hj']

end
end IsingBulk.Anisotropic.NegativeDominance
