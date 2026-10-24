import IsingBulk.Anisotropic.NegativeDominance.ResonantMiddleIndices
import IsingBulk.Anisotropic.NegativeDominance.ZeroRadius

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open Filter
open scoped Topology

/-- The actual resonant progression is unbounded, and the single selected
integer orders force zero radius through their explicit supergeometric bound. -/
theorem radius_zero_of_resonant_selected_growth (coeff : ℕ→ℂ) {p : ℕ} (hp : 0<p)
    (K : ℝ) (N : ℕ)
    (hg : ∀ell : ℕ,N≤resonantParticle p ell → ∃j : ℕ,resonantParticle p ell≤j ∧
      Real.exp ((j : ℝ)*(2*Real.log (resonantParticle p ell)-K))/2≤‖coeff j‖) :
    (FormalMultilinearSeries.ofScalars ℂ coeff).radius=0 := by
  apply scalar_radius_eq_zero_of_unbounded
  intro r hr C
  have ht : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨Nlog,hNlog⟩ := eventually_atTop.mp (ht.eventually (eventually_ge_atTop ((K-Real.log r+1)/2)))
  obtain ⟨Nc,hNc⟩ := exists_nat_gt (2*C)
  let ell := max N (max Nlog Nc)
  let n := resonantParticle p ell
  have hnell : ell≤n := resonant_index_le_particle hp ell
  have hnN : N≤n := (le_max_left _ _).trans hnell
  have hnlog : Nlog≤n := (le_max_left _ _).trans ((le_max_right _ _).trans hnell)
  have hnC : Nc≤n := (le_max_right _ _).trans ((le_max_right _ _).trans hnell)
  obtain ⟨j,hnj,hbound⟩ := hg ell hnN
  refine ⟨j,?_⟩
  have hrate : 1≤2*Real.log (n : ℝ)-K+Real.log r := by linarith [hNlog n hnlog]
  have hj0 : (0 : ℝ)≤j := Nat.cast_nonneg j
  have hmul := mul_le_mul_of_nonneg_left hrate hj0
  have hp : r^j=Real.exp ((j : ℝ)*Real.log r) := by rw [Real.exp_nat_mul,Real.exp_log hr]
  have hcombine : Real.exp ((j : ℝ)*(2*Real.log (n : ℝ)-K))/2*r^j=
      Real.exp ((j : ℝ)*(2*Real.log (n : ℝ)-K+Real.log r))/2 := by
    rw [hp,div_mul_eq_mul_div,←Real.exp_add]
    congr 1
    congr 1
    ring
  have hscaled : Real.exp (j : ℝ)/2≤‖coeff j‖*r^j := by
    calc
      _ ≤ Real.exp ((j : ℝ)*(2*Real.log (n : ℝ)-K+Real.log r))/2 := by
        gcongr
        simpa only [mul_one] using hmul
      _ = Real.exp ((j : ℝ)*(2*Real.log (n : ℝ)-K))/2*r^j := hcombine.symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hbound (pow_nonneg hr.le _)
  have hjC : 2*C<(j : ℝ) := by exact_mod_cast (hNc.trans_le (by exact_mod_cast hnC.trans hnj))
  have hexp := Real.add_one_le_exp (j : ℝ)
  linarith

end
end IsingBulk.Anisotropic.NegativeDominance
