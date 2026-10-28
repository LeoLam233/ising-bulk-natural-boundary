import IsingBulk.HT22.First.LocalLimit.OneParticle
import IsingBulk.HT22.Arithmetic.BranchCharts
namespace IsingBulk.HT22.Finite
noncomputable section
open IsingBulk.Preferred22 Complex Filter
open scoped Topology

theorem branch_root_ne_constraintSign (d : PreferredBranchData) (negative : Bool) :
    exp ((d.alpha:ℂ)*I)≠Physical.constraintSign negative := by
  have hs : 0<Real.sin d.alpha := Real.sin_pos_of_pos_of_lt_pi d.alpha_pos
    (by linarith [d.alpha_lt,Real.pi_pos])
  intro hh
  have hi := congrArg Complex.im hh
  have hsign : (Physical.constraintSign negative).im=0 := by
    cases negative <;> simp [Physical.constraintSign]
  rw [hsign] at hi
  simp [Complex.exp_mul_I,←Complex.ofReal_cos,←Complex.ofReal_sin] at hi
  linarith

theorem one_particle_bound (d : PreferredBranchData) (negative : Bool) (j : ℕ) :
    ∃ C ε₀ : ℝ,0<C ∧ 0<ε₀ ∧ ∀ ε : ℝ,0<ε → ε<ε₀ →
    ‖iteratedDeriv j (Physical.signedCoefficient negative 1)
      (IsingBulk.Branch.radialParameter d.alpha ε)‖≤C*(1+|Real.log ε|) := by
  simpa only [iteratedDeriv_eq_iterate] using
    LocalLimit.oneParticle_radial_derivative_bound negative d.alpha (branch_root_ne_constraintSign d negative) j

theorem one_particle_limit (d : PreferredBranchData) (negative : Bool) (j : ℕ) :
    Tendsto (fun ε : ℝ => ε • iteratedDeriv j (Physical.signedCoefficient negative 1)
      (IsingBulk.Branch.radialParameter d.alpha ε)) (𝓝[>] 0) (𝓝 (0:ℂ)) := by
  simpa only [iteratedDeriv_eq_iterate] using
    LocalLimit.oneParticle_radial_derivative_limit negative d.alpha (branch_root_ne_constraintSign d negative) j
end
end IsingBulk.HT22.Finite
