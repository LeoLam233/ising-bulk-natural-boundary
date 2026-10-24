import IsingBulk.Anisotropic.NegativeDominance.BallMassEntropy
import IsingBulk.Anisotropic.NegativeNormalForm.Vandermonde

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open IsingBulk.First IsingBulk.Anisotropic.NegativeNormalForm MeasureTheory Set
open scoped BigOperators

theorem norm_vandermonde_real_sq {n : ℕ} (v : Fin n→ℝ) :
    ‖vandermonde (fun i => (v i : ℂ))‖^2=firstVandermonde v^2 := by
  have he : vandermonde (fun i => (v i : ℂ))=(firstVandermonde v : ℂ) := by
    simp [vandermonde,firstVandermonde]
  rw [he,Complex.norm_real,Real.norm_eq_abs,sq_abs]

/-- Integrating the genuine Vandermonde envelope on any portion of the actual
constrained ball preserves its superexponential dimension suppression. -/
theorem norm_integral_vandermonde_ball_bound {n : ℕ} (hn : 1≤n)
    (S : Set (Fin n→ℝ)) (hS : S⊆constrainedEnergyBall n)
    (f : (Fin n→ℝ)→ℂ) (K : ℝ) (hK : 0≤K)
    (hf : ∀x∈S,‖f x‖≤K*‖vandermonde (fun i => ((shapeExtend x i : ℝ) : ℂ))‖^2) :
    ‖∫x in S,f x‖≤K*Real.exp (-((n+1 : ℝ)^2)/2*Real.log (n+1)+10*(n+1 : ℝ)^2) := by
  have hbox := hS.trans (constrainedEnergyBall_subset_box n)
  have hfin : volume S<⊤ := (measure_mono hbox).trans_lt isCompact_Icc.measure_lt_top
  have hm : volume.real S≤2^n := by
    simpa only [constrained_box_volume] using
      measureReal_mono (μ := volume) hbox isCompact_Icc.measure_lt_top.ne
  have hb := norm_setIntegral_le_of_norm_le_const hfin
    (C := K*(16/((n+1 : ℕ) : ℝ))^((n+1).choose 2)) (f := f) (by
      intro x hx
      have hfx := hf x hx
      rw [norm_vandermonde_real_sq] at hfx
      exact hfx.trans (mul_le_mul_of_nonneg_left
        (vandermonde_sq_energy_ball (by omega) (shapeExtend x) (hS hx)) hK))
  calc
    _ ≤ K*(16/((n+1 : ℕ) : ℝ))^((n+1).choose 2)*volume.real S := hb
    _ ≤ K*(16/((n+1 : ℕ) : ℝ))^((n+1).choose 2)*2^n := by gcongr
    _ = K*(2^((n+1)-1)*(16/((n+1 : ℕ) : ℝ))^((n+1).choose 2)) := by simp; ring
    _ ≤ _ := by
      have he := mul_le_mul_of_nonneg_left (ball_mass_envelope_entropy (n+1) (by omega)) hK
      simpa only [Nat.cast_add,Nat.cast_one] using he

end
end IsingBulk.Anisotropic.NegativeDominance
