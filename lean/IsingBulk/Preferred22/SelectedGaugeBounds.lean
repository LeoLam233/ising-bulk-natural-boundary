import IsingBulk.Preferred22.SelectedKernelGeometry
import Mathlib.Analysis.Matrix.Normed

/-! Exact norm identities and pair bounds for the literal physical gauge
kernel. The square-root gauges are handled algebraically; no continuous
choice of their signs is assumed. -/
namespace IsingBulk.Preferred22
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 1000000

lemma preferred_gaugeKernel_norm_sq {N : ℕ} (y z : Fin N → ℂ) (i j : Fin N) :
    ‖gaugeKernel y z i j‖^2=
      (‖z i‖/‖y i‖)*(‖z j‖/‖y j‖)*(‖y i-y j‖/‖1-z i*z j‖)^2 := by
  have hi : ‖Complex.sqrt (z i/y i)‖^2=‖z i‖/‖y i‖ := by
    rw [←norm_pow,complex_sqrt_sq,norm_div]
  have hj : ‖Complex.sqrt (z j/y j)‖^2=‖z j‖/‖y j‖ := by
    rw [←norm_pow,complex_sqrt_sq,norm_div]
  simp only [gaugeKernel,norm_div,norm_mul,norm_neg,Complex.norm_I,one_mul,
    div_pow,mul_pow,hi,hj]
  ring

theorem preferred_gaugeKernel_direct_squared_bound {N : ℕ}
    (y z : Fin N → ℂ) (i j : Fin N) {E : ℝ} (hE : 0≤E)
    (hyi : ‖y i‖≤E) (hyj : ‖y j‖≤E)
    (hyii : ‖(y i)⁻¹‖≤E) (hyji : ‖(y j)⁻¹‖≤E)
    (hzi : ‖z i‖≤1) (hzj : ‖z j‖≤1) :
    ‖gaugeKernel y z i j‖^2≤4*E^4/‖1-z i*z j‖^2 := by
  have hri : ‖z i‖/‖y i‖≤E := by
    rw [div_eq_mul_inv,←norm_inv]
    exact (mul_le_mul hzi hyii (norm_nonneg _) (by norm_num)).trans_eq (one_mul E)
  have hrj : ‖z j‖/‖y j‖≤E := by
    rw [div_eq_mul_inv,←norm_inv]
    exact (mul_le_mul hzj hyji (norm_nonneg _) (by norm_num)).trans_eq (one_mul E)
  have hdiff : ‖y i-y j‖≤2*E := (norm_sub_le _ _).trans (by linarith)
  have hs : ‖y i-y j‖^2≤(2*E)^2 := sq_le_sq₀ (norm_nonneg _) (by positivity) |>.mpr hdiff
  rw [preferred_gaugeKernel_norm_sq,div_pow]
  have hh := mul_le_mul (mul_le_mul hri hrj (by positivity) hE)
    (div_le_div_of_nonneg_right hs (sq_nonneg ‖1-z i*z j‖)) (by positivity) (by positivity : 0≤E*E)
  exact hh.trans_eq (by ring)

theorem preferred_gaugeKernel_swapped_norm_sq {N : ℕ}
    (y z : Fin N → ℂ) (i j : Fin N) (S : ℂ)
    (hyi : y i≠0) (hyj : y j≠0) (hzi : z i≠0) (hzj : z j≠0)
    (hi : y i+(y i)⁻¹+z i+(z i)⁻¹=2*S)
    (hj : y j+(y j)⁻¹+z j+(z j)⁻¹=2*S)
    (hD : 1-z i*z j≠0) (hY : 1-y i*y j≠0) :
    ‖gaugeKernel y z i j‖^2=
      (‖y i‖/‖z i‖)*(‖y j‖/‖z j‖)*(‖z i-z j‖/‖1-y i*y j‖)^2 := by
  have hpair := congrArg (fun x : ℂ => ‖x‖)
    (preferred_pair_reciprocal_identity hyi hyj hzi hzj hi hj hD hY)
  simp only [norm_div,norm_mul,norm_neg] at hpair
  rw [preferred_gaugeKernel_norm_sq,hpair]
  have hyin := norm_ne_zero_iff.mpr hyi
  have hyjn := norm_ne_zero_iff.mpr hyj
  have hzin := norm_ne_zero_iff.mpr hzi
  have hzjn := norm_ne_zero_iff.mpr hzj
  have hYn := norm_ne_zero_iff.mpr hY
  field_simp

theorem preferred_gaugeKernel_same_squared_bound {N : ℕ}
    (y z : Fin N → ℂ) (i j : Fin N) (S : ℂ) {E K : ℝ}
    (hE : 0≤E) (hK : 0≤K)
    (hyi : y i≠0) (hyj : y j≠0) (hzi : z i≠0) (hzj : z j≠0)
    (hi : y i+(y i)⁻¹+z i+(z i)⁻¹=2*S)
    (hj : y j+(y j)⁻¹+z j+(z j)⁻¹=2*S)
    (hD : 1-z i*z j≠0) (hY : 1-y i*y j≠0)
    (hyiE : ‖y i‖≤E) (hyjE : ‖y j‖≤E)
    (hziK : ‖(z i)⁻¹‖≤K) (hzjK : ‖(z j)⁻¹‖≤K)
    (hzi1 : ‖z i‖≤1) (hzj1 : ‖z j‖≤1) :
    ‖gaugeKernel y z i j‖^2≤4*(E*K)^2/‖1-y i*y j‖^2 := by
  have hri : ‖y i‖/‖z i‖≤E*K := by
    rw [div_eq_mul_inv,←norm_inv]
    exact mul_le_mul hyiE hziK (norm_nonneg _) hE
  have hrj : ‖y j‖/‖z j‖≤E*K := by
    rw [div_eq_mul_inv,←norm_inv]
    exact mul_le_mul hyjE hzjK (norm_nonneg _) hE
  have hdiff : ‖z i-z j‖≤2 := (norm_sub_le _ _).trans (by linarith)
  have hs : ‖z i-z j‖^2≤4 := by nlinarith [norm_nonneg (z i-z j)]
  rw [preferred_gaugeKernel_swapped_norm_sq y z i j S hyi hyj hzi hzj hi hj hD hY,div_pow]
  have hh := mul_le_mul (mul_le_mul hri hrj (by positivity) (mul_nonneg hE hK))
    (div_le_div_of_nonneg_right hs (sq_nonneg ‖1-y i*y j‖)) (by positivity)
    (by positivity : 0≤(E*K)*(E*K))
  exact hh.trans_eq (by ring)

end
end IsingBulk.Preferred22
