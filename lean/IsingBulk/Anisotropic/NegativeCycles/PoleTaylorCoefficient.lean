import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

namespace IsingBulk.Anisotropic.NegativeCycles
noncomputable section

theorem pole_normalized_taylor_coefficient (a T : ℂ) (hT : T≠0) (j : ℕ) :
    iteratedDeriv j (fun t : ℂ => a/(T-t)) 0/(j.factorial:ℂ)=a/T^(j+1) := by
  simp only [div_eq_mul_inv,iteratedDeriv_const_mul_field]
  rw [iteratedDeriv_comp_const_sub]
  dsimp only
  rw [smul_eq_mul,sub_zero,iteratedDeriv_eq_iterate,iter_deriv_inv']
  dsimp only
  have hz : (-1-(j:ℤ))=-((j+1:ℕ):ℤ) := by omega
  rw [hz,zpow_neg,zpow_natCast]
  have hsgn : (-1:ℂ)^j*(-1)^j=1 := by rw [←mul_pow]; norm_num
  have hf : (j.factorial:ℂ)≠0 := by exact_mod_cast Nat.factorial_ne_zero j
  field_simp
  linear_combination a*hsgn

open Filter
open scoped Topology

theorem pole_remainder_normalized_taylor {f R : ℂ → ℂ} (a T : ℂ) (hT : T≠0)
    (hR : AnalyticAt ℂ R 0)
    (he : f =ᶠ[𝓝 0] (fun t => a/(T-t)+R t)) (j : ℕ) :
    iteratedDeriv j f 0/(j.factorial:ℂ)=a/T^(j+1)+iteratedDeriv j R 0/(j.factorial:ℂ) := by
  have hp : AnalyticAt ℂ (fun t : ℂ => a/(T-t)) 0 :=
    analyticAt_const.div (analyticAt_const.sub analyticAt_id) (by simpa using hT)
  rw [he.iteratedDeriv_eq j]
  change iteratedDeriv j ((fun t : ℂ => a/(T-t))+R) 0/(j.factorial:ℂ)=_
  rw [iteratedDeriv_add hp.contDiffAt hR.contDiffAt,add_div,
    pole_normalized_taylor_coefficient a T hT j]

end
end IsingBulk.Anisotropic.NegativeCycles
