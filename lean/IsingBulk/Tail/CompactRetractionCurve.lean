import IsingBulk.Tail.CompactRetractionJets
import IsingBulk.Tail.CompactSecondDerivative

/-! Actual affine angular rays retain dimension-uniform first and second
coupled radial velocities. Occupancy is differentiated as a sum on the ray. -/
namespace IsingBulk.Tail
noncomputable section
open scoped ContDiff BigOperators
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

def radialRayExponent {N : ℕ} (f : SelectorFunctions) (c₀ eps τ lam : ℝ)
    (θ omegaVec : Fin N → ℝ) (i : Fin N) (t : ℝ) : ℝ :=
  coupledRadialExponent c₀ eps τ lam (f.p ((θ+t • omegaVec) i)) (f.m ((θ+t • omegaVec) i))
    (occupancy (fun l => f.p ((θ+t • omegaVec) l))/(N:ℝ))

theorem affine_angular_ray_hasDerivAt {N : ℕ} (θ omegaVec : Fin N → ℝ) (t : ℝ) :
    HasDerivAt (fun u : ℝ => θ+u • omegaVec) omegaVec t := by
  simpa using ((hasDerivAt_id t).smul_const omegaVec).const_add θ

theorem retraction_ray_derivative_bounds (f : SelectorFunctions)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m)
    (hpper : Function.Periodic f.p (2*Real.pi)) (hmper : Function.Periodic f.m (2*Real.pi)) :
    ∃ C : ℝ, 0<C ∧ ∀ (N : ℕ), 0<N → ∀ (c₀ eps τ lam : ℝ)
      (θ omegaVec : Fin N → ℝ) (i : Fin N) (t : ℝ), 0≤τ → 0≤lam → ‖omegaVec‖≤1 →
      |deriv (radialRayExponent f c₀ eps τ lam θ omegaVec i) t|≤C*τ*lam ∧
      |deriv (deriv (radialRayExponent f c₀ eps τ lam θ omegaVec i)) t|≤C*τ*lam := by
  obtain ⟨C₁,hC₁,hfirst⟩ := periodic_retraction_jet_bound f.p f.m hp hm hpper hmper 1
  obtain ⟨C₂,hC₂,hsecond⟩ := periodic_retraction_jet_bound f.p f.m hp hm hpper hmper 2
  refine ⟨max C₁ C₂,lt_of_lt_of_le hC₁ (le_max_left _ _),?_⟩
  intro N hN c₀ eps τ lam θ omegaVec i t hτ hlam homegaVec
  let H := normalizedRetractionShift N f.p f.m i
  let line := fun u : ℝ => θ+u • omegaVec
  have hH : ContDiff ℝ ∞ H := normalizedRetractionShift_smooth N f.p f.m hp hm i
  have hline : ContDiff ℝ ∞ line := by dsimp [line]; fun_prop
  have hld : deriv line=(fun _ => omegaVec) := funext (fun u => (affine_angular_ray_hasDerivAt θ omegaVec u).deriv)
  have hld2 : deriv (deriv line) t=0 := by rw [hld]; simp
  have hdH : deriv (fun u => H (line u)) t=fderiv ℝ H (line t) omegaVec :=
    ((hH.differentiable (by simp) (line t)).hasFDerivAt.comp_hasDerivAt t
      (affine_angular_ray_hasDerivAt θ omegaVec t)).deriv
  have hn1 : ‖deriv (fun u => H (line u)) t‖≤C₁ := by
    rw [hdH]
    have hj := hfirst N hN i (line t)
    rw [norm_iteratedFDeriv_one] at hj
    exact ((fderiv ℝ H (line t)).le_opNorm omegaVec).trans
      ((mul_le_mul_of_nonneg_right hj (norm_nonneg _)).trans (mul_le_of_le_one_right hC₁.le homegaVec))
  have hd2 := second_derivative_comp_curve (f := H) (p := line) (x := t)
    ((hH.of_le (by simp : (2:ℕ∞ω)≤∞)).contDiffAt)
    ((hline.of_le (by simp : (2:ℕ∞ω)≤∞)).contDiffAt)
  rw [hld2,hld,map_zero,add_zero] at hd2
  have hn2 : ‖deriv (deriv (fun u => H (line u))) t‖≤C₂ := by
    rw [hd2]
    have hh := (iteratedFDeriv ℝ 2 H (line t)).le_opNorm (fun _ => omegaVec)
    simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] at hh
    have hpow : ‖omegaVec‖^2≤1 := pow_le_one₀ (norm_nonneg _) homegaVec
    exact hh.trans ((mul_le_mul_of_nonneg_right (hsecond N hN i (line t)) (by positivity)).trans
      (mul_le_of_le_one_right hC₂.le hpow))
  have he : radialRayExponent f c₀ eps τ lam θ omegaVec i=(fun u => (-c₀*eps)+(lam*τ)*H (line u)) := by
    funext u
    dsimp [radialRayExponent,coupledRadialExponent,H,line,normalizedRetractionShift,normalizedAngularOccupancy,occupancy]
  have hA : 0≤lam*τ := mul_nonneg hlam hτ
  constructor
  · rw [he,deriv_const_add,deriv_const_mul_field,abs_mul,abs_of_nonneg hA]
    have hh := mul_le_mul_of_nonneg_left (show |deriv (fun u => H (line u)) t|≤C₁ by simpa [Real.norm_eq_abs] using hn1) hA
    have hc := mul_le_mul_of_nonneg_left (le_max_left C₁ C₂) hA
    nlinarith
  · rw [he,deriv_const_add',deriv_const_mul_field',deriv_const_mul_field,abs_mul,abs_of_nonneg hA]
    have hh := mul_le_mul_of_nonneg_left (show |deriv (deriv (fun u => H (line u))) t|≤C₂ by simpa [Real.norm_eq_abs] using hn2) hA
    have hc := mul_le_mul_of_nonneg_left (le_max_right C₁ C₂) hA
    nlinarith

end
end IsingBulk.Tail
