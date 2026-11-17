import IsingBulk.AnisoF002.C03.IsotropicRadialDifferential

/-!
# Identifying integrated currents with the original complex derivatives

A holomorphic original coefficient and a nondegenerate real radial
path determine every integrated current uniquely. The proof uses the
actual neighborhood derivative identities successively; it never
treats a previously differentiated coefficient as fixed.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set Filter
open scoped Topology

theorem radial_current_identifies_iteratedDeriv (f : ℂ → ℂ)
    (I : ℕ → ℝ → ℂ) (p p' : ℝ → ℂ) (U : Set ℝ) (hU : IsOpen U) (J : ℕ)
    (hf : ∀ t ∈ U, AnalyticAt ℂ f (p t))
    (hp : ∀ t ∈ U, HasDerivAt p (p' t) t)
    (hp' : ∀ t ∈ U, p' t ≠ 0)
    (hzero : ∀ t ∈ U, I 0 t = f (p t))
    (hstep : ∀ k : ℕ, k < J → ∀ t ∈ U,
      HasDerivAt (I k) (p' t * I (k + 1) t) t) :
    ∀ k : ℕ, k ≤ J → ∀ t ∈ U, I k t = iteratedDeriv k f (p t) := by
  intro k hk
  induction k with
  | zero =>
      intro t ht
      simpa only [iteratedDeriv_zero] using hzero t ht
  | succ k ih =>
      intro t ht
      have hkJ : k < J := by omega
      have ih' := ih (by omega)
      have ha : AnalyticAt ℂ (iteratedDeriv k f) (p t) := by
        simpa only [iteratedDeriv_eq_iterate] using (hf t ht).iterated_deriv k
      have hcurve : HasDerivAt (fun u => iteratedDeriv k f (p u))
          (p' t * iteratedDeriv (k + 1) f (p t)) t := by
        simpa only [Function.comp_def, smul_eq_mul, iteratedDeriv_succ] using
          ha.differentiableAt.hasDerivAt.scomp t (hp t ht)
      have he : I k =ᶠ[𝓝 t] (fun u => iteratedDeriv k f (p u)) := by
        filter_upwards [hU.mem_nhds ht] with u hu
        exact ih' u hu
      exact mul_left_cancel₀ (hp' t ht) ((hstep k hkJ t ht).unique
        (hcurve.congr_of_eventuallyEq he))

end
end IsingBulk.AnisoF002.Isotropic
