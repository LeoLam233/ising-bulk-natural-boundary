import IsingBulk.Anisotropic.FormFactors.RealResponseSqueeze
import Mathlib.Analysis.Convex.Deriv

namespace IsingBulk.Anisotropic.PhysicalField
noncomputable section
open Set Filter
open scoped Topology

/-- The finite-volume GHS concavity bound passes through the thermodynamic
limit. No uniform-field differentiability of the infinite state is assumed. -/
theorem thermodynamic_secant_bound (m : ℝ → ℝ) (finiteM : ℕ → ℝ → ℝ)
    (d : ℕ → ℝ) (L : ℝ)
    (hc : ∀ n, ConcaveOn ℝ (Ici 0) (finiteM n))
    (hd : ∀ n, HasDerivAt (finiteM n) (d n) 0)
    (hbound : ∀ n, d n≤L)
    (hlim : ∀ h, 0≤h → Tendsto (fun n => finiteM n h) atTop (𝓝 (m h))) :
    ∀ h, 0<h → m h-m 0≤L*h := by
  intro h hh
  apply le_of_tendsto ((hlim h hh.le).sub (hlim 0 le_rfl))
  filter_upwards [] with n
  have hs := (hc n).slope_le_of_hasDerivAt (by simp : (0:ℝ)∈Ici 0) hh.le hh (hd n)
  simp only [slope_def_field,sub_zero] at hs
  exact ((div_le_iff₀ hh).mp hs).trans (mul_le_mul_of_nonneg_right (hbound n) hh.le)

/-- Exact right response from finite local tilts and finite-volume concavity.
The thermodynamic and field limits are not interchanged. -/
theorem thermodynamic_uniform_field_derivative (m : ℝ → ℝ)
    (localM finiteM : ℕ → ℝ → ℝ) (localD finiteD : ℕ → ℝ) (L : ℝ)
    (hzero : ∀ n, localM n 0=m 0)
    (hlower : ∀ n h, 0<h → localM n h≤m h)
    (hlocal : ∀ n, HasDerivAt (localM n) (localD n) 0)
    (hlocalLimit : Tendsto localD atTop (𝓝 L))
    (hconcave : ∀ n, ConcaveOn ℝ (Ici 0) (finiteM n))
    (hfinite : ∀ n, HasDerivAt (finiteM n) (finiteD n) 0)
    (hbound : ∀ n, finiteD n≤L)
    (hlim : ∀ h, 0≤h → Tendsto (fun n => finiteM n h) atTop (𝓝 (m h))) :
    HasDerivWithinAt m L (Ioi 0) 0 :=
  FormFactors.uniform_field_right_derivative m localM localD L hzero hlower hlocal hlocalLimit
    (thermodynamic_secant_bound m finiteM finiteD L hconcave hfinite hbound hlim)

end
end IsingBulk.Anisotropic.PhysicalField
