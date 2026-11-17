import IsingBulk.AnisoF002.C03.RegularCollisionBlowup

/-!
# Exact second divided differences for the isotropic first chart

The analytic filling keeps the original function and its linear term.
Its central value is derived by differentiating the exact identity, so
the quadratic coefficient is not supplied as an additional premise.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Filter IsingBulk.AnisoF002.RegularTail.C03
open scoped Topology

def isotropicSecondFill (f : ℂ → ℂ) (a : ℂ) : ℂ → ℂ :=
  dslope (dslope f a) a

theorem isotropicSecondFill_analytic {f : ℂ → ℂ} {a : ℂ}
    (hf : AnalyticAt ℂ f a) : AnalyticAt ℂ (isotropicSecondFill f a) a :=
  analyticAt_dslope_center (analyticAt_dslope_center hf)

theorem isotropicSecondFill_exact (f : ℂ → ℂ) (a z : ℂ) :
    f z = f a + (z - a) * deriv f a + (z - a) ^ 2 * isotropicSecondFill f a z := by
  have h1 := sub_smul_dslope f a z
  have h2 := sub_smul_dslope (dslope f a) a z
  simp only [smul_eq_mul, dslope_same] at h1 h2
  change (z - a) * isotropicSecondFill f a z = dslope f a z - deriv f a at h2
  linear_combination -h1 - (z - a) * h2

theorem deriv_dslope_at_analytic_center {f : ℂ → ℂ} {a : ℂ}
    (hf : AnalyticAt ℂ f a) : deriv (dslope f a) a = deriv (deriv f) a / 2 := by
  let D : ℂ → ℂ := dslope f a
  have hD : AnalyticAt ℂ D a := analyticAt_dslope_center hf
  have hidentity : (fun z => f a + (z - a) * D z) = f := by
    funext z
    have hh := sub_smul_dslope f a z
    simp only [smul_eq_mul] at hh
    dsimp only [D]
    linear_combination hh
  have hfirst : deriv f =ᶠ[𝓝 a] fun z => D z + (z - a) * deriv D z := by
    filter_upwards [hD.eventually_analyticAt] with z hz
    have hd := (hasDerivAt_const z (f a)).add
      (((hasDerivAt_id z).sub_const a).mul hz.differentiableAt.hasDerivAt)
    have hh := hd.deriv
    change deriv (fun w => f a + (w - a) * D w) z =
      0 + (1 * D z + (z - a) * deriv D z) at hh
    rw [hidentity] at hh
    simpa only [sub_self, one_mul, zero_add] using hh
  have hd := hD.differentiableAt.hasDerivAt.add
    (((hasDerivAt_id a).sub_const a).mul hD.deriv.differentiableAt.hasDerivAt)
  change HasDerivAt (fun z => D z + (z - a) * deriv D z)
    (deriv D a + (1 * deriv D a + (a - a) * deriv (deriv D) a)) a at hd
  have hsecond : deriv (deriv f) a = 2 * deriv D a := by
    rw [hfirst.deriv_eq, hd.deriv]
    simp only [sub_self, one_mul, zero_mul, add_zero]
    ring
  change deriv D a = _
  linear_combination -hsecond / 2

theorem isotropicSecondFill_center {f : ℂ → ℂ} {a : ℂ}
    (hf : AnalyticAt ℂ f a) :
    isotropicSecondFill f a a = deriv (deriv f) a / 2 := by
  rw [isotropicSecondFill, dslope_same, deriv_dslope_at_analytic_center hf]

theorem isotropicSecondFill_sin_zero : isotropicSecondFill Complex.sin 0 0 = 0 := by
  rw [isotropicSecondFill_center Complex.analyticAt_sin]
  simp only [Complex.deriv_sin, Complex.deriv_cos, Complex.sin_zero, neg_zero, zero_div]

end
end IsingBulk.AnisoF002.Isotropic
