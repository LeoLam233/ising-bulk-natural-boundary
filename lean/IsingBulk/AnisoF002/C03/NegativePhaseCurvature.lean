import IsingBulk.AnisoF002.C03.NegativePhaseExpansion

/-!
# Exact angular curvature of the actual unsquared dispersion

Both derivatives are forced by the analytic cosh identity.  The second
derivative is obtained by differentiating that identity twice, including
the derivative of the phase itself.  No quadratic surrogate is assumed.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Filter
open scoped Topology

theorem cosh_dispersion_first_derivative {f : ℂ → ℂ} {a b d : ℂ}
    (hf : DifferentiableAt ℂ f d)
    (he : (fun x => Complex.cosh (f x)) =ᶠ[𝓝 d] (fun x => a + b * Complex.cos x)) :
    Complex.sinh (f d) * deriv f d = -b * Complex.sin d := by
  have hr : HasDerivAt (fun x : ℂ => a + b * Complex.cos x) (-b * Complex.sin d) d := by
    convert ((Complex.hasDerivAt_cos d).const_mul b).const_add a using 1
    ring
  exact hf.hasDerivAt.ccosh.unique (hr.congr_of_eventuallyEq he)

theorem cosh_dispersion_second_derivative {f : ℂ → ℂ} {a b d : ℂ}
    (hf : AnalyticAt ℂ f d)
    (he : (fun x => Complex.cosh (f x)) =ᶠ[𝓝 d] (fun x => a + b * Complex.cos x)) :
    Complex.sinh (f d) * deriv (deriv f) d =
      -b * Complex.cos d - Complex.cosh (f d) * (deriv f d) ^ 2 := by
  have hfirst : (fun x => Complex.sinh (f x) * deriv f x) =ᶠ[𝓝 d]
      (fun x => -b * Complex.sin x) := by
    filter_upwards [hf.eventually_analyticAt, he.eventuallyEq_nhds] with x hx heq
    exact cosh_dispersion_first_derivative hx.differentiableAt heq
  have hl := hf.differentiableAt.hasDerivAt.csinh.mul hf.deriv.differentiableAt.hasDerivAt
  have hr : HasDerivAt (fun x : ℂ => -b * Complex.sin x) (-b * Complex.cos d) d := by
    convert (Complex.hasDerivAt_sin d).const_mul (-b) using 1
  have hh := hl.unique (hr.congr_of_eventuallyEq hfirst)
  linear_combination hh

theorem negative_center_angular_curvature (B : ℂ → ℂ) (φ d : ℝ)
    (hφ : Real.sin φ ≠ 0) {g : ℂ × ℂ → ℂ}
    (hga : AnalyticAt ℂ g ((1 - Real.cos d : ℝ), (d : ℂ)))
    (hgv : g ((1 - Real.cos d : ℝ), (d : ℂ)) = (φ : ℂ) * Complex.I)
    (hge : ∀ᶠ a in 𝓝 ((1 - Real.cos d : ℝ), (d : ℂ)),
      Complex.cosh (g a) = localNegativeDispersion B φ a) :
    angularJet 2 g ((1 - Real.cos d : ℝ), (d : ℂ)) =
      Complex.I * B ((1 - Real.cos d : ℝ) : ℂ) / (Real.sin φ : ℂ) *
        ((Real.cos d : ℂ) - B ((1 - Real.cos d : ℝ) : ℂ) * (Real.cos φ : ℂ) /
          (Real.sin φ : ℂ) ^ 2 * (Real.sin d : ℂ) ^ 2) := by
  let τ : ℂ := ((1 - Real.cos d : ℝ) : ℂ)
  let f : ℂ → ℂ := fun δ => g (τ, δ)
  have hf : AnalyticAt ℂ f (d : ℂ) :=
    hga.comp_of_eq (analyticAt_const.prod analyticAt_id) rfl
  have he : (fun δ => Complex.cosh (f δ)) =ᶠ[𝓝 (d : ℂ)]
      (fun δ => ((Real.cos φ : ℂ) + B τ * (τ - 1)) + B τ * Complex.cos δ) := by
    have hm : Tendsto (fun δ : ℂ => (τ, δ)) (𝓝 (d : ℂ)) (𝓝 (τ, (d : ℂ))) :=
      continuousAt_const.prodMk continuousAt_id
    filter_upwards [hm.eventually hge] with δ hδ
    change Complex.cosh (g (τ, δ)) = _
    rw [hδ]
    unfold localNegativeDispersion
    ring
  have hfirst := cosh_dispersion_first_derivative hf.differentiableAt he
  have hsecond := cosh_dispersion_second_derivative hf he
  have hfv : f (d : ℂ) = (φ : ℂ) * Complex.I := hgv
  rw [hfv, Complex.sinh_mul_I, ← Complex.ofReal_sin, ← Complex.ofReal_sin] at hfirst
  rw [hfv, Complex.sinh_mul_I, Complex.cosh_mul_I, ← Complex.ofReal_sin,
    ← Complex.ofReal_cos, ← Complex.ofReal_cos] at hsecond
  have hs : (Real.sin φ : ℂ) ≠ 0 := by exact_mod_cast hφ
  have hsn : (Real.sin φ : ℂ) * Complex.I ≠ 0 := mul_ne_zero hs Complex.I_ne_zero
  have hfd : deriv f (d : ℂ) = -(B τ * (Real.sin d : ℂ)) /
      ((Real.sin φ : ℂ) * Complex.I) := by
    apply (eq_div_iff hsn).mpr
    linear_combination hfirst
  rw [hfd] at hsecond
  simp only [angularJet, iteratedDeriv_succ, iteratedDeriv_zero]
  change deriv (deriv f) (d : ℂ) = _
  apply (mul_left_cancel₀ hsn)
  rw [hsecond]
  dsimp [τ]
  field_simp
  simp only [Complex.I_sq]
  ring_nf
  norm_num

end
end IsingBulk.AnisoF002.NegativeHT
