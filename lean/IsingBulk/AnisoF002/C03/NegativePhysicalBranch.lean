import IsingBulk.AnisoF002.C03.NegativePhysicalChart

/-!
# The local negative-edge phase is the actual small spectral root

The analytic phase is constructed at the endpoint, then identified on the
real inward approach by its positive real part.  This preserves the
physical branch rather than postulating a logarithm of the root.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open IsingBulk.Anisotropic IsingBulk.AnisoF002.Geometry Set Filter
open scoped Topology

theorem abs_cos_lt_one_of_sin_ne_zero {φ : ℝ} (hφ : Real.sin φ ≠ 0) :
    |Real.cos φ| < 1 := by
  apply (sq_lt_one_iff_abs_lt_one (Real.cos φ)).mp
  nlinarith [Real.cos_sq_add_sin_sq φ, sq_pos_of_ne_zero hφ]

theorem exists_negative_physical_phase {lam φ : ℝ} {z : ℂ}
    (hlam : 0 < lam) (hx : z.re ≠ 0) (hφ : Real.sin φ ≠ 0)
    (hinc : spectralA lam z = spectralS z * (Real.cos φ : ℂ) + spectralT lam z * (-1)) :
    ∃ (Z B : ℂ → ℂ) (g : ℂ × ℂ → ℂ),
      AnalyticAt ℂ Z 0 ∧ Z 0 = z ∧ AnalyticAt ℂ B 0 ∧
      B 0 = spectralT lam z / spectralS z ∧ B 0 ≠ 0 ∧
      (∀ t, B t = spectralT lam (Z t) / spectralS (Z t)) ∧
      AnalyticAt ℂ g (0, 0) ∧ g (0, 0) = (φ : ℂ) * Complex.I ∧
      (∀ᶠ a in 𝓝 (0, 0), Complex.cosh (g a) = localNegativeDispersion B φ a) ∧
      (∀ᶠ a in 𝓝 (0, 0), spectralS (Z a.1) ≠ 0 ∧
        Complex.cosh (g a) =
          (spectralA lam (Z a.1) - spectralT lam (Z a.1) *
            Complex.cos ((Real.pi : ℂ) + a.2)) / spectralS (Z a.1)) ∧
      (∀ᶠ t in 𝓝 0, negativeParameterF002 lam (Real.cos φ) (Z t) = t) ∧
      (∀ᶠ w in 𝓝 z, Z (negativeParameterF002 lam (Real.cos φ) w) = w) := by
  obtain ⟨Z, B, hZa, hZ0, hBa, hB0, hBne, hBe, hp, hleft⟩ :=
    exists_negative_physical_chart hlam hx (abs_cos_lt_one_of_sin_ne_zero hφ) hinc
  have hBa0 : AnalyticAt ℂ B (((1 - Real.cos 0 : ℝ)) : ℂ) := by simpa using hBa
  obtain ⟨g, hga, hg0, _, hge⟩ := exists_local_negative_phase B φ 0 hφ hBa0
  have hga' : AnalyticAt ℂ g (0, 0) := by simpa using hga
  have hg0' : g (0, 0) = (φ : ℂ) * Complex.I := by simpa using hg0
  have hge' : ∀ᶠ a in 𝓝 (0, 0), Complex.cosh (g a) = localNegativeDispersion B φ a := by
    simpa using hge
  refine ⟨Z, B, g, hZa, hZ0, hBa, hB0, hBne, hBe, hga', hg0', hge', ?_,
    hp.mono (fun _ h => h.1), hleft⟩
  have hproj : Tendsto (fun a : ℂ × ℂ => a.1) (𝓝 (0, 0)) (𝓝 0) :=
    continuous_fst.continuousAt
  filter_upwards [hge', hproj.eventually hp] with a ha hp'
  refine ⟨hp'.2.1, ?_⟩
  rw [ha, hp'.2.2.2 a.2]
  unfold localNegativeDispersion
  ring

def realPairToComplex (a : ℝ × ℝ) : ℂ × ℂ := ((a.1 : ℂ), (a.2 : ℂ))

theorem continuous_realPairToComplex : Continuous realPairToComplex :=
  (Complex.continuous_ofReal.comp continuous_fst).prodMk
    (Complex.continuous_ofReal.comp continuous_snd)

/-- The actual inward branch has positive real phase.  This conclusion is
uniform on one neighborhood of the two real local variables, before n. -/
theorem negative_phase_re_pos_near_inward {B : ℂ → ℂ} {g : ℂ × ℂ → ℂ} {φ : ℝ}
    (hB : ContinuousAt B 0) (hBim : (B 0).im < 0)
    (hg : ContinuousAt g (0, 0)) (hg0 : g (0, 0) = (φ : ℂ) * Complex.I)
    (hφ0 : 0 < φ) (hφpi : φ < Real.pi)
    (hge : ∀ᶠ a in 𝓝 (0, 0), Complex.cosh (g a) = localNegativeDispersion B φ a) :
    ∀ᶠ a : ℝ × ℝ in 𝓝 (0, 0), a.1 < 0 → 0 < (g (realPairToComplex a)).re := by
  have hc : Tendsto realPairToComplex (𝓝 (0, 0)) (𝓝 (0, 0)) :=
    continuous_realPairToComplex.continuousAt
  have hb : ∀ᶠ t in 𝓝 (0 : ℂ), (B t).im < 0 :=
    (Complex.continuous_im.continuousAt.comp hB).eventually (Iio_mem_nhds hBim)
  have hbt : Tendsto (fun a : ℝ × ℝ => (a.1 : ℂ)) (𝓝 (0, 0)) (𝓝 0) :=
    (Complex.continuous_ofReal.comp continuous_fst).continuousAt
  have hbp : ∀ᶠ a : ℝ × ℝ in 𝓝 (0, 0), (B (a.1 : ℂ)).im < 0 :=
    hbt.eventually hb
  have hsin0 : 0 < Real.sin (g (0, 0)).im := by
    simpa only [hg0, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_im, Complex.I_re, mul_one, zero_mul, add_zero] using
      Real.sin_pos_of_pos_of_lt_pi hφ0 hφpi
  have hsin : ∀ᶠ a in 𝓝 (0, 0), 0 < Real.sin (g a).im :=
    (Real.continuous_sin.continuousAt.comp
      (Complex.continuous_im.continuousAt.comp hg)).eventually (Ioi_mem_nhds hsin0)
  filter_upwards [hc.eventually hge, hbp, hc.eventually hsin] with a ha hba hsa
  intro ht
  have hshift : a.1 - (1 - Real.cos a.2) < 0 := by linarith [Real.cos_le_one a.2]
  have him := congrArg Complex.im ha
  rw [complex_cosh_im] at him
  have him' : Real.sinh (g (realPairToComplex a)).re *
      Real.sin (g (realPairToComplex a)).im =
      (B (a.1 : ℂ)).im * (a.1 - (1 - Real.cos a.2)) := by
    simpa [localNegativeDispersion, realPairToComplex, ← Complex.ofReal_cos] using him
  have hp : 0 < Real.sinh (g (realPairToComplex a)).re *
      Real.sin (g (realPairToComplex a)).im := by
    rw [him']
    exact mul_pos_of_neg_of_neg hba hshift
  exact Real.sinh_pos_iff.mp ((mul_pos_iff_of_pos_right hsa).mp hp)

theorem exp_neg_cosh_identity (γ : ℂ) :
    2 * Complex.cosh γ * Complex.exp (-γ) = Complex.exp (-γ) ^ 2 + 1 := by
  rw [Complex.cosh, Complex.exp_neg]
  field_simp
  ring

theorem small_root_choice_of_witness {lam : ℝ} {z r : ℂ} (q : ℝ)
    (hS : spectralS z ≠ 0) (hp : spectralRootPolynomialF002 lam z q r = 0)
    (hn : ‖r‖ < 1) : r = spectralSmallRootF002 lam z q := by
  have he : ∃ r : ℂ, spectralRootPolynomialF002 lam z q r = 0 ∧ ‖r‖ < 1 := ⟨r, hp, hn⟩
  have hh := he.choose_spec
  have hpoly (v : ℂ) (hv : spectralRootPolynomialF002 lam z q v = 0) :
      v ^ 2 - 2 * ((spectralA lam z - spectralT lam z * (Real.cos q : ℂ)) /
        spectralS z) * v + 1 = 0 := by
    apply (mul_left_cancel₀ hS)
    rw [mul_zero]
    change spectralS z * v ^ 2 -
      2 * (spectralA lam z - spectralT lam z * (Real.cos q : ℂ)) * v + spectralS z = 0 at hv
    field_simp
    linear_combination hv
  have hu := reciprocal_small_root_unique (hpoly r hp) (hpoly he.choose hh.1) hn hh.2
  simpa only [spectralSmallRootF002, dite_eq_left he] using hu

/-- Canonical-root identification needs the unsquared equation and the
positive real phase, not a global logarithm hypothesis. -/
theorem phase_exp_eq_spectralSmallRoot {lam : ℝ} {z γ : ℂ} {q : ℝ}
    (hS : spectralS z ≠ 0)
    (hc : Complex.cosh γ =
      (spectralA lam z - spectralT lam z * (Real.cos q : ℂ)) / spectralS z)
    (hr : 0 < γ.re) :
    Complex.exp (-γ) = spectralSmallRootF002 lam z q := by
  have hp : spectralRootPolynomialF002 lam z q (Complex.exp (-γ)) = 0 := by
    have hrel := exp_neg_cosh_identity γ
    have hcoeff := (div_eq_iff hS).mp hc.symm
    unfold spectralRootPolynomialF002
    linear_combination -spectralS z * hrel - 2 * Complex.exp (-γ) * hcoeff
  have hn : ‖Complex.exp (-γ)‖ < 1 := by
    rw [Complex.norm_exp, Complex.neg_re]
    exact Real.exp_lt_one_iff.mpr (neg_neg_of_pos hr)
  exact small_root_choice_of_witness q hS hp hn

end
end IsingBulk.AnisoF002.NegativeHT
