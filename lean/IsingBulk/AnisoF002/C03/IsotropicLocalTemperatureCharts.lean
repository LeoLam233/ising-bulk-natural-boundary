import IsingBulk.AnisoF002.C03.IsotropicPhysicalDomains
import IsingBulk.AnisoF002.C03.IsotropicRadialApproach

/-!
# Actual local temperature charts for the isotropic exterior radial path

The inverse functions are constructed by the analytic inverse theorem.
LT has sinh Z(t)=t and HT has sinh Z(t)=t^{-1}; the same original
dispersion is t+t^{-1}. Membership in each original physical domain
is proved on the actual exterior radial approach.
-/

noncomputable section
namespace IsingBulk.AnisoF002.Isotropic
open scoped Topology
open IsingBulk.Anisotropic IsingBulk.AnisoF002.Geometry
open Set Filter

theorem isotropic_local_analytic_inverse {f : ℂ → ℂ} {z d : ℂ}
    (ha : AnalyticAt ℂ f z) (hd : HasDerivAt f d z) (hd0 : d ≠ 0) :
    ∃ Z : ℂ → ℂ, AnalyticAt ℂ Z (f z) ∧ Z (f z) = z ∧
      (∀ᶠ t in 𝓝 (f z), f (Z t) = t) ∧ (∀ᶠ w in 𝓝 z, Z (f w) = w) := by
  have hstrict : HasStrictDerivAt f d z := by
    simpa only [hd.deriv] using ha.hasStrictDerivAt
  let H := (hstrict.hasStrictFDerivAt_equiv hd0).toOpenPartialHomeomorph f
  have hm : z ∈ H.source :=
    (hstrict.hasStrictFDerivAt_equiv hd0).mem_toOpenPartialHomeomorph_source
  refine ⟨H.symm, H.analyticAt_symm' hm ha
    (hstrict.hasStrictFDerivAt_equiv hd0).hasFDerivAt.fderiv, H.left_inv hm,
    H.eventually_right_inverse' hm, H.eventually_left_inverse hm⟩

theorem isotropicExteriorRadial_zero (α : ℝ) :
    isotropicExteriorRadial α 0 = Complex.exp ((α : ℂ) * Complex.I) := by
  simp only [isotropicExteriorRadial, add_zero, Complex.ofReal_one, one_mul]

theorem isotropicRadialParameter_zero (α : ℝ) :
    isotropicRadialParameter α 0 = ((2 * Real.cos α : ℝ) : ℂ) := by
  rw [isotropicRadialParameter_formula]
  norm_num

theorem isotropicExteriorRadial_tendsto (α : ℝ) :
    Tendsto (isotropicExteriorRadial α) (𝓝 (0 : ℝ))
      (𝓝 (Complex.exp ((α : ℂ) * Complex.I))) := by
  have hc : Continuous (isotropicExteriorRadial α) :=
    (Complex.continuous_ofReal.comp (continuous_const.add continuous_id)).mul continuous_const
  simpa only [isotropicExteriorRadial_zero] using hc.continuousAt.tendsto (x := (0 : ℝ))

theorem isotropicRadialParameter_tendsto (α : ℝ) :
    Tendsto (isotropicRadialParameter α) (𝓝 (0 : ℝ)) (𝓝 ((2 * Real.cos α : ℝ) : ℂ)) := by
  have ht := isotropicExteriorRadial_tendsto α
  have hh := ht.add (ht.inv₀ (Complex.exp_ne_zero _))
  have he : Complex.exp ((α : ℂ) * Complex.I) + (Complex.exp ((α : ℂ) * Complex.I))⁻¹ =
      ((2 * Real.cos α : ℝ) : ℂ) := by
    simpa only [isotropicRadialParameter, isotropicExteriorRadial_zero] using isotropicRadialParameter_zero α
  exact he ▸ hh

theorem isotropicRadialParameter_eventually_upper {α : ℝ} (hα : 0 < α ∧ α < Real.pi) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < (isotropicRadialParameter α ε).im := by
  have hu : ∀ᶠ ε : ℝ in 𝓝 0, ε < 1 := Iio_mem_nhds zero_lt_one
  filter_upwards [self_mem_nhdsWithin, hu.filter_mono nhdsWithin_le_nhds] with ε hε hε1
  exact (isotropicRadialParameter_estimates α ε hα hε hε1.le).2.2.2.1

theorem isotropic_exp_sq_ne_one {α : ℝ} (hα : 0 < α ∧ α < Real.pi) :
    Complex.exp ((α : ℂ) * Complex.I) ^ 2 ≠ 1 := by
  intro he
  have hi : 0 < (Complex.exp ((α : ℂ) * Complex.I)).im := by
    simpa only [Complex.exp_mul_I, Complex.add_im, Complex.mul_im, ← Complex.ofReal_sin,
      ← Complex.ofReal_cos, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_one, mul_zero, add_zero, zero_add] using
      Real.sin_pos_of_pos_of_lt_pi hα.1 hα.2
  rcases sq_eq_one_iff.mp he with he | he
  · rw [he, Complex.one_im] at hi
    exact (lt_irrefl 0) hi
  · rw [he] at hi
    norm_num at hi

theorem exists_isotropic_joukowski_inverse {α : ℝ} (hα : 0 < α ∧ α < Real.pi) :
    ∃ T : ℂ → ℂ, AnalyticAt ℂ T ((2 * Real.cos α : ℝ) : ℂ) ∧
      T ((2 * Real.cos α : ℝ) : ℂ) = Complex.exp ((α : ℂ) * Complex.I) ∧
      (∀ᶠ S in 𝓝 ((2 * Real.cos α : ℝ) : ℂ), T S + (T S)⁻¹ = S) ∧
      (∀ᶠ t in 𝓝 (Complex.exp ((α : ℂ) * Complex.I)), T (t + t⁻¹) = t) := by
  let t₀ := Complex.exp ((α : ℂ) * Complex.I)
  have ht : t₀ ≠ 0 := Complex.exp_ne_zero _
  have hd : HasDerivAt (fun t : ℂ => t + t⁻¹) (1 - (t₀ ^ 2)⁻¹) t₀ := by
    have hi : HasDerivAt (fun t : ℂ => t) (1 : ℂ) t₀ := hasDerivAt_id' t₀
    have hv : HasDerivAt (fun t : ℂ => t⁻¹) (-(t₀ ^ 2)⁻¹) t₀ := hasDerivAt_inv ht
    convert hi.add hv using 1
  have hd0 : 1 - (t₀ ^ 2)⁻¹ ≠ 0 := by
    intro he
    have hh : (t₀ ^ 2)⁻¹ = 1 := (sub_eq_zero.mp he).symm
    rw [inv_eq_one] at hh
    exact isotropic_exp_sq_ne_one hα hh
  have hc : t₀ + t₀⁻¹ = ((2 * Real.cos α : ℝ) : ℂ) := by
    simpa only [isotropicRadialParameter, isotropicExteriorRadial_zero, t₀] using isotropicRadialParameter_zero α
  obtain ⟨T, ha, hT, hright, hleft⟩ := isotropic_local_analytic_inverse
    (analyticAt_id.add (analyticAt_id.inv ht)) hd hd0
  exact ⟨T, hc ▸ ha, hc ▸ hT, hc ▸ hright, hleft⟩

theorem exists_isotropic_low_temperature_chart {z : ℂ} {α : ℝ}
    (hx : 0 < z.re) (he : Complex.sinh z = Complex.exp ((α : ℂ) * Complex.I)) :
    ∃ Z : ℂ → ℂ, AnalyticAt ℂ Z (Complex.exp ((α : ℂ) * Complex.I)) ∧
      Z (Complex.exp ((α : ℂ) * Complex.I)) = z ∧
      (∀ᶠ t in 𝓝 (Complex.exp ((α : ℂ) * Complex.I)),
        Complex.sinh (Z t) = t ∧ isotropicPhysicalParameter (Z t) = t + t⁻¹) ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), Z (isotropicExteriorRadial α ε) ∈ omegaL 1) := by
  obtain ⟨Z, hZa, hZ0, hZright, _⟩ := isotropic_local_analytic_inverse
    Complex.analyticAt_sinh (Complex.hasDerivAt_sinh z)
    (complex_cosh_ne_zero_of_re_ne_zero hx.ne')
  rw [he] at hZa hZ0 hZright
  have hzre : ∀ᶠ t in 𝓝 (Complex.exp ((α : ℂ) * Complex.I)), 0 < (Z t).re := by
    have hc : Tendsto Z (𝓝 (Complex.exp ((α : ℂ) * Complex.I))) (𝓝 z) := by
      simpa only [hZ0] using hZa.continuousAt.tendsto
    exact hc.eventually ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hx)
  refine ⟨Z, hZa, hZ0, ?_, ?_⟩
  · filter_upwards [hZright] with t ht
    exact ⟨ht, by simp only [isotropicPhysicalParameter, ht]⟩
  · have ht : Tendsto (isotropicExteriorRadial α) (𝓝[>] (0 : ℝ))
        (𝓝 (Complex.exp ((α : ℂ) * Complex.I))) :=
      (isotropicExteriorRadial_tendsto α).mono_left nhdsWithin_le_nhds
    filter_upwards [ht.eventually hZright, ht.eventually hzre, self_mem_nhdsWithin] with ε heq hre hε
    apply (isotropic_low_domain_iff _).mpr
    exact ⟨hre, by rw [heq]; exact isotropicExteriorRadial_exterior α ε hε⟩

theorem exists_isotropic_high_temperature_chart {z : ℂ} {α : ℝ}
    (hx : z.re ≠ 0) (hy : |z.im| < Real.pi / 2)
    (he : Complex.sinh z = (Complex.exp ((α : ℂ) * Complex.I))⁻¹) :
    ∃ Z : ℂ → ℂ, AnalyticAt ℂ Z (Complex.exp ((α : ℂ) * Complex.I)) ∧
      Z (Complex.exp ((α : ℂ) * Complex.I)) = z ∧
      (∀ᶠ t in 𝓝 (Complex.exp ((α : ℂ) * Complex.I)),
        Complex.sinh (Z t) = t⁻¹ ∧ isotropicPhysicalParameter (Z t) = t + t⁻¹) ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), Z (isotropicExteriorRadial α ε) ∈ omegaH 1) := by
  obtain ⟨Y, hYa, hY0, hYright, _⟩ := isotropic_local_analytic_inverse
    Complex.analyticAt_sinh (Complex.hasDerivAt_sinh z) (complex_cosh_ne_zero_of_re_ne_zero hx)
  rw [he] at hYa hY0 hYright
  let Z : ℂ → ℂ := fun t => Y t⁻¹
  have ht0 : Complex.exp ((α : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
  have hZa : AnalyticAt ℂ Z (Complex.exp ((α : ℂ) * Complex.I)) :=
    hYa.comp (analyticAt_id.inv ht0)
  have hZ0 : Z (Complex.exp ((α : ℂ) * Complex.I)) = z := hY0
  have hZright : ∀ᶠ t in 𝓝 (Complex.exp ((α : ℂ) * Complex.I)), Complex.sinh (Z t) = t⁻¹ :=
    (continuousAt_id.inv₀ ht0).eventually hYright
  have hzstrip : ∀ᶠ t in 𝓝 (Complex.exp ((α : ℂ) * Complex.I)), |(Z t).im| < Real.pi / 2 := by
    have hc : Tendsto Z (𝓝 (Complex.exp ((α : ℂ) * Complex.I))) (𝓝 z) := by
      simpa only [hZ0] using hZa.continuousAt.tendsto
    exact hc.eventually ((isOpen_lt Complex.continuous_im.abs continuous_const).mem_nhds hy)
  refine ⟨Z, hZa, hZ0, ?_, ?_⟩
  · filter_upwards [hZright] with t ht
    exact ⟨ht, by simp only [isotropicPhysicalParameter, ht, inv_inv, add_comm]⟩
  · have ht : Tendsto (isotropicExteriorRadial α) (𝓝[>] (0 : ℝ))
        (𝓝 (Complex.exp ((α : ℂ) * Complex.I))) :=
      (isotropicExteriorRadial_tendsto α).mono_left nhdsWithin_le_nhds
    filter_upwards [ht.eventually hZright, ht.eventually hzstrip, self_mem_nhdsWithin] with ε heq hstrip hε
    apply (isotropic_high_domain_iff _).mpr
    refine ⟨hstrip, ?_⟩
    rw [heq, norm_inv]
    exact (inv_lt_one₀ (lt_trans zero_lt_one (isotropicExteriorRadial_exterior α ε hε))).mpr
      (isotropicExteriorRadial_exterior α ε hε)

end IsingBulk.AnisoF002.Isotropic
