import IsingBulk.AnisoF002.C03.IsotropicRadialTransfer
import IsingBulk.AnisoF002.C03.IsotropicPhysicalBoundaryDensity

/-!
# Dense radial obstructions on the actual isotropic temperature frontiers

The only inputs are obstructions of the full canonical particle series
at a dense set of noncritical angles. Each local physical chart is an
actual inverse sinh chart. Conjugation is proved for lambda one directly
from the unique physical root and the constant spectral ratio one.
-/

noncomputable section
namespace IsingBulk.AnisoF002.Isotropic
open scoped Topology ComplexConjugate
open Set Filter IsingBulk.Anisotropic IsingBulk.AnisoF002.Geometry
open IsingBulk.AnisoF002.RegularTail.C03

theorem isotropic_unit_upper_angle {s : ℂ} (hn : ‖s‖ = 1) (hi : 0 < s.im)
    (hr : s.re ≠ 0) :
    ∃ α : ℝ, (0 < α ∧ α < Real.pi) ∧ α ≠ Real.pi / 2 ∧
      s = Complex.exp ((α : ℂ) * Complex.I) := by
  refine ⟨s.arg, ⟨?_, Complex.arg_lt_pi_iff.mpr (Or.inr hi.ne')⟩, ?_, ?_⟩
  · exact lt_of_le_of_ne (Complex.arg_nonneg_iff.mpr hi.le)
      (fun he => hi.ne' (Complex.arg_eq_zero_iff.mp he.symm).2)
  · intro he
    exact hr (Complex.arg_eq_pi_div_two_iff.mp he).1
  · simpa only [hn, Complex.ofReal_one, one_mul] using (Complex.norm_mul_exp_arg_mul_I s).symm

theorem isotropic_low_canonical_noextension_of_dense_radial
    {A : Set ℝ} (m : ℕ) (hA : A ⊆ Ioo (0 : ℝ) Real.pi)
    (hd : ∀ α ∈ Ioo (0 : ℝ) Real.pi, α ≠ Real.pi / 2 → α ∈ closure A)
    (hno : ∀ α ∈ A, ¬ HasIsotropicRadialGerm (isotropicFullParticleSeries m 0 1) α)
    {z : ℂ} (hz : z ∈ isotropicNoncriticalBoundary (omegaL 1))
    (hi : 0 < (Complex.sinh z).im) :
    ¬ HasDomainExtension (omegaL 1) (canonicalAngularTailF002 1 m) z := by
  have hfront := (isotropic_low_frontier_iff z).mp hz.1
  have hx := lt_of_le_of_ne hfront.1 (sinh_real_ne_zero_implies_re_ne_zero hz.2.1).symm
  obtain ⟨α, hα, hαne, he⟩ := isotropic_unit_upper_angle hfront.2 hi hz.2.1
  obtain ⟨Z, hZa, hZ0, hZeq, _⟩ := exists_isotropic_low_temperature_chart hx he
  rintro ⟨U, hU, hzU, g, hg, hge⟩
  have hecont : Continuous (fun θ : ℝ => Complex.exp ((θ : ℂ) * Complex.I)) :=
    Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)
  have ht : Tendsto (fun θ : ℝ => Complex.exp ((θ : ℂ) * Complex.I)) (𝓝 α)
      (𝓝 (Complex.exp ((α : ℂ) * Complex.I))) := hecont.continuousAt.tendsto
  have hzt : Tendsto (fun θ : ℝ => Z (Complex.exp ((θ : ℂ) * Complex.I))) (𝓝 α) (𝓝 z) := by
    simpa only [Function.comp_def, hZ0] using hZa.continuousAt.tendsto.comp ht
  have hnear := (hzt.eventually (hU.mem_nhds hzU)).and
    ((hzt.eventually ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hx)).and
      (ht.eventually hZeq))
  obtain ⟨θ, hθA, hθU, hθx, hθeq⟩ :=
    ((mem_closure_iff_frequently.mp (hd α hα hαne)).and_eventually hnear).exists
  exact hno θ hθA (isotropic_low_canonical_radial_germ m (hA hθA) hθx hθeq.1
    ⟨U, hU, hθU, g, hg, hge⟩)

theorem isotropic_high_canonical_noextension_of_dense_radial
    {A : Set ℝ} (m : ℕ) (hA : A ⊆ Ioo (0 : ℝ) Real.pi)
    (hd : ∀ α ∈ Ioo (0 : ℝ) Real.pi, α ≠ Real.pi / 2 → α ∈ closure A)
    (hno : ∀ α ∈ A, ¬ HasIsotropicRadialGerm (isotropicFullParticleSeries m 0 1) α)
    {z : ℂ} (hz : z ∈ isotropicNoncriticalBoundary (omegaH 1))
    (hi : (Complex.sinh z).im < 0) :
    ¬ HasDomainExtension (omegaH 1) (canonicalAngularTailF002 1 m) z := by
  have hfront := (isotropic_high_frontier_iff z).mp hz.1
  have hx := sinh_real_ne_zero_implies_re_ne_zero hz.2.1
  have hy : |z.im| < Real.pi / 2 := by
    simpa only [isotropic_strip_width] using Physical.high_frontier_nonzero_re_strip
      (by norm_num : (0 : ℝ) < 1) hz.1 hx
  have hs : Complex.sinh z ≠ 0 := fun he => hz.2.1 (by rw [he, Complex.zero_re])
  have hni : ‖(Complex.sinh z)⁻¹‖ = 1 := by rw [norm_inv, hfront.2, inv_one]
  have hii : 0 < ((Complex.sinh z)⁻¹).im := by
    rw [Complex.inv_im]
    exact div_pos (neg_pos.mpr hi) (Complex.normSq_pos.mpr hs)
  have hri : ((Complex.sinh z)⁻¹).re ≠ 0 := by
    rw [Complex.inv_re]
    exact div_ne_zero hz.2.1 (Complex.normSq_pos.mpr hs).ne'
  obtain ⟨α, hα, hαne, hei⟩ := isotropic_unit_upper_angle hni hii hri
  have he : Complex.sinh z = (Complex.exp ((α : ℂ) * Complex.I))⁻¹ := by
    simpa only [inv_inv] using congrArg Inv.inv hei
  obtain ⟨Z, hZa, hZ0, hZeq, _⟩ := exists_isotropic_high_temperature_chart hx hy he
  rintro ⟨U, hU, hzU, g, hg, hge⟩
  have hecont : Continuous (fun θ : ℝ => Complex.exp ((θ : ℂ) * Complex.I)) :=
    Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)
  have ht : Tendsto (fun θ : ℝ => Complex.exp ((θ : ℂ) * Complex.I)) (𝓝 α)
      (𝓝 (Complex.exp ((α : ℂ) * Complex.I))) := hecont.continuousAt.tendsto
  have hzt : Tendsto (fun θ : ℝ => Z (Complex.exp ((θ : ℂ) * Complex.I))) (𝓝 α) (𝓝 z) := by
    simpa only [Function.comp_def, hZ0] using hZa.continuousAt.tendsto.comp ht
  have hre : ∀ᶠ w in 𝓝 z, w.re ≠ 0 := Complex.continuous_re.continuousAt.eventually_ne hx
  have hstrip : ∀ᶠ w in 𝓝 z, |w.im| < Real.pi / 2 :=
    (isOpen_lt Complex.continuous_im.abs continuous_const).mem_nhds hy
  have hnear := (hzt.eventually (hU.mem_nhds hzU)).and
    ((hzt.eventually hre).and ((hzt.eventually hstrip).and (ht.eventually hZeq)))
  obtain ⟨θ, hθA, hθU, hθx, hθy, hθeq⟩ :=
    ((mem_closure_iff_frequently.mp (hd α hα hαne)).and_eventually hnear).exists
  exact hno θ hθA (isotropic_high_canonical_radial_germ m (hA hθA) hθx hθy hθeq.1
    ⟨U, hU, hθU, g, hg, hge⟩)

theorem isotropic_canonical_extension_conjugate {D : Set ℂ} {z : ℂ} (m : ℕ)
    (hD : ∀ w, conj w ∈ D ↔ w ∈ D) (hDC : D ⊆ (spectralSetF002 1)ᶜ)
    (hS : spectralS z ≠ 0)
    (he : HasDomainExtension D (canonicalAngularTailF002 1 m) z) :
    HasDomainExtension D (canonicalAngularTailF002 1 m) (conj z) := by
  apply physical_extension_conjugate hD _ he
  have hnear := (analyticAt_spectralS_f002 z).continuousAt.eventually_ne hS
  filter_upwards [hnear] with w hw hd
  apply physical_canonicalTail_conj (hDC hd) _ m
  rw [spectralRatioF002, isotropic_spectralT, div_self hw]
  exact Or.inl (by norm_num)

theorem isotropic_noncritical_conjugate {D : Set ℂ}
    (hD : ∀ w, conj w ∈ D ↔ w ∈ D) {z : ℂ}
    (hz : z ∈ isotropicNoncriticalBoundary D) :
    conj z ∈ isotropicNoncriticalBoundary D := by
  refine ⟨(physical_frontier_conj hD z).mpr hz.1, ?_, ?_⟩
  · simpa only [Complex.sinh_conj, Complex.conj_re] using hz.2.1
  · simpa only [Complex.sinh_conj, Complex.conj_im, neg_ne_zero] using hz.2.2

theorem isotropic_low_all_noncritical_noextension
    {A : Set ℝ} (m : ℕ) (hA : A ⊆ Ioo (0 : ℝ) Real.pi)
    (hd : ∀ α ∈ Ioo (0 : ℝ) Real.pi, α ≠ Real.pi / 2 → α ∈ closure A)
    (hno : ∀ α ∈ A, ¬ HasIsotropicRadialGerm (isotropicFullParticleSeries m 0 1) α)
    {z : ℂ} (hz : z ∈ isotropicNoncriticalBoundary (omegaL 1)) :
    ¬ HasDomainExtension (omegaL 1) (canonicalAngularTailF002 1 m) z := by
  rcases lt_or_gt_of_ne hz.2.2 with hi | hi
  · intro he
    have hcz := isotropic_noncritical_conjugate (physical_low_domain_conj 1) hz
    have hic : 0 < (Complex.sinh (conj z)).im := by
      simpa only [Complex.sinh_conj, Complex.conj_im] using neg_pos.mpr hi
    apply isotropic_low_canonical_noextension_of_dense_radial m hA hd hno hcz hic
    exact isotropic_canonical_extension_conjugate m (physical_low_domain_conj 1)
      (omegaLF002_subset_complement (by norm_num))
      (spectralS_ne_zero_of_re_ne_zero (sinh_real_ne_zero_implies_re_ne_zero hz.2.1)) he
  · exact isotropic_low_canonical_noextension_of_dense_radial m hA hd hno hz hi

theorem isotropic_high_all_noncritical_noextension
    {A : Set ℝ} (m : ℕ) (hA : A ⊆ Ioo (0 : ℝ) Real.pi)
    (hd : ∀ α ∈ Ioo (0 : ℝ) Real.pi, α ≠ Real.pi / 2 → α ∈ closure A)
    (hno : ∀ α ∈ A, ¬ HasIsotropicRadialGerm (isotropicFullParticleSeries m 0 1) α)
    {z : ℂ} (hz : z ∈ isotropicNoncriticalBoundary (omegaH 1)) :
    ¬ HasDomainExtension (omegaH 1) (canonicalAngularTailF002 1 m) z := by
  rcases lt_or_gt_of_ne hz.2.2 with hi | hi
  · exact isotropic_high_canonical_noextension_of_dense_radial m hA hd hno hz hi
  · intro he
    have hcz := isotropic_noncritical_conjugate (physical_high_domain_conj 1) hz
    have hic : (Complex.sinh (conj z)).im < 0 := by
      simpa only [Complex.sinh_conj, Complex.conj_im] using neg_neg_of_pos hi
    apply isotropic_high_canonical_noextension_of_dense_radial m hA hd hno hcz hic
    exact isotropic_canonical_extension_conjugate m (physical_high_domain_conj 1)
      (omegaHF002_subset_complement (by norm_num))
      (spectralS_ne_zero_of_re_ne_zero (sinh_real_ne_zero_implies_re_ne_zero hz.2.1)) he

end IsingBulk.AnisoF002.Isotropic
