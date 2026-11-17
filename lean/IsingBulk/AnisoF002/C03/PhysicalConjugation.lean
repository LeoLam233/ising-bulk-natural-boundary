import IsingBulk.AnisoF002.C03.PhysicalSeriesAttachment
import IsingBulk.AnisoF002.C03.PhysicalInwardComponent
import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# Conjugation of the actual spectrum, roots and complete canonical series

The polynomial root is identified by uniqueness in the unit disk.  The
complete numerator uses its real sine factorization, including all pairs.
The principal square root is compared only on its genuine slit domain.
The local extension transport uses the twice-conjugated analytic germ.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open IsingBulk.Anisotropic IsingBulk.AnisoF002.Geometry Filter Set MeasureTheory
open scoped Topology BigOperators ComplexConjugate

theorem physical_spectralS_conj (z : ℂ) : spectralS (conj z) = conj (spectralS z) :=
  Complex.sinh_conj z

theorem physical_spectralT_conj (lam : ℝ) (z : ℂ) :
    spectralT lam (conj z) = conj (spectralT lam z) := by
  unfold spectralT
  have hm : (lam : ℂ) * conj z = conj ((lam : ℂ) * z) := by simp
  rw [hm, Complex.sinh_conj]

theorem physical_spectralA_conj (lam : ℝ) (z : ℂ) :
    spectralA lam (conj z) = conj (spectralA lam z) := by
  unfold spectralA
  have hm : (lam : ℂ) * conj z = conj ((lam : ℂ) * z) := by simp
  rw [hm, Complex.cosh_conj, Complex.cosh_conj, map_mul]

theorem physical_spectralRatio_conj (lam : ℝ) (z : ℂ) :
    spectralRatioF002 lam (conj z) = conj (spectralRatioF002 lam z) := by
  simp only [spectralRatioF002, physical_spectralT_conj, physical_spectralS_conj, map_div₀]

theorem physical_spectralDet_conj (lam : ℝ) (z : ℂ) :
    spectralDetF002 lam (conj z) = -spectralDetF002 lam z := by
  simp only [spectralDetF002, physical_spectralS_conj, physical_spectralT_conj,
    Complex.conj_re, Complex.conj_im]
  ring

theorem physical_spectralSet_conj (lam : ℝ) (z : ℂ) :
    conj z ∈ spectralSetF002 lam ↔ z ∈ spectralSetF002 lam := by
  have hf (w : ℂ) (hw : w ∈ spectralSetF002 lam) : conj w ∈ spectralSetF002 lam := by
    obtain ⟨u, hu, v, hv, h⟩ := hw
    refine ⟨u, hu, v, hv, ?_⟩
    simpa only [physical_spectralA_conj, physical_spectralS_conj, physical_spectralT_conj,
      map_add, map_mul, Complex.conj_ofReal] using congrArg conj h
  exact ⟨fun h => by simpa only [starRingEnd_self_apply] using hf (conj z) h, hf z⟩

theorem physical_canonicalRoot_conj {lam : ℝ} {z : ℂ}
    (hz : z ∉ spectralSetF002 lam) (q : ℝ) :
    spectralSmallRootF002 lam (conj z) q = conj (spectralSmallRootF002 lam z q) := by
  have hzc : conj z ∉ spectralSetF002 lam := (physical_spectralSet_conj lam z).not.mpr hz
  symm
  apply spectralSmallRootF002_unique q hzc
  · have hp := congrArg conj (spectralSmallRootF002_spec q hz).1
    simpa only [spectralRootPolynomialF002, physical_spectralS_conj,
      physical_spectralT_conj, physical_spectralA_conj, map_add, map_sub, map_mul,
      map_pow, map_ofNat, map_zero, Complex.conj_ofReal] using hp
  · simpa only [Complex.norm_conj] using (spectralSmallRootF002_spec q hz).2

theorem physical_sqrt_conj {B : ℂ} (hB : B ∈ Complex.slitPlane) :
    Complex.sqrt (conj B) = conj (Complex.sqrt B) := by
  simpa only [Complex.sqrt, map_inv₀, map_ofNat] using
    Complex.conj_cpow B (2⁻¹ : ℂ) (Complex.slitPlane_arg_ne_pi hB)

theorem physical_oneBody_conj {lam : ℝ} {z : ℂ}
    (hz : z ∉ spectralSetF002 lam) (q : ℝ) :
    spectralOneBodyF002 lam (conj z) q = conj (spectralOneBodyF002 lam z q) := by
  simp only [spectralOneBodyF002, physical_canonicalRoot_conj hz, map_mul,
    map_div₀, map_pow, map_sub, map_one, map_ofNat]

theorem physical_canceledPair_conj {lam : ℝ} {z : ℂ}
    (hz : z ∉ spectralSetF002 lam) (q t : ℝ) :
    spectralCanceledPairF002 lam (conj z) q t = conj (spectralCanceledPairF002 lam z q t) := by
  simp only [spectralCanceledPairF002_factorization, spectralSinePairCoefficientF002,
    sinePairCoefficient, physical_spectralT_conj, physical_spectralS_conj,
    physical_canonicalRoot_conj hz, map_mul, map_div₀, map_pow, map_sub, map_one,
    map_ofNat, Complex.conj_ofReal]

theorem physical_canonicalDensity_conj {N : ℕ} {lam : ℝ} {z : ℂ}
    (hz : z ∉ spectralSetF002 lam) (hB : spectralRatioF002 lam z ∈ Complex.slitPlane)
    (q : Fin N → ℝ) :
    canonicalAngularDensityF002 lam (conj z) q = conj (canonicalAngularDensityF002 lam z q) := by
  simp only [canonicalAngularDensityF002, fullRootNumeratorF002,
    physical_spectralRatio_conj, physical_sqrt_conj hB, physical_oneBody_conj hz,
    physical_canceledPair_conj hz, physical_canonicalRoot_conj hz, map_mul,
    map_div₀, map_pow, map_sub, map_add, map_one, map_prod]

theorem physical_canonicalCoefficient_conj {lam : ℝ} {z : ℂ}
    (hz : z ∉ spectralSetF002 lam) (hB : spectralRatioF002 lam z ∈ Complex.slitPlane) (n : ℕ) :
    canonicalAngularCoefficientF002 lam n (conj z) = conj (canonicalAngularCoefficientF002 lam n z) := by
  unfold canonicalAngularCoefficientF002
  simp_rw [physical_canonicalDensity_conj hz hB]
  rw [integral_conj]
  simp only [map_mul, map_inv₀, map_natCast]

theorem physical_canonicalTail_conj {lam : ℝ} {z : ℂ}
    (hz : z ∉ spectralSetF002 lam) (hB : spectralRatioF002 lam z ∈ Complex.slitPlane) (m : ℕ) :
    canonicalAngularTailF002 lam m (conj z) = conj (canonicalAngularTailF002 lam m z) := by
  unfold canonicalAngularTailF002
  simp_rw [physical_canonicalCoefficient_conj hz hB]
  exact (RCLike.conj_tsum _).symm

theorem physical_high_domain_conj (lam : ℝ) (z : ℂ) : conj z ∈ omegaH lam ↔ z ∈ omegaH lam := by
  change conj z ∈ omegaHF002 lam ↔ z ∈ omegaHF002 lam
  simp only [omegaHF002, highProfileF002, mem_ofPred_eq, Complex.conj_im, Complex.conj_re,
    abs_neg, Real.cos_neg, mul_neg]

theorem physical_low_domain_conj (lam : ℝ) (z : ℂ) : conj z ∈ omegaL lam ↔ z ∈ omegaL lam := by
  change conj z ∈ omegaLF002 lam ↔ z ∈ omegaLF002 lam
  simp only [omegaLF002, lowProfileF002, mem_ofPred_eq, Complex.conj_im, Complex.conj_re,
    Real.cos_neg, mul_neg]

theorem physical_frontier_conj {D : Set ℂ} (hD : ∀ w, conj w ∈ D ↔ w ∈ D) (z : ℂ) :
    conj z ∈ frontier D ↔ z ∈ frontier D := by
  have hp : Complex.conjCLE.toHomeomorph ⁻¹' D = D := by ext w; exact hD w
  have hh := Complex.conjCLE.toHomeomorph.preimage_frontier D
  rw [hp] at hh
  exact Set.ext_iff.mp hh z

theorem physical_profileDifference_neg (lam y : ℝ) :
    profileDifferenceF002 lam (-y) = profileDifferenceF002 lam y := by
  simp only [profileDifferenceF002, signedProfileRF002, signedProfileUF002, Real.cos_neg, mul_neg]

theorem physical_regularBoundary_conj {lam : ℝ} {D : Set ℂ}
    (hD : ∀ w, conj w ∈ D ↔ w ∈ D) {z : ℂ}
    (hz : z ∈ regularBoundaryF002 lam D) : conj z ∈ regularBoundaryF002 lam D := by
  exact ⟨(physical_frontier_conj hD z).mpr hz.1,
    by simpa only [Complex.conj_re] using hz.2.1,
    by simpa only [Complex.conj_im, physical_profileDifference_neg] using hz.2.2⟩

theorem analyticAt_twice_conjugated {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z) :
    AnalyticAt ℂ (fun w => conj (f (conj w))) (conj z) := by
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  have he : ∀ᶠ w in 𝓝 (conj z), AnalyticAt ℂ f (conj w) := by
    have hc : ContinuousAt conj (conj z) := Complex.continuous_conj.continuousAt
    have hh : ∀ᶠ w in 𝓝 (conj (conj z)), AnalyticAt ℂ f w := by
      simpa only [starRingEnd_self_apply] using hf.eventually_analyticAt
    exact hc.eventually hh
  filter_upwards [he] with w hw
  simpa only [Function.comp_def, starRingEnd_self_apply] using hw.differentiableAt.conj_conj

theorem physical_extension_conjugate {D : Set ℂ} {F : ℂ → ℂ} {z : ℂ}
    (hD : ∀ w, conj w ∈ D ↔ w ∈ D)
    (hF : ∀ᶠ w in 𝓝 z, w ∈ D → F (conj w) = conj (F w))
    (he : HasDomainExtension D F z) : HasDomainExtension D F (conj z) := by
  obtain ⟨U, hU, hzU, g, hg, heq⟩ := he
  obtain ⟨V, hV, hVo, hzV⟩ := mem_nhds_iff.mp hF
  refine ⟨conj ⁻¹' (U ∩ V), (hU.inter hVo).preimage Complex.continuous_conj,
    by simpa only [mem_preimage, starRingEnd_self_apply, mem_inter_iff] using And.intro hzU hzV,
    (fun w => conj (g (conj w))), ?_, ?_⟩
  · intro w hw
    simpa only [starRingEnd_self_apply] using analyticAt_twice_conjugated (hg _ hw.1)
  · intro w hw
    have hd : conj w ∈ D := (hD w).mpr hw.2
    change conj (g (conj w)) = F w
    rw [heq ⟨hw.1.1, hd⟩]
    simpa only [starRingEnd_self_apply] using (hV hw.1.2 hd).symm

theorem physical_canonical_extension_conjugate {lam : ℝ} {D : Set ℂ} {z : ℂ} {m : ℕ}
    (hD : ∀ w, conj w ∈ D ↔ w ∈ D) (hDC : D ⊆ (spectralSetF002 lam)ᶜ)
    (hx : z.re ≠ 0) (hdet : spectralDetF002 lam z ≠ 0)
    (he : HasDomainExtension D (canonicalAngularTailF002 lam m) z) :
    HasDomainExtension D (canonicalAngularTailF002 lam m) (conj z) := by
  apply physical_extension_conjugate hD ?_ he
  have hS := spectralS_ne_zero_of_re_ne_zero hx
  have hB : spectralRatioF002 lam z ∈ Complex.slitPlane := by
    apply Or.inr
    rw [spectralRatioF002_im]
    exact div_ne_zero hdet (Complex.normSq_pos.mpr hS).ne'
  have hnear := (analyticAt_spectralRatioF002 hS).continuousAt.eventually
    (Complex.isOpen_slitPlane.mem_nhds hB)
  filter_upwards [hnear] with w hw
  intro hd
  exact physical_canonicalTail_conj (hDC hd) hw m

end
end IsingBulk.AnisoF002.RegularTail.C03
