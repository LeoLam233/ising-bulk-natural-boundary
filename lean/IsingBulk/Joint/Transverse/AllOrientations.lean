import IsingBulk.Joint.Transverse.AllOrientationAmbient
import IsingBulk.Joint.Transverse.GeometricTransversality

/-! # Every nonramified holomorphic transverse curve, in all orientations
The transversality premise is the nonzero derivative of the literal unsquared
edge equation. It is not an ambient nonextension premise or a selected slice.
-/
namespace IsingBulk.Joint.Transverse
noncomputable section
open Set IsingBulk.Anisotropic

theorem oriented_prime_high_curve_no_extension {c : ℂ→Coupling} {z : ℂ}
    (hc : AnalyticAt ℂ c z) (hK : c z∈frontier highDomain)
    (hf : OrientedPrimeJointFace (c z)) (ht : IsNonramifiedJointTransversal c z) :
    ¬HasFullExtension (c ⁻¹' highDomain) (FormFactors.highNormalizedBulk∘c) z := by
  obtain ⟨hS,hp,b,hb,hprime,h⟩ := hf
  rcases h with ⟨hB,he⟩ | ⟨hB,he⟩
  · exact positive_high_curve_no_extension hc hK hS hp hB hb hprime he
      (ht.positive_deriv hc hS he)
  · exact Negative.transverse_negative_high_no_extension_of_edge_deriv hc hS
      (by simpa using hB) hK hp he (ht.negative_deriv hc hS he) hprime

theorem oriented_prime_low_curve_no_extension {c : ℂ→Coupling} {z : ℂ}
    (hc : AnalyticAt ℂ c z) (hK : c z∈frontier lowDomain)
    (hf : OrientedPrimeJointFace (c z)) (ht : IsNonramifiedJointTransversal c z) :
    ¬HasFullExtension (c ⁻¹' lowDomain) (FormFactors.lowNormalizedBulk∘c) z := by
  obtain ⟨hS,hp,b,hb,hprime,h⟩ := hf
  rcases h with ⟨hB,he⟩ | ⟨hB,he⟩
  · exact positive_low_curve_no_extension hc hK hS hp hB hb hprime he
      (ht.positive_deriv hc hS he)
  · exact negative_even_low_curve_no_extension hc hK hS hp hB hb hprime he
      (ht.negative_deriv hc hS he)

variable {corrH corrL : PhysicalField.CorrelationFamily}

/-- The complete high-temperature susceptibility on every nonramified
holomorphic transversal at every selected regular phase, without orientation exclusions. -/
theorem prime_regular_high_curve_no_extension
    (hphys : PhysicalField.PublishedRealSpinFamily corrH corrL)
    {c : ℂ→Coupling} {z : ℂ} (hc : AnalyticAt ℂ c z)
    (hK : c z∈frontier highDomain) (hr : IsPrimeRegularJointEdge (c z))
    (ht : IsNonramifiedJointTransversal c z) :
    ¬HasFullExtension (c ⁻¹' highDomain) (FormFactors.highNormalizedBulk∘c) z := by
  intro hext
  rcases primeRegular_oriented_cases hr with h | h | h | h
  · exact oriented_prime_high_curve_no_extension hc hK h ht hext
  · apply oriented_prime_high_curve_no_extension (reflectedCurve_analyticAt hc)
      (by simpa [reflectedCurve] using (star_frontier_high_iff (c z)).mpr hK)
      (by simpa [reflectedCurve] using h) ht.reflected
    exact fullExtension_reflected_curve star_highDomain_iff
      (fun L hL => FormFactors.highNormalizedBulk_conjugate hphys hL) hext
  · apply oriented_prime_high_curve_no_extension
      ((analyticAt_snd.comp hc).prod (analyticAt_fst.comp hc))
      ((swap_frontier_high_iff (c z)).mpr hK) h ht.swap
    exact fullExtension_swapped_curve swap_highDomain_iff
      (fun L hL => FormFactors.highNormalizedBulk_swap hL) hext
  · have hcs : AnalyticAt ℂ (fun t => (c t).swap) z :=
      (analyticAt_snd.comp hc).prod (analyticAt_fst.comp hc)
    apply oriented_prime_high_curve_no_extension (reflectedCurve_analyticAt hcs)
      (by simpa [reflectedCurve] using
        (star_frontier_high_iff (c z).swap).mpr ((swap_frontier_high_iff (c z)).mpr hK))
      (by simpa [reflectedCurve] using h) ht.swap.reflected
    exact fullExtension_reflected_curve star_highDomain_iff
      (fun L hL => FormFactors.highNormalizedBulk_conjugate hphys hL)
      (fullExtension_swapped_curve swap_highDomain_iff
        (fun L hL => FormFactors.highNormalizedBulk_swap hL) hext)

/-- The complete low-temperature susceptibility, including negative even
parity, on every nonramified holomorphic transversal in all orientations. -/
theorem prime_regular_low_curve_no_extension
    (hphys : PhysicalField.PublishedRealSpinFamily corrH corrL)
    {c : ℂ→Coupling} {z : ℂ} (hc : AnalyticAt ℂ c z)
    (hK : c z∈frontier lowDomain) (hr : IsPrimeRegularJointEdge (c z))
    (ht : IsNonramifiedJointTransversal c z) :
    ¬HasFullExtension (c ⁻¹' lowDomain) (FormFactors.lowNormalizedBulk∘c) z := by
  intro hext
  rcases primeRegular_oriented_cases hr with h | h | h | h
  · exact oriented_prime_low_curve_no_extension hc hK h ht hext
  · apply oriented_prime_low_curve_no_extension (reflectedCurve_analyticAt hc)
      (by simpa [reflectedCurve] using (star_frontier_low_iff (c z)).mpr hK)
      (by simpa [reflectedCurve] using h) ht.reflected
    exact fullExtension_reflected_curve star_lowDomain_iff
      (fun L hL => FormFactors.lowNormalizedBulk_conjugate hphys hL) hext
  · apply oriented_prime_low_curve_no_extension
      ((analyticAt_snd.comp hc).prod (analyticAt_fst.comp hc))
      ((swap_frontier_low_iff (c z)).mpr hK) h ht.swap
    exact fullExtension_swapped_curve swap_lowDomain_iff
      (fun L hL => FormFactors.lowNormalizedBulk_swap hL) hext
  · have hcs : AnalyticAt ℂ (fun t => (c t).swap) z :=
      (analyticAt_snd.comp hc).prod (analyticAt_fst.comp hc)
    apply oriented_prime_low_curve_no_extension (reflectedCurve_analyticAt hcs)
      (by simpa [reflectedCurve] using
        (star_frontier_low_iff (c z).swap).mpr ((swap_frontier_low_iff (c z)).mpr hK))
      (by simpa [reflectedCurve] using h) ht.swap.reflected
    exact fullExtension_reflected_curve star_lowDomain_iff
      (fun L hL => FormFactors.lowNormalizedBulk_conjugate hphys hL)
      (fullExtension_swapped_curve swap_lowDomain_iff
        (fun L hL => FormFactors.lowNormalizedBulk_swap hL) hext)

/-- The extension being rejected is ordinary one-variable holomorphic
extension, not merely a syntactically analytic alternative. -/
theorem prime_regular_high_curve_no_holomorphic_extension
    (hphys : PhysicalField.PublishedRealSpinFamily corrH corrL)
    {c : ℂ→Coupling} {z : ℂ} (hc : AnalyticAt ℂ c z)
    (hK : c z∈frontier highDomain) (hr : IsPrimeRegularJointEdge (c z))
    (ht : IsNonramifiedJointTransversal c z) :
    ¬HasHolomorphicFullExtension (c ⁻¹' highDomain) (FormFactors.highNormalizedBulk∘c) z :=
  fun he => prime_regular_high_curve_no_extension hphys hc hK hr ht
    (scalar_fullExtension_of_holomorphic he)

theorem prime_regular_low_curve_no_holomorphic_extension
    (hphys : PhysicalField.PublishedRealSpinFamily corrH corrL)
    {c : ℂ→Coupling} {z : ℂ} (hc : AnalyticAt ℂ c z)
    (hK : c z∈frontier lowDomain) (hr : IsPrimeRegularJointEdge (c z))
    (ht : IsNonramifiedJointTransversal c z) :
    ¬HasHolomorphicFullExtension (c ⁻¹' lowDomain) (FormFactors.lowNormalizedBulk∘c) z :=
  fun he => prime_regular_low_curve_no_extension hphys hc hK hr ht
    (scalar_fullExtension_of_holomorphic he)

end
end IsingBulk.Joint.Transverse
