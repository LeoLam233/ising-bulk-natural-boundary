import IsingBulk.Joint.Transverse.AmbientObstruction
import IsingBulk.Joint.Transverse.SymmetryTransport
import IsingBulk.Joint.Negative.TransverseObstruction
import IsingBulk.Joint.Geometry.OrientedRegular

/-! # Actual ambient obstructions in every regular prime-phase orientation -/
namespace IsingBulk.Joint.Transverse
noncomputable section
open Set Filter IsingBulk.Anisotropic
open scoped Topology

theorem negative_high_no_holomorphic_extension {K : Coupling} {b : ℝ}
    (hK : K∈frontier highDomain) (hS : S K≠0) (hp : p K^2≠1)
    (hB : 0<(-transferB K).im) (hprime : b∈primePhaseCosines)
    (he : negativeParameter b K=0) :
    ¬HasHolomorphicFullExtension highDomain FormFactors.highNormalizedBulk K := by
  obtain ⟨c,hc,hc0,hn,_⟩ := exists_negative_normal_curve hS hp he
  have hn' : (fun t => negativeParameter b (c t)) =ᶠ[𝓝 (0:ℂ)] id := hn
  have hd : deriv (fun t => negativeParameter b (c t)) 0≠0 := by
    rw [hn'.deriv_eq]
    simp
  intro hext
  apply Negative.transverse_negative_high_no_extension_of_edge_deriv hc
    (hc0 ▸ hS) (by simpa [hc0] using hB) (hc0 ▸ hK) (hc0 ▸ hp)
    (by simpa only [hc0,negativeParameter] using he) hd hprime
  exact analytic_scalar_pullback_of_holomorphic_extension hc hc0 hext

theorem oriented_prime_high_no_holomorphic_extension {K : Coupling}
    (hK : K∈frontier highDomain) (hf : OrientedPrimeJointFace K) :
    ¬HasHolomorphicFullExtension highDomain FormFactors.highNormalizedBulk K := by
  obtain ⟨hS,hp,b,hb,hprime,h⟩ := hf
  rcases h with ⟨hB,he⟩ | ⟨hB,he⟩
  · exact positive_high_no_holomorphic_extension hK hS hp hB hb hprime he
  · exact negative_high_no_holomorphic_extension hK hS hp hB hprime he

theorem oriented_prime_low_no_holomorphic_extension {K : Coupling}
    (hK : K∈frontier lowDomain) (hf : OrientedPrimeJointFace K) :
    ¬HasHolomorphicFullExtension lowDomain FormFactors.lowNormalizedBulk K := by
  obtain ⟨hS,hp,b,hb,hprime,h⟩ := hf
  rcases h with ⟨hB,he⟩ | ⟨hB,he⟩
  · exact positive_low_no_holomorphic_extension hK hS hp hB hb hprime he
  · exact negative_even_low_no_holomorphic_extension hK hS hp hB hb hprime he

variable {corrH corrL : PhysicalField.CorrelationFamily}

theorem prime_regular_high_no_holomorphic_extension
    (hphys : PhysicalField.PublishedRealSpinFamily corrH corrL)
    {K : Coupling} (hK : K∈frontier highDomain) (hr : IsPrimeRegularJointEdge K) :
    ¬HasHolomorphicFullExtension highDomain FormFactors.highNormalizedBulk K := by
  intro hext
  rcases primeRegular_oriented_cases hr with h | h | h | h
  · exact oriented_prime_high_no_holomorphic_extension hK h hext
  · exact oriented_prime_high_no_holomorphic_extension ((star_frontier_high_iff K).mpr hK) h
      (holomorphicExtension_star star_highDomain_iff
        (fun L hL => FormFactors.highNormalizedBulk_conjugate hphys hL) hext)
  · exact oriented_prime_high_no_holomorphic_extension ((swap_frontier_high_iff K).mpr hK) h
      (holomorphicExtension_swap swap_highDomain_iff
        (fun L hL => FormFactors.highNormalizedBulk_swap hL) hext)
  · exact oriented_prime_high_no_holomorphic_extension
      ((star_frontier_high_iff K.swap).mpr ((swap_frontier_high_iff K).mpr hK)) h
      (holomorphicExtension_star star_highDomain_iff
        (fun L hL => FormFactors.highNormalizedBulk_conjugate hphys hL)
        (holomorphicExtension_swap swap_highDomain_iff
          (fun L hL => FormFactors.highNormalizedBulk_swap hL) hext))

theorem prime_regular_low_no_holomorphic_extension
    (hphys : PhysicalField.PublishedRealSpinFamily corrH corrL)
    {K : Coupling} (hK : K∈frontier lowDomain) (hr : IsPrimeRegularJointEdge K) :
    ¬HasHolomorphicFullExtension lowDomain FormFactors.lowNormalizedBulk K := by
  intro hext
  rcases primeRegular_oriented_cases hr with h | h | h | h
  · exact oriented_prime_low_no_holomorphic_extension hK h hext
  · exact oriented_prime_low_no_holomorphic_extension ((star_frontier_low_iff K).mpr hK) h
      (holomorphicExtension_star star_lowDomain_iff
        (fun L hL => FormFactors.lowNormalizedBulk_conjugate hphys hL) hext)
  · exact oriented_prime_low_no_holomorphic_extension ((swap_frontier_low_iff K).mpr hK) h
      (holomorphicExtension_swap swap_lowDomain_iff
        (fun L hL => FormFactors.lowNormalizedBulk_swap hL) hext)
  · exact oriented_prime_low_no_holomorphic_extension
      ((star_frontier_low_iff K.swap).mpr ((swap_frontier_low_iff K).mpr hK)) h
      (holomorphicExtension_star star_lowDomain_iff
        (fun L hL => FormFactors.lowNormalizedBulk_conjugate hphys hL)
        (holomorphicExtension_swap swap_lowDomain_iff
          (fun L hL => FormFactors.lowNormalizedBulk_swap hL) hext))

end
end IsingBulk.Joint.Transverse
