import IsingBulk.Anisotropic.NegativeDominance.FixedParticleJets
import IsingBulk.Anisotropic.RegularEdges.ComplexAngularIdentity

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open IsingBulk.First IsingBulk.Anisotropic.RegularEdges FormFactors Set Filter
open scoped Topology

/-- Attachment to the actual full-site coefficient on the high-temperature
component and the negative physical sheet. This is only a fixed odd term. -/
theorem fixed_odd_fullCoefficient_has_domain_extension
    (n : ℕ) (hN : Odd (n+1)) {lam b : ℝ} (hlam : 0<lam) {z : ℂ}
    (hS : spectralS z≠0) (hedge : spectralA lam z+spectralT lam z=(b : ℂ)*spectralS z)
    (hb : |b|<1) (hB : 0<(-spectralT lam z/spectralS z).im) :
    HasDomainExtension ((omegaH lam\{0})∩negativePhysicalSheet lam)
      (unscaledFullCoefficient (n+1) lam) z := by
  have ha := continuedAngularCoefficient_negative_analyticAt n hN hS hedge hb hB
  obtain ⟨U,hU,hUopen,hzU⟩ := mem_nhds_iff.mp ha.eventually_analyticAt
  refine ⟨U,hUopen,hzU,continuedAngularCoefficient n lam,fun w hw => hU hw,?_⟩
  intro w hw
  exact (continuedAngularCoefficient_eq_unscaled_on_sheet n lam hw.2.2).trans
    ((unscaledFullCoefficient_eq_angular_omegaH n hlam) hw.2.1).symm

/-- Boundary derivatives of the actual full-site fixed odd coefficient. -/
theorem fixed_odd_fullCoefficient_boundary_jets
    {ι : Type*} {l : Filter ι} {path : ι → ℂ}
    (n : ℕ) (hN : Odd (n+1)) {lam b : ℝ} (hlam : 0<lam) {z : ℂ}
    (hS : spectralS z≠0) (hedge : spectralA lam z+spectralT lam z=(b : ℂ)*spectralS z)
    (hb : |b|<1) (hB : 0<(-spectralT lam z/spectralS z).im)
    (hp : Tendsto path l (𝓝 z))
    (hin : ∀ᶠ t in l, path t∈(omegaH lam\{0})∩negativePhysicalSheet lam) (j : ℕ) :
    Tendsto (fun t => iteratedDeriv j (unscaledFullCoefficient (n+1) lam) (path t)/(j.factorial : ℂ)) l
      (𝓝 (iteratedDeriv j (continuedAngularCoefficient n lam) z/(j.factorial : ℂ))) := by
  have hangular := fixed_odd_particle_boundary_jets n hN hS hedge hb hB hp
    (hin.mono (fun _ ht => ht.2)) j
  apply hangular.congr'
  filter_upwards [hin] with t ht
  have he : unscaledFullCoefficient (n+1) lam =ᶠ[𝓝 (path t)] unscaledAngularCoefficient n lam := by
    filter_upwards [((omegaH_isOpen hlam).sdiff isClosed_singleton).mem_nhds ht.1] with w hw
    exact unscaledFullCoefficient_eq_angular_omegaH n hlam hw
  rw [he.iteratedDeriv_eq]

end
end IsingBulk.Anisotropic.NegativeDominance
