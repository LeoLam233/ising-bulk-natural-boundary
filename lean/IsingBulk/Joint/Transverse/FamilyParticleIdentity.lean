import IsingBulk.Joint.Transverse.FamilyNegativeEvenIdentity

/-! # Exact physical particle identities, with all weights and phases retained -/
namespace IsingBulk.Joint.Transverse
noncomputable section
open RegularEdges IsingBulk.Anisotropic.RegularEdges Set Filter Metric
open scoped Topology

def highFullParticle (m : ℕ) (K : Coupling) : ℂ :=
  FormFactors.highPrefactor K*p K^m*FormFactors.unscaledFullCoefficient (2*m+1) K

def lowFullParticle (m : ℕ) (K : Coupling) : ℂ :=
  FormFactors.lowPrefactor K*p K^(m+1)*FormFactors.unscaledFullCoefficient (2*m+2) K

theorem highFullParticle_positive_model (m : ℕ) {b : ℝ} {curve : ℂ→Coupling} {u : ℂ}
    (hK : curve u∈highDomain) (hS : S (curve u)≠0)
    (hB : 0<(transferB (curve u)).im) (he : positiveParameter b (curve u)=u) (hi : 0<u.im) :
    highFullParticle m (curve u)=positiveHighMultiplier (curve u)*
      angularCoefficient (2*m) b (fun v=>transferB (curve v)) (fun v=>positiveParticleScale (curve v)) u := by
  have hid := (fullCoefficient_eq_physicalAngular_high (2*m) hK hS).trans
    (physicalAngular_eq_positiveCoefficient (2*m) (highDomain_subset_spectralComplement hK) hS he hi hB)
  have hr := positiveParticleRoot_ne_zero hS hB
  have hs := angularCoefficient_rescale (2*m) b (fun v=>transferB (curve v))
    (fun v=>S (curve v)) (fun v=>positiveParticleRoot (curve v)) u
  unfold highFullParticle positiveHighMultiplier
  simp only [positiveParticleScale]
  rw [hs,pow_succ,pow_mul,positiveParticleRoot_sq]
  change _=FormFactors.highPrefactor (curve u)/positiveParticleRoot (curve u)*
    (p (curve u)^m*positiveParticleRoot (curve u)*angularCoefficient (2*m) b (curveB curve) (curveS curve) u)
  rw [hid]
  field_simp

theorem lowFullParticle_positive_model (m : ℕ) {b : ℝ} {curve : ℂ→Coupling} {u : ℂ}
    (hK : curve u∈lowDomain) (hS : S (curve u)≠0)
    (hB : 0<(transferB (curve u)).im) (he : positiveParameter b (curve u)=u) (hi : 0<u.im) :
    lowFullParticle m (curve u)=FormFactors.lowPrefactor (curve u)*
      angularCoefficient (2*m+1) b (fun v=>transferB (curve v)) (fun v=>positiveParticleScale (curve v)) u := by
  have hid := (fullCoefficient_eq_physicalAngular_low (2*m+1) hK).trans
    (physicalAngular_eq_positiveCoefficient (2*m+1) (lowDomain_subset_spectralComplement hK) hS he hi hB)
  have hs := angularCoefficient_rescale (2*m+1) b (fun v=>transferB (curve v))
    (fun v=>S (curve v)) (fun v=>positiveParticleRoot (curve v)) u
  unfold lowFullParticle
  simp only [positiveParticleScale]
  rw [hs,show 2*m+1+1=2*(m+1) by omega,pow_mul,positiveParticleRoot_sq]
  rw [show 2*(m+1)=2*m+1+1 by omega,hid]
  exact mul_assoc _ _ _

theorem lowFullParticle_negative_even_model (m : ℕ) {b : ℝ} {curve : ℂ→Coupling} {u : ℂ}
    (hK : curve u∈lowDomain) (hS : S (curve u)≠0)
    (hB : 0<(-transferB (curve u)).im) (he : negativeParameter b (curve u)=u) (hi : 0<u.im) :
    lowFullParticle m (curve u)=FormFactors.lowPrefactor (curve u)*
      angularCoefficient (2*m+1) b (fun v=> -transferB (curve v)) (fun v=>negativeEvenParticleScale (curve v)) u := by
  have hid := (fullCoefficient_eq_physicalAngular_low (2*m+1) hK).trans
    (physicalAngular_eq_negative_even_model (curve:=curve) (n:=2*m+1) ⟨m+1,by omega⟩
      (lowDomain_subset_spectralComplement hK) hS he hi hB)
  have hs := angularCoefficient_rescale (2*m+1) b (fun v=> -transferB (curve v))
    (fun v=>Complex.I*S (curve v)) (fun v=>negativeEvenParticleRoot (curve v)) u
  unfold lowFullParticle
  simp only [negativeEvenParticleScale]
  rw [hs,show 2*m+1+1=2*(m+1) by omega,pow_mul,negativeEvenParticleRoot_sq]
  rw [show 2*(m+1)=2*m+1+1 by omega,hid]
  exact mul_assoc _ _ _

end
end IsingBulk.Joint.Transverse
