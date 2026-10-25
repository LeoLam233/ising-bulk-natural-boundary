import IsingBulk.Joint.Transverse.FamilyParticleIdentity
import IsingBulk.Joint.FormFactors.Swap
import IsingBulk.Joint.Geometry.Conjugation
import IsingBulk.Joint.FormFactors.ParticleConjugation

/-! Exact symmetries and genuine mixed smoothness of the literal physical
particle functions, including their physical prefactors and all p weights. -/
namespace IsingBulk.Joint.Transverse
noncomputable section
open FormFactors

theorem highFullParticle_swap (m : ℕ) {K : Coupling} (hK : K∉spectralSet) :
    highFullParticle m K.swap=highFullParticle m K := by
  simp only [highFullParticle,highPrefactor_swap,p_swap,
    unscaledFullCoefficient_swap (2*m+1) (by omega) hK]

theorem lowFullParticle_swap (m : ℕ) {K : Coupling} (hK : K∉spectralSet) :
    lowFullParticle m K.swap=lowFullParticle m K := by
  simp only [lowFullParticle,lowPrefactor_swap,p_swap,
    unscaledFullCoefficient_swap (2*m+2) (by omega) hK]

theorem highFullParticle_contDiffAt (m j : ℕ) {K : Coupling} (hK : K∈highDomain) :
    ContDiffAt ℂ j (highFullParticle m) K :=
  ((highPrefactor_analyticOnNhd K hK).contDiffAt.mul
    ((p_analyticAt_normalized K).pow m).contDiffAt).mul
      (unscaledFullCoefficient_contDiffAt j (2*m+1) (by omega)
        (highDomain_subset_spectralComplement hK))

theorem lowFullParticle_contDiffAt (m j : ℕ) {K : Coupling} (hK : K∈lowDomain) :
    ContDiffAt ℂ j (lowFullParticle m) K :=
  ((lowPrefactor_analyticOnNhd K hK).contDiffAt.mul
    ((p_analyticAt_normalized K).pow (m+1)).contDiffAt).mul
      (unscaledFullCoefficient_contDiffAt j (2*m+2) (by omega)
        (lowDomain_subset_spectralComplement hK))

theorem highFullParticle_conjugate (m : ℕ) {K : Coupling} (hK : K∈highDomain) :
    highFullParticle m (star K)=star (highFullParticle m K) := by
  simp only [highFullParticle,highPrefactor_conjugate hK,p_star,
    unscaledFullCoefficient_conjugate_high (2*m+1) (by omega) hK,star_mul,star_pow]
  ring

theorem lowFullParticle_conjugate (m : ℕ) {K : Coupling} (hK : K∈lowDomain) :
    lowFullParticle m (star K)=star (lowFullParticle m K) := by
  simp only [lowFullParticle,lowPrefactor_conjugate hK,p_star,
    unscaledFullCoefficient_conjugate_low (2*m+2) (by omega) hK,star_mul,star_pow]
  ring

end
end IsingBulk.Joint.Transverse
