import IsingBulk.Joint.Transverse.ConstantAnisotropy
import IsingBulk.Joint.Transverse.PositiveObstruction
import IsingBulk.Joint.Transverse.NegativeEvenObstruction
import IsingBulk.Joint.Final.HolomorphicExtension

/-! # Genuine ambient holomorphic obstructions from actual transverse curves
Only the valid implication is used: an ambient holomorphic extension would
pull back to a scalar analytic extension on the constructed transversal.
-/
namespace IsingBulk.Joint.Transverse
noncomputable section
open Set
open IsingBulk.Anisotropic IsingBulk.Anisotropic.RegularEdges

theorem positive_high_no_holomorphic_extension {K : Coupling} {b : ℝ}
    (hK : K∈frontier highDomain) (hS : S K≠0) (hp : p K^2≠1)
    (hB : 0<(transferB K).im) (hb : |b|<1) (hprime : b∈primePhaseCosines)
    (he : positiveParameter b K=0) :
    ¬HasHolomorphicFullExtension highDomain FormFactors.highNormalizedBulk K := by
  obtain ⟨c,hc,hc0,hn,_⟩ := exists_positive_normal_curve hS hp he
  intro hext
  apply normalized_positive_high_no_extension hc (hc0 ▸ hK) (hc0 ▸ hS) (hc0 ▸ hp)
    (by simpa [curveB,hc0] using hB) hb hprime hn
  exact analytic_scalar_pullback_of_holomorphic_extension hc hc0 hext

theorem positive_low_no_holomorphic_extension {K : Coupling} {b : ℝ}
    (hK : K∈frontier lowDomain) (hS : S K≠0) (hp : p K^2≠1)
    (hB : 0<(transferB K).im) (hb : |b|<1) (hprime : b∈primePhaseCosines)
    (he : positiveParameter b K=0) :
    ¬HasHolomorphicFullExtension lowDomain FormFactors.lowNormalizedBulk K := by
  obtain ⟨c,hc,hc0,hn,_⟩ := exists_positive_normal_curve hS hp he
  intro hext
  apply normalized_positive_low_no_extension hc (hc0 ▸ hK) (hc0 ▸ hS) (hc0 ▸ hp)
    (by simpa [curveB,hc0] using hB) hb hprime hn
  exact analytic_scalar_pullback_of_holomorphic_extension hc hc0 hext

theorem negative_even_low_no_holomorphic_extension {K : Coupling} {b : ℝ}
    (hK : K∈frontier lowDomain) (hS : S K≠0) (hp : p K^2≠1)
    (hB : 0<(-transferB K).im) (hb : |b|<1) (hprime : b∈primePhaseCosines)
    (he : negativeParameter b K=0) :
    ¬HasHolomorphicFullExtension lowDomain FormFactors.lowNormalizedBulk K := by
  obtain ⟨c,hc,hc0,hn,_⟩ := exists_negative_normal_curve hS hp he
  intro hext
  apply normalized_negative_even_low_no_extension hc (hc0 ▸ hK) (hc0 ▸ hS) (hc0 ▸ hp)
    (by simpa [negativeCurveB,hc0] using hB) hb hprime hn
  exact analytic_scalar_pullback_of_holomorphic_extension hc hc0 hext

end
end IsingBulk.Joint.Transverse
