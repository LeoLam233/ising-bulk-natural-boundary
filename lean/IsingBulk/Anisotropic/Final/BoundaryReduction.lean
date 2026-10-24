import IsingBulk.Anisotropic.Final.FullConjugation
import IsingBulk.Anisotropic.Final.FullAxisExchange
import IsingBulk.Anisotropic.Final.LocalPullback
import IsingBulk.Anisotropic.Geometry.PrimeOrientation

namespace IsingBulk.Anisotropic
noncomputable section
open Set FormFactors

theorem no_domain_extension_conjugate {D : Set ℂ} {f : ℂ → ℂ} {z : ℂ}
    (hD : ∀ w, star w∈D ↔ w∈D) (hf : ∀ w∈D, star (f (star w))=f w)
    (hn : ¬HasDomainExtension D f (star z)) : ¬HasDomainExtension D f z := by
  intro he
  apply hn
  exact domain_extension_of_conjugate hD hf (by simpa only [star_star] using he)

theorem no_domain_extension_real_scaling {D E : Set ℂ} {f g : ℂ → ℂ}
    {lam : ℝ} (hlam : lam≠0) {z : ℂ}
    (hD : ∀ w, (lam:ℂ)*w∈E ↔ w∈D) (hf : ∀ w∈D, f ((lam:ℂ)*w)=g w)
    (hn : ¬HasDomainExtension E f ((lam:ℂ)*z)) : ¬HasDomainExtension D g z := by
  have hd : deriv (fun w : ℂ => (lam:ℂ)*w) z≠0 := by
    have hder : HasDerivAt (fun w : ℂ => (lam:ℂ)*w) (lam:ℂ) z := by
      simpa only [id_eq,mul_one] using (hasDerivAt_id z).const_mul (lam:ℂ)
    rw [hder.deriv]
    exact Complex.ofReal_ne_zero.mpr hlam
  have hh : ¬HasDomainExtension ((fun w : ℂ => (lam:ℂ)*w) ⁻¹' E)
      (f ∘ (fun w : ℂ => (lam:ℂ)*w)) z :=
    no_domain_extension_preimage (analyticAt_const.mul analyticAt_id) hd hn
  have hset : (fun w : ℂ => (lam:ℂ)*w) ⁻¹' E=D := Set.ext hD
  rw [hset] at hh
  exact no_domain_extension_of_eqOn (fun w hw => hf w hw) hh

/-- Pure transport of genuine obstructions. The oriented endpoint hypothesis is
not a final theorem assumption: it is discharged by the actual endpoint proofs. -/
theorem prime_no_extension_of_oriented_V (D : ℝ → Set ℂ) (F : ℝ → ℂ → ℂ)
    (haxisD : ∀ lam, 0<lam → ∀ w, (lam:ℂ)*w∈D (lam⁻¹) ↔ w∈D lam)
    (haxisB : ∀ lam, 0<lam → ∀ w, (lam:ℂ)*w∈frontier (D (lam⁻¹)) ↔ w∈frontier (D lam))
    (haxisF : ∀ lam, 0<lam → ∀ w∈D lam, F (lam⁻¹) ((lam:ℂ)*w)=F lam w)
    (hV : ∀ lam, 0<lam → ∀ w∈frontier (D lam), OrientedPrimeVEdge lam w →
      ¬HasDomainExtension (D lam) (F lam) w)
    {lam : ℝ} (hlam : 0<lam)
    (hconjD : ∀ w, star w∈D lam ↔ w∈D lam)
    (hconjB : ∀ w, star w∈frontier (D lam) ↔ w∈frontier (D lam))
    (hconjF : EqOn (fun w => star (F lam (star w))) (F lam) (D lam))
    {z : ℂ} (hz : z∈frontier (D lam)) (hp : PrimeRegularEdgePoint lam z) :
    ¬HasDomainExtension (D lam) (F lam) z := by
  have hs (w : ℂ) (hw : w∈frontier (D lam))
      (he : OrientedPrimeVEdge (lam⁻¹) ((lam:ℂ)*w)) :
      ¬HasDomainExtension (D lam) (F lam) w := by
    exact no_domain_extension_real_scaling hlam.ne' (haxisD lam hlam) (haxisF lam hlam)
      (hV (lam⁻¹) (inv_pos.mpr hlam) _ ((haxisB lam hlam w).mpr hw) he)
  rcases prime_regular_orientation hlam hp with h | h | h | h
  · exact hV lam hlam z hz h
  · exact no_domain_extension_conjugate hconjD (fun w hw => hconjF hw)
      (hV lam hlam (star z) ((hconjB z).mpr hz) h)
  · exact hs z hz h
  · exact no_domain_extension_conjugate hconjD (fun w hw => hconjF hw)
      (hs (star z) ((hconjB z).mpr hz) h)

theorem high_prime_no_extension_of_oriented
    (hV : ∀ lam, 0<lam → ∀ w∈frontier (omegaH lam), OrientedPrimeVEdge lam w →
      ¬HasDomainExtension (omegaH lam) (highNormalizedBulk lam) w)
    {lam : ℝ} (hlam : 0<lam) {corrH corrL : ℝ → LatticeSite → ℝ}
    (hphys : PublishedRealSpinFormFactors lam corrH corrL)
    {z : ℂ} (hz : z∈frontier (omegaH lam)) (hp : PrimeRegularEdgePoint lam z) :
    ¬HasDomainExtension (omegaH lam) (highNormalizedBulk lam) z :=
  prime_no_extension_of_oriented_V omegaH highNormalizedBulk
    (fun _ h => omegaH_axis_exchange_iff h) (fun _ h => frontier_omegaH_axis_exchange_iff h)
    (fun _ h _ hz => highNormalizedBulk_axis_exchange h hz) hV hlam
    (omegaH_conj_iff lam) (frontier_omegaH_conj_iff lam)
    (highNormalizedBulk_conjugate hlam hphys) hz hp

theorem low_prime_no_extension_of_oriented
    (hV : ∀ lam, 0<lam → ∀ w∈frontier (omegaL lam), OrientedPrimeVEdge lam w →
      ¬HasDomainExtension (omegaL lam) (lowNormalizedBulk lam) w)
    {lam : ℝ} (hlam : 0<lam) {corrH corrL : ℝ → LatticeSite → ℝ}
    (hphys : PublishedRealSpinFormFactors lam corrH corrL)
    {z : ℂ} (hz : z∈frontier (omegaL lam)) (hp : PrimeRegularEdgePoint lam z) :
    ¬HasDomainExtension (omegaL lam) (lowNormalizedBulk lam) z :=
  prime_no_extension_of_oriented_V omegaL lowNormalizedBulk
    (fun _ h => omegaL_axis_exchange_iff h) (fun _ h => frontier_omegaL_axis_exchange_iff h)
    (fun _ h _ hz => lowNormalizedBulk_axis_exchange h hz) hV hlam
    (omegaL_conj_iff lam) (frontier_omegaL_conj_iff lam)
    (lowNormalizedBulk_conjugate hlam hphys) hz hp

end
end IsingBulk.Anisotropic
