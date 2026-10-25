import IsingBulk.Joint.Negative.FamilyInteriorMixedTails
import IsingBulk.Joint.Negative.FamilyPhysicalSum
import IsingBulk.Joint.Transverse.FamilyIndependentIdentity

/-! # Literal negative HT particle tails in all ambient mixed directions -/
namespace IsingBulk.Joint.Negative
noncomputable section
open IsingBulk.Joint.Transverse IsingBulk.Joint.RegularEdges Set Filter Metric
open scoped Topology

def negativeHighMultiplier (K : Coupling) : ℂ :=
  FormFactors.highPrefactor K/negativeEvenParticleRoot K

theorem negative_highFullParticle_continued (m : ℕ) {b : ℝ} {K : Coupling}
    (hK : K∈highDomain) (hS : S K≠0) (hB : 0<(-transferB K).im)
    (hi : 0<(transferC K+transferB K-(b:ℂ)).im) :
    highFullParticle m K=negativeHighMultiplier K*
      (negativeEvenParticleRoot K^(2*m+1)*continuedAngularCoefficient (2*m) K) := by
  rw [←negative_high_weighted_particle_eq m hK hS
    (by simpa only [Complex.neg_im,neg_pos] using hB) hi (negativeEvenParticleRoot_sq K)]
  unfold highFullParticle negativeHighMultiplier
  field_simp [negativeEvenParticleRoot_ne_zero hS hB]

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The physical side is an evaluation condition, not an ambient derivative
oracle. The identity is differentiated only after obtaining an OPEN physical
germ. Canonical root square identities hold in every ambient parameter direction. -/
theorem compact_negative_high_physical_mixed_tails {b : ℝ} (curve : ℂ × E→Coupling)
    {Q : Set E} (hb : |b|<1) (hQ : IsCompact Q)
    (hc : ∀eta∈Q,AnalyticAt ℂ curve (0,eta))
    (hK : ∀eta∈Q,curve (0,eta)∈closure highDomain)
    (hp : ∀eta∈Q,p (curve (0,eta))^2≠1)
    (hS : ∀eta∈Q,S (curve (0,eta))≠0)
    (hB : ∀eta∈Q,0<(-transferB (curve (0,eta))).im)
    (he : ∀eta∈Q,A (curve (0,eta))+T (curve (0,eta))=(b:ℂ)*S (curve (0,eta))) :
    ∃δ : ℝ,0<δ ∧ ∀j : ℕ,∃G : ℕ→ℝ,Summable G ∧ (∀k,0≤G k) ∧
      ∀eta∈Q,∀u : ℂ,‖u‖<δ → curve (u,eta)∈highDomain →
        0<(transferC (curve (u,eta))+transferB (curve (u,eta))-(b:ℂ)).im → ∀k : ℕ,
      ‖iteratedFDeriv ℂ j (fun q=>highFullParticle (j+2+k) (curve q)) (u,eta)‖≤G k := by
  have hR : ∀eta∈Q,AnalyticAt ℂ (fun q=>negativeEvenParticleRoot (curve q)) (0,eta) :=
    fun eta heta=>negativeEvenParticleRoot_family_analyticAt (hc eta heta) (hS eta heta) (hB eta heta)
  have hR0 : ∀eta∈Q,negativeEvenParticleRoot (curve (0,eta))≠0 :=
    fun eta heta=>negativeEvenParticleRoot_ne_zero (hS eta heta) (hB eta heta)
  have hW : ∀eta∈Q,AnalyticAt ℂ (fun q=>negativeHighMultiplier (curve q)) (0,eta) :=
    fun eta heta=>((highPrefactor_boundary_analyticAt (hK eta heta) (hp eta heta)).comp
      (hc eta heta)).div (hR eta heta) (hR0 eta heta)
  obtain ⟨d,hd,hjets⟩ := compact_actual_negative_interior_mixed_tails curve
    (fun q=>negativeEvenParticleRoot (curve q)) (fun q=>negativeHighMultiplier (curve q))
    hb hQ hc hR hW hS hR0 he (by simpa only [neg_div,transferB] using hB)
  let U : Set (ℂ × E) := {q | AnalyticAt ℂ curve q ∧ S (curve q)≠0 ∧ 0<(-transferB (curve q)).im}
  have hU : IsOpen U := by
    rw [isOpen_iff_mem_nhds]
    intro q hq
    have hsi : ContinuousAt (fun q=>S (curve q)) q :=
      Complex.continuous_sinh.continuousAt.comp hq.1.continuousAt.fst
    exact hq.1.eventually_analyticAt.and (hsi.eventually_ne hq.2.1 |>.and
      (continuousAt_const.eventually_lt (Complex.continuous_im.continuousAt.comp
        (transferB_family_analyticAt hq.1 hq.2.1).continuousAt.neg) hq.2.2))
  obtain ⟨r,hr,htube⟩ := compact_product_tube hQ hU (fun eta heta=>⟨hc eta heta,hS eta heta,hB eta heta⟩)
  refine ⟨min r d,lt_min hr hd,?_⟩
  intro j
  obtain ⟨G,hG,hG0,hbound⟩ := hjets j
  refine ⟨fun k=>G (1+2*k),hG.comp_injective (by intro x y h; dsimp at h; omega),fun k=>hG0 _,?_⟩
  intro eta heta u hu hKu hi k
  have ht := htube eta heta u (hu.trans_le (min_le_left _ _))
  have hpa := negativeEvenPhysicalParameter_family_analyticAt b ht.1 ht.2.1 ht.2.2
  have hsi : ContinuousAt (fun q=>S (curve q)) (u,eta) :=
    Complex.continuous_sinh.continuousAt.comp ht.1.continuousAt.fst
  have heq : (fun q=>highFullParticle (j+2+k) (curve q)) =ᶠ[𝓝 (u,eta)]
      (fun q=>negativeHighMultiplier (curve q)*(negativeEvenParticleRoot (curve q)^(2*(j+2+k)+1)*
        continuedAngularCoefficient (2*(j+2+k)) (curve q))) := by
    filter_upwards [ht.1.continuousAt.preimage_mem_nhds (highDomain_isOpen.mem_nhds hKu),
      hsi.eventually_ne ht.2.1,
      continuousAt_const.eventually_lt (Complex.continuous_im.continuousAt.comp hpa.continuousAt.snd.fst) ht.2.2,
      continuousAt_const.eventually_lt (Complex.continuous_im.continuousAt.comp hpa.continuousAt.fst) hi]
      with q hq hs hb' hi'
    exact negative_highFullParticle_continued _ hq hs hb' hi'
  rw [(heq.iteratedFDeriv ℂ j).eq_of_nhds]
  have hh := hbound eta heta u (hu.trans_le (min_le_right _ _)) hi (1+2*k)
  simpa only [show 2*j+3+(1+2*k)=2*(j+2+k) by omega] using hh

/-- Normalized negative families have a derived common physical side and the
literal HT mixed tails there. No physical membership premise remains. -/
theorem compact_negative_high_physical_mixed_tails_on_common_tube {b : ℝ}
    (curve : ℂ × E→Coupling) {Q : Set E} (hb : |b|<1) (hQ : IsCompact Q)
    (hc : ∀eta∈Q,AnalyticAt ℂ curve (0,eta))
    (hK : ∀eta∈Q,curve (0,eta)∈frontier highDomain)
    (hp : ∀eta∈Q,p (curve (0,eta))^2≠1)
    (hS : ∀eta∈Q,S (curve (0,eta))≠0)
    (hB : ∀eta∈Q,(transferB (curve (0,eta))).im<0)
    (he : ∀eta∈Q,∀ᶠt : ℂ in 𝓝 0,transferC (curve (t,eta))+transferB (curve (t,eta))=
      (b:ℂ)+transferB (curve (t,eta))*t) :
    ∃δ : ℝ,0<δ ∧
      (∀eta∈Q,∀u : ℂ,‖u‖<δ →
        (curve (u,eta)∈highDomain ↔ 0<(transferB (curve (u,eta))*u).im)) ∧
      ∀j : ℕ,∃G : ℕ→ℝ,Summable G ∧ (∀k,0≤G k) ∧
      ∀eta∈Q,∀u : ℂ,‖u‖<δ → 0<(transferB (curve (u,eta))*u).im → ∀k : ℕ,
      ‖iteratedFDeriv ℂ j (fun q=>highFullParticle (j+2+k) (curve q)) (u,eta)‖≤G k := by
  have hedge (eta : E) (heta : eta∈Q) : A (curve (0,eta))+T (curve (0,eta))=(b:ℂ)*S (curve (0,eta)) := by
    have hh := Filter.EventuallyEq.eq_of_nhds (he eta heta)
    simp only [mul_zero,add_zero,transferC,transferB] at hh
    rw [←add_div] at hh
    exact (div_eq_iff (hS eta heta)).mp hh
  obtain ⟨d,hd,hjets⟩ := compact_negative_high_physical_mixed_tails curve hb hQ hc
    (fun eta heta=>(hK eta heta).1) hp hS
    (by simpa only [Complex.neg_im,neg_pos] using hB) hedge
  obtain ⟨r,hr,htube⟩ := compact_negative_high_tube curve hQ hc hS hB hK hp hb he
  refine ⟨min r d,lt_min hr hd,?_,?_⟩
  · intro eta heta u hu
    exact (htube eta heta u (hu.trans_le (min_le_left _ _))).2.2.2.2
  · intro j
    obtain ⟨G,hG,hG0,hbound⟩ := hjets j
    refine ⟨G,hG,hG0,?_⟩
    intro eta heta u hu hi k
    have ht := htube eta heta u (hu.trans_le (min_le_left _ _))
    apply hbound eta heta u (hu.trans_le (min_le_right _ _)) (ht.2.2.2.2.mpr hi) _ k
    rw [ht.2.2.2.1,add_sub_cancel_left]
    exact hi

end
end IsingBulk.Joint.Negative
