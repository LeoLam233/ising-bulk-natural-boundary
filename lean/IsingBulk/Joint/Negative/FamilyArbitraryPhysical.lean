import IsingBulk.Joint.Transverse.FamilyNormalizationAttachment
import IsingBulk.Joint.Transverse.FamilyEstimateStatements

/-! Arbitrary nonramified negative-odd families are normalized jointly, then
receive the actual complete obstruction and literal physical mixed tails.
No square-root family, exact normalization, or estimate is an input. -/
namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter Metric Transverse IsingBulk.Anisotropic
open scoped Topology
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- The negative edge coordinate is analytic jointly in all family variables. -/
theorem negative_edge_family_analyticAt {curve : E→Coupling} {q : E} (b : ℂ)
    (hc : AnalyticAt ℂ curve q) (hS : S (curve q)≠0) (hB : transferB (curve q)≠0) :
    AnalyticAt ℂ (fun q=>edgeParameter b (curve q)) q := by
  have hCa := (transferC_analyticAt hS).comp hc
  have hBa := (transferB_analyticAt hS).comp hc
  exact ((hCa.add hBa).sub analyticAt_const).div hBa hB

/-- Construct the common product chart before choosing ANY compact admissible
subfamily. The result retains exact recovery of the original family and every
complete negative-odd physical estimate. -/
theorem arbitrary_negative_high_family_estimates {b : ℝ} (curve : ℂ × E→Coupling) {eta₀ : E}
    (hc₀ : AnalyticAt ℂ curve (0,eta₀)) (hS₀ : S (curve (0,eta₀))≠0)
    (hB₀ : (transferB (curve (0,eta₀))).im<0)
    (hprime : b∈primePhaseCosines)
    (he₀ : edgeParameter b (curve (0,eta₀))=0)
    (hd₀ : deriv (fun z=>edgeParameter b (curve (z,eta₀))) 0≠0) :
    ∃N : FamilyNormalization (fun q=>edgeParameter b (curve q)) eta₀,
      (∀z eta, ‖z‖<N.radius → ‖eta-eta₀‖<N.radius →
        N.normalizedFamily curve (edgeParameter b (curve (z,eta)),eta)=curve (z,eta)) ∧
      ∀Q : Set E, IsCompact Q → Q⊆ball eta₀ N.radius →
        (∀eta∈Q,edgeParameter b (curve (0,eta))=0) →
        (∀eta∈Q,curve (0,eta)∈frontier highDomain) →
        (∀eta∈Q,S (curve (0,eta))≠0) →
        (∀eta∈Q,p (curve (0,eta))^2≠1) →
        (∀eta∈Q,(transferB (curve (0,eta))).im<0) →
        NegativeHighFamilyEstimates (N.normalizedFamily curve) Q := by
  have hf := negative_edge_family_analyticAt (E:=ℂ × E) b hc₀ hS₀
    (transferB_ne_zero_of_im_neg hB₀)
  obtain ⟨N,hcenters⟩ := exists_familyNormalization_with_analytic_centers curve hc₀ hf he₀ hd₀
  refine ⟨N,fun z eta hz heta=>N.original_recovered curve hz heta,?_⟩
  intro Q hQ hQN he hK hS hp hB
  let c := N.normalizedFamily curve
  have hnorm (eta : E) (heta : eta∈Q) : ‖eta-eta₀‖<N.radius := by
    simpa only [mem_ball,dist_eq_norm] using hQN heta
  have hc0 (eta : E) (heta : eta∈Q) : c (0,eta)=curve (0,eta) :=
    N.normalized_center curve (hnorm eta heta) (he eta heta)
  have hc (eta : E) (heta : eta∈Q) : AnalyticAt ℂ c (0,eta) :=
    N.normalized_analyticAt_center curve (hnorm eta heta) (he eta heta)
      (hcenters eta (hnorm eta heta))
  have hSc (eta : E) (heta : eta∈Q) : S (c (0,eta))≠0 := by rw [hc0 eta heta]; exact hS eta heta
  have hBc (eta : E) (heta : eta∈Q) : (transferB (c (0,eta))).im<0 := by rw [hc0 eta heta]; exact hB eta heta
  have hKc (eta : E) (heta : eta∈Q) : c (0,eta)∈frontier highDomain := by rw [hc0 eta heta]; exact hK eta heta
  have hpc (eta : E) (heta : eta∈Q) : p (c (0,eta))^2≠1 := by rw [hc0 eta heta]; exact hp eta heta
  have hchart (eta : E) (heta : eta∈Q) :
      ∀ᶠt : ℂ in 𝓝 0,transferC (c (t,eta))+transferB (c (t,eta))=
        (b:ℂ)+transferB (c (t,eta))*t := by
    have hba : AnalyticAt ℂ (fun t : ℂ=>transferB (c (t,eta))) 0 :=
      ((transferB_analyticAt (hSc eta heta)).comp (hc eta heta)).comp
        (f:=fun t : ℂ=>(t,eta)) (analyticAt_id.prod analyticAt_const)
    filter_upwards [N.right_inv_germ (hnorm eta heta),
      hba.continuousAt.eventually_ne (transferB_ne_zero_of_im_neg (hBc eta heta))] with t ht hBt
    have hh := edgeParameter_identity b (c (t,eta)) hBt
    change edgeParameter b (c (t,eta))=t at ht
    rwa [ht] at hh
  have ha (eta : E) (heta : eta∈Q) :
      AnalyticAt ℂ (fun q=>negativeEvenParticleRoot (c q)) (0,eta) :=
    negativeEvenParticleRoot_family_analyticAt (hc eta heta) (hSc eta heta)
      (by simpa only [Complex.neg_im,neg_pos] using hBc eta heta)
  refine ⟨compact_negative_high_physical_obstruction c (fun q=>negativeEvenParticleRoot (c q))
    hQ hc ha hSc hBc hKc hpc hprime hchart (fun eta heta=>Eventually.of_forall
      (fun t=>negativeEvenParticleRoot_sq (c (t,eta)))),?_⟩
  exact compact_negative_high_physical_mixed_tails_on_common_tube c
    (abs_lt_one_of_primePhaseCosines hprime) hQ hc hKc hpc hSc hBc hchart

end
end IsingBulk.Joint.Negative
