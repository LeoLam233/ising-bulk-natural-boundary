import IsingBulk.Joint.Transverse.FamilyNormalizationAttachment
import IsingBulk.Joint.Transverse.FamilyEstimateStatements

/-! # Arbitrary nonramified families, with normalization constructed internally

The original family need not be in edge coordinates. One jointly analytic,
parameter-preserving inverse is constructed on an actual common polydisk, with
both inverse identities. Every compact admissible family in that parameter disk
then has the complete physical estimates after this proved coordinate change.
-/
namespace IsingBulk.Joint.Transverse
noncomputable section
open IsingBulk.Anisotropic Set Filter Metric
open scoped Topology
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- Complete estimates for arbitrary nonramified original families. The
normalization, common polydisk and original-family recovery are constructed,
not hypotheses. All compact admissible parameter subsets share that inverse. -/
theorem positive_high_arbitrary_family_quantitative {b : ℝ} (curve : ℂ × E→Coupling)
    {eta₀ : E} (hc : AnalyticAt ℂ curve (0,eta₀)) (hS₀ : S (curve (0,eta₀))≠0)
    (hB₀ : 0<(transferB (curve (0,eta₀))).im)
    (hzero : positiveParameter b (curve (0,eta₀))=0)
    (hd : deriv (fun z=>positiveParameter b (curve (z,eta₀))) 0≠0)
    (hb : |b|<1) (hprime : b∈primePhaseCosines) :
    ∃N : FamilyNormalization (fun q=>positiveParameter b (curve q)) eta₀,
      (∀z eta,‖z‖<N.radius → ‖eta-eta₀‖<N.radius →
        N.normalizedFamily curve (positiveParameter b (curve (z,eta)),eta)=curve (z,eta)) ∧
      ∀Q : Set E,IsCompact Q → (∀eta∈Q,‖eta-eta₀‖<N.radius) →
      (∀eta∈Q,curve (0,eta)∈frontier highDomain) →
      (∀eta∈Q,S (curve (0,eta))≠0) → (∀eta∈Q,p (curve (0,eta))^2≠1) →
      (∀eta∈Q,0<(transferB (curve (0,eta))).im) →
      (∀eta∈Q,positiveParameter b (curve (0,eta))=0) →
      PositiveHighFamilyEstimates b (N.normalizedFamily curve) Q := by
  have hf : AnalyticAt ℂ (fun q=>positiveParameter b (curve q)) (0,eta₀) :=
    analyticAt_fst.comp (positivePhysicalParameter_family_analyticAt b hc hS₀ hB₀)
  obtain ⟨N,hca⟩ := exists_familyNormalization_with_analytic_centers curve hc hf hzero hd
  refine ⟨N,?_,?_⟩
  · intro z eta hz heta
    exact N.original_recovered curve hz heta
  intro Q hQ hQN hK hS hp hB hz
  have he (eta : E) (heta : eta∈Q) := N.normalized_center curve (hQN eta heta) (hz eta heta)
  apply positive_high_normalized_family_estimates (N.normalizedFamily curve) hQ
    (fun eta heta=>N.normalized_analyticAt_center curve (hQN eta heta) (hz eta heta) (hca eta (hQN eta heta)))
    (fun eta heta=>by rw [he eta heta]; exact hK eta heta)
    (fun eta heta=>by rw [he eta heta]; exact hS eta heta)
    (fun eta heta=>by rw [he eta heta]; exact hp eta heta)
    (fun eta heta=>by rw [he eta heta]; exact hB eta heta) hb hprime
  intro eta heta
  exact N.right_inv_germ (hQN eta heta)

/-- Complete estimates for arbitrary nonramified original families. The
normalization, common polydisk and original-family recovery are constructed,
not hypotheses. All compact admissible parameter subsets share that inverse. -/
theorem positive_low_arbitrary_family_quantitative {b : ℝ} (curve : ℂ × E→Coupling)
    {eta₀ : E} (hc : AnalyticAt ℂ curve (0,eta₀)) (hS₀ : S (curve (0,eta₀))≠0)
    (hB₀ : 0<(transferB (curve (0,eta₀))).im)
    (hzero : positiveParameter b (curve (0,eta₀))=0)
    (hd : deriv (fun z=>positiveParameter b (curve (z,eta₀))) 0≠0)
    (hb : |b|<1) (hprime : b∈primePhaseCosines) :
    ∃N : FamilyNormalization (fun q=>positiveParameter b (curve q)) eta₀,
      (∀z eta,‖z‖<N.radius → ‖eta-eta₀‖<N.radius →
        N.normalizedFamily curve (positiveParameter b (curve (z,eta)),eta)=curve (z,eta)) ∧
      ∀Q : Set E,IsCompact Q → (∀eta∈Q,‖eta-eta₀‖<N.radius) →
      (∀eta∈Q,curve (0,eta)∈frontier lowDomain) →
      (∀eta∈Q,S (curve (0,eta))≠0) → (∀eta∈Q,p (curve (0,eta))^2≠1) →
      (∀eta∈Q,0<(transferB (curve (0,eta))).im) →
      (∀eta∈Q,positiveParameter b (curve (0,eta))=0) →
      PositiveLowFamilyEstimates b (N.normalizedFamily curve) Q := by
  have hf : AnalyticAt ℂ (fun q=>positiveParameter b (curve q)) (0,eta₀) :=
    analyticAt_fst.comp (positivePhysicalParameter_family_analyticAt b hc hS₀ hB₀)
  obtain ⟨N,hca⟩ := exists_familyNormalization_with_analytic_centers curve hc hf hzero hd
  refine ⟨N,?_,?_⟩
  · intro z eta hz heta
    exact N.original_recovered curve hz heta
  intro Q hQ hQN hK hS hp hB hz
  have he (eta : E) (heta : eta∈Q) := N.normalized_center curve (hQN eta heta) (hz eta heta)
  apply positive_low_normalized_family_estimates (N.normalizedFamily curve) hQ
    (fun eta heta=>N.normalized_analyticAt_center curve (hQN eta heta) (hz eta heta) (hca eta (hQN eta heta)))
    (fun eta heta=>by rw [he eta heta]; exact hK eta heta)
    (fun eta heta=>by rw [he eta heta]; exact hS eta heta)
    (fun eta heta=>by rw [he eta heta]; exact hp eta heta)
    (fun eta heta=>by rw [he eta heta]; exact hB eta heta) hb hprime
  intro eta heta
  exact N.right_inv_germ (hQN eta heta)

/-- Complete estimates for arbitrary nonramified original families. The
normalization, common polydisk and original-family recovery are constructed,
not hypotheses. All compact admissible parameter subsets share that inverse. -/
theorem negative_even_low_arbitrary_family_quantitative {b : ℝ} (curve : ℂ × E→Coupling)
    {eta₀ : E} (hc : AnalyticAt ℂ curve (0,eta₀)) (hS₀ : S (curve (0,eta₀))≠0)
    (hB₀ : 0<(-transferB (curve (0,eta₀))).im)
    (hzero : negativeParameter b (curve (0,eta₀))=0)
    (hd : deriv (fun z=>negativeParameter b (curve (z,eta₀))) 0≠0)
    (hb : |b|<1) (hprime : b∈primePhaseCosines) :
    ∃N : FamilyNormalization (fun q=>negativeParameter b (curve q)) eta₀,
      (∀z eta,‖z‖<N.radius → ‖eta-eta₀‖<N.radius →
        N.normalizedFamily curve (negativeParameter b (curve (z,eta)),eta)=curve (z,eta)) ∧
      ∀Q : Set E,IsCompact Q → (∀eta∈Q,‖eta-eta₀‖<N.radius) →
      (∀eta∈Q,curve (0,eta)∈frontier lowDomain) →
      (∀eta∈Q,S (curve (0,eta))≠0) → (∀eta∈Q,p (curve (0,eta))^2≠1) →
      (∀eta∈Q,0<(-transferB (curve (0,eta))).im) →
      (∀eta∈Q,negativeParameter b (curve (0,eta))=0) →
      NegativeEvenLowFamilyEstimates b (N.normalizedFamily curve) Q := by
  have hf : AnalyticAt ℂ (fun q=>negativeParameter b (curve q)) (0,eta₀) :=
    analyticAt_fst.comp (negativeEvenPhysicalParameter_family_analyticAt b hc hS₀ hB₀)
  obtain ⟨N,hca⟩ := exists_familyNormalization_with_analytic_centers curve hc hf hzero hd
  refine ⟨N,?_,?_⟩
  · intro z eta hz heta
    exact N.original_recovered curve hz heta
  intro Q hQ hQN hK hS hp hB hz
  have he (eta : E) (heta : eta∈Q) := N.normalized_center curve (hQN eta heta) (hz eta heta)
  apply negative_even_low_normalized_family_estimates (N.normalizedFamily curve) hQ
    (fun eta heta=>N.normalized_analyticAt_center curve (hQN eta heta) (hz eta heta) (hca eta (hQN eta heta)))
    (fun eta heta=>by rw [he eta heta]; exact hK eta heta)
    (fun eta heta=>by rw [he eta heta]; exact hS eta heta)
    (fun eta heta=>by rw [he eta heta]; exact hp eta heta)
    (fun eta heta=>by rw [he eta heta]; exact hB eta heta) hb hprime
  intro eta heta
  exact N.right_inv_germ (hQN eta heta)

end
end IsingBulk.Joint.Transverse
