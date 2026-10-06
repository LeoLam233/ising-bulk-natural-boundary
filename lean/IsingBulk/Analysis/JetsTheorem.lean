import IsingBulk.Analysis.JetsAllOrder
import IsingBulk.Analysis.JetsUniform

/-! Source-facing unfactored jet filtration. The result uses one and the same
semantic list for the actual iterate, term shapes, poles, estimates and count. -/
namespace IsingBulk.Jets
noncomputable section
open IsingBulk.Lie
open scoped ContDiff

theorem distinct_pair_dimension {N : ℕ} (p q : Fin N) (hpq : p ≠ q) : 2 ≤ N := by
  by_contra hN
  apply hpq
  apply Fin.ext
  have hp := p.isLt
  have hq := q.isLt
  omega

theorem SourceJetTerm.source_unfactored {n : ℕ} (T : SourceJetTerm (n+1))
    (p q : Fin (n+1)) (v θ : ℝ) (w : AngularSpace n → ℝ)
    (A : ℂ × (Fin (n+1) → ℂ) → ℂ) (s : ℂ) (x : AngularSpace n)
    (hA : AnalyticAt ℂ A (s,chartMap v θ s x)) :
    T.sourceValue p q v θ w (unfactoredNumerator A) s x =
      (cutoffJet T.cutoff w x:ℂ)*chartJacobian v θ s x*
        (T.coefficient p q (s,chartMap v θ s x)*
          numeratorJet (List.replicate (parameterOrder T.numerator) none ++
            (spatialWord T.numerator).map some) (unfactoredNumerator A) (s,chartMap v θ s x)/
          regularKernel s (chartMap v θ s x)) := by
  rw [T.sourceValue_eq]
  unfold SourceJetTerm.value
  rw [T.unfactored_density p q A _ hA]
  ring

/-- This is a conclusion bundle, constructed below from the preceding chart
calculus. None of its fields is an assumption of the source-facing theorem. -/
structure SourceJetExpansion {n : ℕ} (p q : Fin (n+1)) (j r C : ℕ)
    (U : Set (ℂ × ℂ)) (P : Set (ℂ × ℂ × ℂ)) : Prop where
  count : (sourceJetTerms p q j).length ≤ C*(n+1)^C
  filtration : ∀ T ∈ sourceJetTerms p q j,
    T.pole+T.cutoff.length+(spatialWord T.numerator).length ≤ 2*j ∧
    parameterOrder T.numerator+T.cutoff.length+(spatialWord T.numerator).length ≤ j
  regular_coefficients : ∀ z : ℂ × (Fin (n+1) → ℂ),
    (∀ i, (z.1,z.2 i) ∈ U) → (z.1,z.2 p,z.2 q) ∈ P →
      CoefficientPoint p q z ∧ ∀ T ∈ sourceJetTerms p q j,
        JetBound T.regularPart z r ((C:ℝ)*(n+1)^C)
  pole_certificate : ∀ T ∈ sourceJetTerms p q j, ∀ z : ℂ × (Fin (n+1) → ℂ),
    z.2 q-z.2 p ≠ 0 → (z.2 q-z.2 p)^T.pole*T.coefficient p q z = T.regularPart z
  source_form : ∀ T ∈ sourceJetTerms p q j, ∀ (v θ : ℝ) (w : AngularSpace n → ℝ)
    (A : ℂ × (Fin (n+1) → ℂ) → ℂ) (s : ℂ) (x : AngularSpace n),
    AnalyticAt ℂ A (s,chartMap v θ s x) →
    T.sourceValue p q v θ w (unfactoredNumerator A) s x =
      (cutoffJet T.cutoff w x:ℂ)*chartJacobian v θ s x*
        (T.coefficient p q (s,chartMap v θ s x)*
          numeratorJet (List.replicate (parameterOrder T.numerator) none ++
            (spatialWord T.numerator).map some) (unfactoredNumerator A) (s,chartMap v θ s x)/
          regularKernel s (chartMap v θ s x))
  actual_iteration : ∀ (v θ : ℝ) (w : AngularSpace n → ℝ)
    (A : ℂ × (Fin (n+1) → ℂ) → ℂ) (S : Set ℂ) (R : Set (AngularSpace n)),
    IsOpen S → IsOpen R → ContDiff ℝ ∞ w →
    (∀ s ∈ S, ∀ x ∈ R, ActualJetPoint v θ p q s x) →
    (∀ s ∈ S, ∀ x ∈ R, AnalyticAt ℂ A (s,chartMap v θ s x)) →
    ∀ s ∈ S, ∀ x ∈ R,
      ((lieStep (actualField v θ p q))^[j]
        (initialSourceDensity v θ w (unfactoredNumerator A))) s x =
      ((sourceJetTerms p q j).map
        (fun T => T.sourceValue p q v θ w (unfactoredNumerator A) s x)).sum

/-- Appendix D, lem:jets. The base data and finite orders precede the scalar
and selected-pair neighborhoods and the one source constant. Every selected
pair is distinct. Actual fractions are used only on an open regular chart;
the coefficient estimate includes the diagonal in the fixed base neighborhood. -/
theorem lemma_jets (s : ℂ) (c : ℝ) (hs : s ≠ 0)
    (hS : s+s⁻¹ = (1+c:ℂ)) (hc : |c| < 1) (j r : ℕ) :
    ∃ C : ℕ, 0 < C ∧ ∃ U : Set (ℂ × ℂ), ∃ P : Set (ℂ × ℂ × ℂ),
      IsOpen U ∧ (s,0) ∈ U ∧ IsOpen P ∧ (s,0,0) ∈ P ∧
      ∀ n : ℕ, ∀ p q : Fin (n+1), p ≠ q → SourceJetExpansion p q j r C U P := by
  obtain ⟨C,hC,U,P,hU,hsU,hP,hsP,h⟩ := sourceJetTerms_uniform s c hs hS hc j r
  refine ⟨C,hC,U,P,hU,hsU,hP,hsP,?_⟩
  intro n p q hpq
  obtain ⟨hcount,hcoeff⟩ := h (n+1) (by omega) p q hpq
  refine ⟨hcount,sourceJetTerms_valid p q j,?_,?_,?_,?_⟩
  · simpa only [Nat.cast_add,Nat.cast_one] using hcoeff
  · exact fun T _ z hz => T.cleared_coefficient p q z hz
  · exact fun T _ v θ w A s x hA => T.source_unfactored p q v θ w A s x hA
  · exact fun v θ w A S R hS hR hw hchart hA =>
      sourceJetTerms_all_order p q hpq v θ w A S R hS hR hw hchart hA j

end
end IsingBulk.Jets
