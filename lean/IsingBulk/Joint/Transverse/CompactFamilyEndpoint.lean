import IsingBulk.Joint.Transverse.AllOrientations
import IsingBulk.Joint.RegularEdges.IndependentCoefficientJets

/-! # Regular-edge transverse and compact-family endpoint
The two claims are separate and both proved: every genuine transverse curve
obstructs the complete physical sum, while every compact admissible complex
parameter family has a common polydisk controlling all mixed complete jets.
The finite low-particle block is explicitly retained in the decomposition.
-/
namespace IsingBulk.Joint.Transverse
noncomputable section
open Set Metric RegularEdges
open scoped BigOperators

/-- Literal all-curve obstruction with independent compact-family control.
The proof of the first conjunct includes the nonzero leading singular term,
all finite competing orders, and the infinite tail; the second conjunct does
not purport to replace that noncancellation argument. -/
theorem joint_transverse_compact_family_endpoint
    {corrH corrL : PhysicalField.CorrelationFamily}
    (hphys : PhysicalField.PublishedRealSpinFamily corrH corrL) :
    (∀ (c : ℂ→Coupling) (z : ℂ), AnalyticAt ℂ c z → IsPrimeRegularJointEdge (c z) →
      IsNonramifiedJointTransversal c z →
      (c z∈frontier highDomain →
        ¬HasHolomorphicFullExtension (c ⁻¹' highDomain) (FormFactors.highNormalizedBulk∘c) z) ∧
      (c z∈frontier lowDomain →
        ¬HasHolomorphicFullExtension (c ⁻¹' lowDomain) (FormFactors.lowNormalizedBulk∘c) z)) ∧
    (∀ (b : ℝ) (K : Set (ℂ × ℂ)), |b|<1 → IsCompact K →
      (∀ v∈K, 0<v.1.im) → (∀ v∈K, v.2≠0) →
      ∃ δ : ℝ, 0<δ ∧ ∀ j : ℕ, ∃ G : ℕ→ℝ,
        Summable G ∧ (∀ k, 0≤G k) ∧
        ∀ v∈K, ∀ x∈ball ((0:ℂ),v) δ, 0<x.1.im →
        Summable (fun n => iteratedFDeriv ℂ j (independentAngularCoefficient n b) x) ∧
        (∑' n, iteratedFDeriv ℂ j (independentAngularCoefficient n b) x)=
          (∑ n∈Finset.range (2*j+3), iteratedFDeriv ℂ j (independentAngularCoefficient n b) x)+
          ∑' k, iteratedFDeriv ℂ j (independentAngularCoefficient (2*j+3+k) b) x ∧
        ∀ k, ‖iteratedFDeriv ℂ j (independentAngularCoefficient (2*j+3+k) b) x‖≤G k) := by
  constructor
  · intro c z hc hr ht
    exact ⟨fun hK => prime_regular_high_curve_no_holomorphic_extension hphys hc hK hr ht,
      fun hK => prime_regular_low_curve_no_holomorphic_extension hphys hc hK hr ht⟩
  · intro b K hb hK hB hS
    exact compact_actual_jets_finite_tail_split hb hK hB hS

end
end IsingBulk.Joint.Transverse
