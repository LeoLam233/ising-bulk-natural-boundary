import IsingBulk.First.RealFredholmIdentification
import IsingBulk.First.ExteriorIdentitySymmetry

/-! Source symmetry of the normalized susceptibility germ and its holomorphic
exterior continuation. The external representation is used only on real s > 1. -/
namespace IsingBulk.First
noncomputable section
open Set

/-- The actual near-infinity germ is constructed internally, together with
absolute convergence, holomorphy and the two source symmetries. -/
theorem normalizedBulkSeries_nearInfinity_source :
    AnalyticOnNhd ℂ (normalizedBulkSeries (1/4)) {s : ℂ | 16 < ‖s‖} ∧
    ∀ s : ℂ, 16 < ‖s‖ →
      Summable (fun n : ℕ => ‖doubleFormFactor (2*(n+1)) (1/4) s‖) ∧
      normalizedBulkSeries (1/4) (-s)=normalizedBulkSeries (1/4) s ∧
      normalizedBulkSeries (1/4) (star s)=star (normalizedBulkSeries (1/4) s) := by
  refine ⟨normalizedBulkSeries_quarter_analyticOn, ?_⟩
  intro s hs
  exact ⟨quarterEvenFormFactor_summable_norm hs, normalizedBulkSeries_even (1/4) s,
    normalizedBulkSeries_conjugate (1/4) (by linarith)⟩

/-- E1 identifies the real restriction of the genuine source germ; the result
does not assert existence of a holomorphic continuation on a larger domain. -/
theorem normalizedSusceptibility_real_germ (X : ℂ → ℂ)
    (hphysical : RealNormalizedFredholmRepresentation X) :
    (∀ x : ℝ, 16 < x → X (x:ℂ)=normalizedBulkSeries (1/4) (x:ℂ)) ∧
    AnalyticOnNhd ℂ (normalizedBulkSeries (1/4)) {s : ℂ | 16 < ‖s‖} :=
  ⟨realNormalizedFredholmRepresentation_quarter X hphysical,
    normalizedBulkSeries_quarter_analyticOn⟩

/-- Full source symmetry on the entire stated exterior domain. X is the
normalized susceptibility, beta_phys inverse times the thermodynamic response.
Its holomorphic continuation domain is explicit; no symmetry is a premise. -/
theorem lemma_symmetry_exterior (X : ℂ → ℂ)
    (hX : AnalyticOnNhd ℂ X {s : ℂ | 1 < ‖s‖})
    (hphysical : RealNormalizedFredholmRepresentation X) :
    (∀ s : ℂ, 1 < ‖s‖ → X (-s)=X s ∧ X (star s)=star (X s)) ∧
    ∀ N : ℕ, Even N → ∀ r : ℝ, ∀ s : ℂ,
      doubleFormFactor N r (-s)=doubleFormFactor N r s ∧
      doubleFormFactor N r (star s)=star (doubleFormFactor N r s) := by
  have h := exterior_symmetry_from_real_near_infinity X (normalizedBulkSeries (1/4))
    hX normalizedBulkSeries_quarter_analyticOn
    (realNormalizedFredholmRepresentation_quarter X hphysical)
    (fun s _ => normalizedBulkSeries_even (1/4) s)
    (fun _ hs => normalizedBulkSeries_conjugate (1/4) (by linarith))
  refine ⟨h.2, ?_⟩
  intro N hN r s
  exact ⟨doubleFormFactor_even N hN r s, doubleFormFactor_conjugate N r s⟩

end
end IsingBulk.First
