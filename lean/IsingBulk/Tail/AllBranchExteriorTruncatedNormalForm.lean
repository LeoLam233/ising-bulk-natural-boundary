import IsingBulk.Tail.AllBranchExteriorTruncatedIntegral
import IsingBulk.Tail.SourceJetNeighborhood

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Jets IsingBulk.Lie MeasureTheory Set Function
open scoped ContDiff

theorem allBranchExterior_sourceTerm_zero_off_support {n : ℕ} (T : SourceJetTerm (n+1))
    (p q : Fin (n+1)) (v θ : ℝ) (w : AngularSpace n → ℝ)
    (Q : ℂ × (Fin (n+1) → ℂ) → ℂ) (s : ℂ) (u : AngularSpace n) (hu : u ∉ tsupport w) :
    T.sourceValue p q v θ w Q s u=0 := by
  have hz : cutoffJet T.cutoff w u=0 := by
    by_contra hn
    exact hu (cutoffJet_tsupport_subset T.cutoff w (subset_tsupport _ hn))
  rw [T.sourceValue_eq]
  simp [SourceJetTerm.value,hz]

theorem allBranchExterior_source_sum_zero_off_support {n : ℕ}
    (p q : Fin (n+1)) (v θ : ℝ) (w : AngularSpace n → ℝ)
    (Q : ℂ × (Fin (n+1) → ℂ) → ℂ) (j : ℕ) (s : ℂ) (u : AngularSpace n) (hu : u ∉ tsupport w) :
    sourceTermSum p q v θ w Q j s u=0 := by
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨T,_,rfl⟩ := List.mem_map.mp hx
  exact allBranchExterior_sourceTerm_zero_off_support T p q v θ w Q s u hu

theorem allBranchExterior_compact_lie_sum {n : ℕ} (v θ : ℝ) (hv : v < 0)
    (p q : Fin (n+1)) (hpq : p ≠ q) (w : AngularSpace n → ℝ) (hw : ContDiff ℝ ∞ w)
    (Q : ℂ × (Fin (n+1) → ℂ) → ℂ) (s : ℂ)
    (hp : ∀ u ∈ tsupport w, ActualJetPoint v θ p q s u)
    (hQ : ∀ u ∈ tsupport w, AnalyticAt ℂ Q (s,chartMap v θ s u)) (j : ℕ) (u : AngularSpace n) :
    ((lieStep (actualField v θ p q))^[j] (initialSourceDensity v θ w Q)) s u=
      sourceTermSum p q v θ w Q j s u := by
  by_cases hu : u ∈ tsupport w
  · exact source_point_all_order v θ p q hpq s u hv w hw Q (hp u hu) (hQ u hu) j
  · have hsupp : ∀ t ∈ (univ : Set ℂ), support (initialSourceDensity v θ w Q t) ⊆ tsupport w := by
      intro t _ x hx
      apply subset_tsupport w
      intro hw0
      exact hx (by simp [initialSourceDensity,hw0])
    have hj := iterate_lieStep_support_subset (actualField v θ p q) (initialSourceDensity v θ w Q)
      isOpen_univ (isClosed_tsupport w) hsupp j s (mem_univ s)
    have hz : ((lieStep (actualField v θ p q))^[j] (initialSourceDensity v θ w Q)) s u=0 := by
      by_contra hn
      exact hu (hj (subset_tsupport _ hn))
    rw [hz,allBranchExterior_source_sum_zero_off_support p q v θ w Q j s u hu]

theorem allBranchExterior_compact_source_normal_form {n : ℕ} (d : LocalBranchData) (ε : ℝ)
    (hε : 0 < ε) (p q : Fin (n+1)) (hpq : p ≠ q) (w : AngularSpace n → ℝ) (hw : ContDiff ℝ ∞ w)
    (hK : HasCompactSupport w) (s : ℂ)
    (hp : ∀ u ∈ tsupport w, ActualJetPoint (-d.c₀*ε) d.thetaB p q s u)
    (hQ : ∀ u ∈ tsupport w, AnalyticAt ℂ
      (unfactoredNumerator (fun t : ℂ × (Fin (n+1) → ℂ) => microRegularAmplitude t.1 t.2))
      (s,chartMap (-d.c₀*ε) d.thetaB s u)) (j : ℕ) :
    iteratedDeriv j (allBranchOriginalWeightedIntegral n d ε w) s =
      ((n+1).factorial:ℂ)⁻¹*∫ u : AngularSpace n,
        sourceTermSum p q (-d.c₀*ε) d.thetaB w
          (unfactoredNumerator (fun t : ℂ × (Fin (n+1) → ℂ) => microRegularAmplitude t.1 t.2)) j s u := by
  rw [allBranchExterior_compact_source_derivative d ε hε p q w hw hK s hp hQ j]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun u => allBranchExterior_compact_lie_sum _ _
    (by nlinarith [d.c₀_pos]) p q hpq w hw _ s hp hQ j u)

theorem allBranchExterior_truncated_normal_form (d : LocalBranchData) :
    ∃ r : ℝ, 0 < r ∧ ∀ ε : ℝ, 0 < ε → ε ≤ r → ∀ n M : ℕ,
      ∀ p q : Fin (n+1), p ≠ q → ∀ h : ℝ, 0 < h → ∀ w : AngularSpace n → ℝ,
      ContDiff ℝ ∞ w → tsupport w ⊆ microcoreCube (n+1) r → ∀ j : ℕ,
      let W := allBranchTruncatedWeight M h p q w
      iteratedDeriv j (allBranchOriginalWeightedIntegral n d ε W) (radialParameter d.theta ε) =
        ((n+1).factorial:ℂ)⁻¹*∫ u : AngularSpace n,
          sourceTermSum p q (-d.c₀*ε) d.thetaB W
            (unfactoredNumerator (fun t : ℂ × (Fin (n+1) → ℂ) => microRegularAmplitude t.1 t.2)) j
            (radialParameter d.theta ε) u := by
  obtain ⟨r,hr,hdata⟩ := allBranchExterior_truncated_source_data d
  refine ⟨r,hr,?_⟩
  intro ε hε hεr n M p q hpq h hh w hw hsupp j
  obtain ⟨hsmooth,hcompact,hpoint⟩ := hdata ε hε hεr n M p q h hh w hw hsupp
  exact allBranchExterior_compact_source_normal_form d ε hε p q hpq _ hsmooth hcompact _
    (fun u hu => (hpoint u hu).1) (fun u hu => (hpoint u hu).2) j

end
end IsingBulk.Tail
