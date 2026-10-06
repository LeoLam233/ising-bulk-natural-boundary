import IsingBulk.Tail.SourceJetNeighborhood
import IsingBulk.Tail.SectorPartitionSupport

/-! Complete compact original-chart derivative/semantic-jet integral
identity. Zero outside the genuine cutoff support is proved on both sides. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Jets IsingBulk.Lie Set MeasureTheory Function
open scoped ContDiff

theorem sourceTermSum_support_subset {n : ℕ} (v theta : ℝ) (p q : Fin (n+1))
    (w : AngularSpace n → ℝ) (Q : ℂ × (Fin (n+1) → ℂ) → ℂ) (j : ℕ) (s : ℂ) :
    support (sourceTermSum p q v theta w Q j s) ⊆ tsupport w := by
  intro x hx
  by_contra hn
  have hz : sourceTermSum p q v theta w Q j s x=0 := by
    unfold sourceTermSum
    apply List.sum_eq_zero
    intro a ha
    obtain ⟨T,hT,rfl⟩ := List.mem_map.mp ha
    have hcut : cutoffJet T.cutoff w x=0 := by
      by_contra h
      exact hn (cutoffJet_tsupport_subset T.cutoff w (subset_closure h))
    simp [SourceJetTerm.sourceValue,hcut]
  exact hx hz

theorem source_compact_integral_sourceTermSum {n : ℕ} (v theta : ℝ) (hv : v<0)
    (p q : Fin (n+1)) (hpq : p≠q) (Q : ℂ × (Fin (n+1) → ℂ) → ℂ)
    (w : AngularSpace n → ℝ) (hw : ContDiff ℝ ∞ w)
    {K : Set (AngularSpace n)} (hK : IsCompact K) (hsupp : tsupport w ⊆ K)
    {s : ℂ} (hpoint : ∀ x∈K,ActualJetPoint v theta p q s x)
    (hQ : ∀ x∈K,AnalyticAt ℂ Q (s,chartMap v theta s x)) (j : ℕ) :
    iteratedDeriv j (fun t => ∫ x,initialSourceDensity v theta w Q t x) s =
      ∫ x,sourceTermSum p q v theta w Q j s x := by
  rw [source_compact_integral_iteratedDeriv v theta p q Q w hw hK hsupp hpoint hQ j]
  let A := initialSourceDensity v theta w Q
  let V := actualField v theta p q
  have hsA : ∀ t∈(univ : Set ℂ),support (A t) ⊆ K := by
    intro t ht x hx
    have hwx : w x≠0 := by intro he; simp [A,initialSourceDensity,he] at hx
    exact hsupp (subset_closure hwx)
  have hsiter := iterate_lieStep_support_subset V A isOpen_univ hK.isClosed hsA j s (mem_univ s)
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x∈K
  · exact source_point_all_order v theta p q hpq s x hv w hw Q (hpoint x hx) (hQ x hx) j
  · have hzero : ((lieStep V)^[j] A) s x=0 := by
      by_contra h
      exact hx (hsiter (subset_closure h))
    have hterms : sourceTermSum p q v theta w Q j s x=0 := by
      by_contra h
      exact hx (hsupp (sourceTermSum_support_subset v theta p q w Q j s h))
    exact hzero.trans hterms.symm

end
end IsingBulk.Tail
