import IsingBulk.Tail.RegularPairNeighborhood
import IsingBulk.Tail.ScaledAnalyticProductJets
import IsingBulk.Tail.IndexedPairCounting
import IsingBulk.Analysis.JetsScalarBounds

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Branch IsingBulk.Jets Filter
open scoped Topology BigOperators

theorem allBranchExterior_complete_pair_jets (s₀ : ℂ) (c q : ℝ) (hs : s₀ ≠ 0)
    (hS : s₀+s₀⁻¹=(1+c:ℂ)) (hc : |c| < 1) (hq : 0 < q) (hq1 : q ≤ 1) (J : ℕ) :
    ∃ C r : ℝ, 1 ≤ C ∧ 0 < r ∧ ∀ N : ℕ, ∀ z : ℂ × (Fin N → ℂ),
      ‖z.1-s₀‖ < r → (∀ i, ‖z.2 i‖ < r) → ∀ k ≤ J,
      ‖iteratedFDeriv ℂ k (fun t : ℂ × (Fin N → ℂ) =>
        ∏ p ∈ orderedIndexPairs (Finset.univ : Finset (Fin N)),
          branchCompletePair (t.1,t.2 p.1,t.2 p.2)) z‖ ≤
        C^k*(N.choose 2:ℝ)^k*q^((N.choose 2:ℤ)-(k:ℤ)) := by
  have hbase := branchCompletePair_analytic s₀ c hs hS hc
  obtain ⟨C₀,hC₀,hjets⟩ := branchCompletePair_finite_jets s₀ c hs hS hc J
  obtain ⟨r₀,hr₀,hstrict⟩ := branchCompletePair_strict_neighborhood s₀ c q hs hS hc hq
  obtain ⟨r₁,hr₁,hlocal⟩ := Metric.eventually_nhds_iff.mp (hbase.eventually_analyticAt.and hjets)
  refine ⟨max 1 C₀,min r₀ r₁,le_max_left _ _,lt_min hr₀ hr₁,?_⟩
  intro N z hz hφ k hk
  let f : (Fin N × Fin N) → (ℂ × (Fin N → ℂ)) → ℂ :=
    fun p t => branchCompletePair (t.1,t.2 p.1,t.2 p.2)
  have hd (p : Fin N × Fin N) : dist (z.1,z.2 p.1,z.2 p.2) (s₀,0,0) < min r₀ r₁ := by
    rw [Prod.dist_eq,Prod.dist_eq,max_lt_iff,max_lt_iff]
    simpa only [dist_eq_norm,sub_zero] using And.intro hz (And.intro (hφ p.1) (hφ p.2))
  have ha (p : Fin N × Fin N) : AnalyticAt ℂ (f p) z :=
    AnalyticAt.comp (g := branchCompletePair) (f := pairCoordinate p.1 p.2)
      ((hlocal ((hd p).trans_le (min_le_right _ _))).1) ((pairCoordinate p.1 p.2).analyticAt z)
  have hb (p : Fin N × Fin N) (j : ℕ) (hj : j ≤ J) :
      ‖iteratedFDeriv ℂ j (f p) z‖ ≤ (max 1 C₀)^j*q^(1-(j:ℤ)) := by
    by_cases hj0 : j=0
    · subst j
      simpa only [norm_iteratedFDeriv_zero,pow_zero,Nat.cast_zero,sub_zero,zpow_one,one_mul]
        using (hstrict _ ((hd p).trans_le (min_le_left _ _))).le
    · have hjp : 1 ≤ j := by omega
      have hpair := hlocal ((hd p).trans_le (min_le_right _ _))
      have hcomp := analytic_linear_comp_jet_bound branchCompletePair (pairCoordinate p.1 p.2) z j
        hpair.1 (pairCoordinate_norm p.1 p.2)
      have hb₀ : ‖iteratedFDeriv ℂ j (f p) z‖ ≤ C₀ := hcomp.trans (hpair.2 j hj)
      have hpow : C₀ ≤ (max 1 C₀)^j := (le_max_right _ _).trans
        (by simpa using pow_le_pow_right₀ (le_max_left 1 C₀) hjp)
      exact hb₀.trans (hpow.trans (le_mul_of_one_le_right (by positivity)
        (one_le_zpow_of_nonpos₀ hq hq1 (by omega))))
  have hh := analytic_finset_product_contraction_jets
    (orderedIndexPairs (Finset.univ : Finset (Fin N))) f z J (max 1 C₀) q
    (by positivity) hq (fun p _ => ha p) (fun p _ j hj => hb p j hj) k hk
  simpa only [orderedIndexPairs_card,Finset.card_univ,Fintype.card_fin] using hh

end
end IsingBulk.Tail
