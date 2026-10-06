import IsingBulk.Tail.AllBranchExteriorNumerator
import IsingBulk.Tail.SourceJetIntegralTheorem
import IsingBulk.First.CompactAnalyticShapeIntegral

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Jets IsingBulk.First

theorem allBranchExterior_vandermonde_collision {N : ℕ} (p q : Fin N) (hpq : p < q)
    (φ : Fin N → ℂ) (hφ : φ p=φ q) : microcoreVandermondeSquared φ=0 := by
  rw [microcore_vandermonde_indexed]
  apply Finset.prod_eq_zero (i := (p,q))
  · simp [orderedIndexPairs,hpq]
  · simp [hφ]

theorem allBranchExterior_complex_density_collision {N : ℕ} (p q : Fin N) (hpq : p < q)
    (v θ : ℝ) (A : ℂ × (Fin N → ℂ) → ℂ) (s : ℂ) (u : Fin N → ℂ) (hu : u p=u q) :
    sourceComplexDensity v θ (unfactoredNumerator A) (s,u)=0 := by
  unfold sourceComplexDensity microComplexPullback
  dsimp only
  rw [allBranchExterior_unfactored_eq,allBranchExterior_vandermonde_collision p q hpq]
  · simp
  · simp only [microComplexChartMap,hu]

theorem allBranchExterior_parameter_jet_collision {N : ℕ} (p q : Fin N) (hpq : p < q)
    (v θ : ℝ) (A : ℂ × (Fin N → ℂ) → ℂ) (s : ℂ) (u : Fin N → ℂ) (hu : u p=u q) (j : ℕ) :
    jointParameterJet (sourceComplexDensity v θ (unfactoredNumerator A)) j (s,u)=0 := by
  rw [jointParameterJet_eq]
  have he : (fun t => sourceComplexDensity v θ (unfactoredNumerator A) (t,u))=fun _ => (0:ℂ) :=
    funext (fun t => allBranchExterior_complex_density_collision p q hpq v θ A t u hu)
  rw [he,← iteratedDeriv_eq_iterate]
  cases j <;> simp

end
end IsingBulk.Tail
