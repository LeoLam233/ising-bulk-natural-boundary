import IsingBulk.Tail.SquaredLinearJets
import IsingBulk.Tail.MicrocoreVandermondeBound

namespace IsingBulk.Tail
noncomputable section
open scoped BigOperators

def branchCoordinateDifference {N : ℕ} (p q : Fin N) : (Fin N → ℂ) →L[ℂ] ℂ :=
  (ContinuousLinearMap.proj p : (Fin N → ℂ) →L[ℂ] ℂ)-ContinuousLinearMap.proj q

theorem branchCoordinateDifference_norm {N : ℕ} (p q : Fin N) :
    ‖branchCoordinateDifference p q‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro z
  change ‖z p-z q‖ ≤ 2*‖z‖
  have hh := norm_sub_le (z p) (z q)
  have h₁ := norm_le_pi_norm z p
  have h₂ := norm_le_pi_norm z q
  linarith

theorem allBranchExterior_vandermonde_jets {N : ℕ} (φ : Fin N → ℂ) (R : ℝ)
    (hR : 0 < R) (hφ : ∀ p q, ‖φ p-φ q‖ ≤ 2*R) (k : ℕ) :
    ‖iteratedFDeriv ℂ k microcoreVandermondeSquared φ‖ ≤
      (8:ℝ)^(N.choose 2)*(N.choose 2:ℝ)^k*R^((N*(N-1):ℕ)-(k:ℤ)) := by
  let s := orderedIndexPairs (Finset.univ : Finset (Fin N))
  let f : (Fin N × Fin N) → (Fin N → ℂ) → ℂ := fun p y => (y p.1-y p.2)^2
  have hb : ∀ p ∈ s, ∀ j ≤ k, ‖iteratedFDeriv ℂ j (f p) φ‖ ≤ 8*R^((2:ℤ)-(j:ℤ)) := by
    intro p _ j _
    exact squared_linear_scaled_jets (branchCoordinateDifference p.1 p.2) φ R hR
      (branchCoordinateDifference_norm p.1 p.2) (hφ p.1 p.2) j
  have ha : ∀ p ∈ s, AnalyticAt ℂ (f p) φ := by
    intro p _
    exact ((branchCoordinateDifference p.1 p.2).analyticAt φ).pow 2
  have hh := analytic_finset_product_scaled_jets s f φ k 8 R 2 (by norm_num) hR ha hb k le_rfl
  have he : (fun y => ∏ p ∈ s, f p y)=microcoreVandermondeSquared := by
    funext y
    exact (microcore_vandermonde_indexed y).symm
  rw [he] at hh
  have hs : s.card=N.choose 2 := by simp [s,orderedIndexPairs_card]
  have hc : 2*N.choose 2=N*(N-1) := by
    rw [Nat.choose_two_right,Nat.mul_div_cancel' (Nat.even_mul_pred_self N).two_dvd]
  rw [hs] at hh
  convert hh using 1
  congr 2
  have hcZ : ((N*(N-1):ℕ):ℤ)=2*(N.choose 2:ℤ) := by exact_mod_cast hc.symm
  rw [hcZ]

end
end IsingBulk.Tail
