import IsingBulk.Tail.MicrocoreTransport
import IsingBulk.Tail.IndexedPairCounting
import IsingBulk.Tail.MicrocoreWindow

/-! Exact full Vandermonde-square degree, without discarding any collision
factor. Source radius and differentiated amplitude are attached separately. -/
namespace IsingBulk.Tail
noncomputable section
open scoped BigOperators

theorem microcore_vandermonde_indexed {N : ℕ} (φ : Fin N → ℂ) :
    microcoreVandermondeSquared φ =
      ∏ p ∈ orderedIndexPairs (Finset.univ : Finset (Fin N)), (φ p.1-φ p.2)^2 := by
  unfold microcoreVandermondeSquared orderedIndexPairs
  simp only [Finset.prod_filter,Finset.prod_product]

theorem microcore_vandermonde_norm_bound {N : ℕ} (φ : Fin N → ℂ)
    {R : ℝ} (hR : 0 ≤ R) (hφ : ∀ i, ‖φ i‖ ≤ R) :
    ‖microcoreVandermondeSquared φ‖ ≤ (2*R)^(N*(N-1)) := by
  rw [microcore_vandermonde_indexed,norm_prod]
  have hb : ∀ p ∈ orderedIndexPairs (Finset.univ : Finset (Fin N)),
      ‖(φ p.1-φ p.2)^2‖ ≤ (2*R)^2 := by
    intro p _
    rw [norm_pow]
    have hn := norm_sub_le (φ p.1) (φ p.2)
    have h1 := hφ p.1
    have h2 := hφ p.2
    nlinarith [norm_nonneg (φ p.1-φ p.2)]
  have hp := Finset.prod_le_prod₀ (fun p _ => norm_nonneg ((φ p.1-φ p.2)^2)) hb
  have hc : 2*N.choose 2=N*(N-1) := by
    rw [Nat.choose_two_right,Nat.mul_div_cancel' (Nat.even_mul_pred_self N).two_dvd]
  simpa only [Finset.prod_const,orderedIndexPairs_card,Finset.card_univ,
    Fintype.card_fin,← pow_mul,hc] using hp

/-- The exact source radius supplies exponential decay already at the square
root scale. The omitted factor N^(-1/2) can only strengthen this bound. -/
theorem microcore_sqrt_radius_exponential {A c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (N : ℕ) (hN : 1 ≤ N) :
    Real.sqrt (microcoreRadius A c N) ≤ Real.exp (-(A+4)*(N:ℝ)/2) := by
  have hNR : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hb : microcoreRadius A c N ≤ Real.exp (-(A+4)*(N:ℝ)) := by
    unfold microcoreRadius
    apply (div_le_self (mul_nonneg hc (Real.exp_nonneg _)) hNR).trans
    exact mul_le_of_le_one_left (Real.exp_nonneg _) hc1
  have he : (Real.exp (-(A+4)*(N:ℝ)/2))^2=Real.exp (-(A+4)*(N:ℝ)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  apply Real.sqrt_le_iff.mpr
  exact ⟨Real.exp_nonneg _,by simpa only [he] using hb⟩

/-- Combining the degree from shape volume and Vandermonde yields the cubic
negative exponent, against any explicitly supplied exp(C N²) amplitude cost. -/
theorem microcore_cubic_exponential_budget {A c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (N : ℕ) (hN : 1 ≤ N) (C : ℝ) :
    Real.exp (C*(N:ℝ)^2)*(Real.sqrt (microcoreRadius A c N))^(N^2-1) ≤
      Real.exp (C*(N:ℝ)^2-(A+4)*(N:ℝ)*((N^2-1:ℕ):ℝ)/2) := by
  have hp := pow_le_pow_left₀ (Real.sqrt_nonneg _) (microcore_sqrt_radius_exponential (A := A) hc hc1 N hN)
    (N^2-1)
  apply (mul_le_mul_of_nonneg_left hp (Real.exp_nonneg _)).trans_eq
  rw [← Real.exp_nat_mul,← Real.exp_add]
  congr 1
  ring

end
end IsingBulk.Tail
