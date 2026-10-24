import IsingBulk.Anisotropic.NegativeNormalForm.Algebra
import IsingBulk.First.ShapeVandermonde

/-! Complex Vandermonde identities on all coincidence divisors.
Every quotient below is represented by a product of supplied divided differences,
never by dividing by the Vandermonde itself. -/
namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open scoped BigOperators
open IsingBulk.First

/-- The actual ordered complex Vandermonde used by the negative-edge residue. -/
def vandermonde {n : ℕ} (v : Config n) : ℂ :=
  ∏ p ∈ firstStrictPairs n, (v p.1 - v p.2)

/-- A polynomial expression for the full density multiplier from pair factors. -/
def pairMultiplier {n : ℕ} (R : Fin n → Fin n → ℂ) : ℂ :=
  ∏ p ∈ firstStrictPairs n, R p.1 p.2

theorem vandermonde_project {n : ℕ} (v : Config n) :
    vandermonde (project v) = vandermonde v := by
  unfold vandermonde
  simp only [project_difference]

theorem vandermonde_dividedDifference {n : ℕ} (v w : Config n)
    (R : Fin n → Fin n → ℂ)
    (hR : ∀ i j, i < j → w i - w j = (v i - v j) * R i j) :
    vandermonde w = vandermonde v * pairMultiplier R := by
  unfold vandermonde pairMultiplier
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  exact hR p.1 p.2 (mem_firstStrictPairs p |>.mp hp)

/-- Full squared numerator factorization, including its zero locus. -/
theorem vandermonde_sq_dividedDifference {n : ℕ} (v w : Config n)
    (R : Fin n → Fin n → ℂ)
    (hR : ∀ i j, i < j → w i - w j = (v i - v j) * R i j) :
    vandermonde w ^ 2 = vandermonde v ^ 2 * pairMultiplier R ^ 2 := by
  rw [vandermonde_dividedDifference v w R hR, mul_pow]

theorem vandermonde_scale {n : ℕ} (v : Config n) (c : ℂ) :
    vandermonde (fun i => c * v i) = c ^ (n.choose 2) * vandermonde v := by
  simp [vandermonde, ← mul_sub, Finset.prod_mul_distrib, firstStrictPairs_card]

theorem vandermonde_sq_scale (m : ℕ) (v : Config (m+1)) (c : ℂ) :
    vandermonde (fun i => c * v i) ^ 2 = c ^ ((m+1)*m) * vandermonde v ^ 2 := by
  rw [vandermonde_scale, mul_pow, ← pow_mul]
  have h := firstStrictPairs_twice_card m
  rw [firstStrictPairs_card] at h
  rw [Nat.mul_comm _ 2, h]

/-- The exponent combines the numerator degree and constrained dimension,
not the ambient dimension. This is the scalar extraction in (4.36). -/
theorem vandermonde_density_scaling (m : ℕ) (v : Config (m+1)) (c : ℂ) :
    vandermonde (fun i => c * v i) ^ 2 * c ^ m =
      c ^ (m * (m+2)) * vandermonde v ^ 2 := by
  rw [vandermonde_sq_scale]
  calc
    _ = (c ^ ((m+1)*m) * c ^ m) * vandermonde v ^ 2 := by ring
    _ = _ := by rw [← pow_add]; congr 2; ring

/-- Substitution of the actual rank-one correction's difference factors. -/
theorem vandermonde_meanCorrection {n : ℕ} (ell w : Config n)
    (L : Fin n → Fin n → ℂ)
    (hL : ∀ i j, i < j → ell i - ell j = (w i - w j) * L i j) :
    vandermonde (meanCorrection ell w) = vandermonde w *
      pairMultiplier (fun i j => 1 + rankOneCoefficient ell * pairing w ell * L i j) := by
  apply vandermonde_dividedDifference
  intro i j hij
  exact meanCorrection_difference_factor ell w i j (L i j) (hL i j hij)

end
end IsingBulk.Anisotropic.NegativeNormalForm
