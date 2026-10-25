import IsingBulk.Joint.Negative.FamilyCompleteBoundaryJets
import IsingBulk.Joint.Negative.ModelData
import IsingBulk.Anisotropic.NegativeDominance.GrowingLowSum

/-! # Complete summable boundary-jet envelopes, uniform over complex families
The same envelope covers every odd particle, including all finite initial
orders. No finite-prefix estimate is inserted as a premise.
-/
namespace IsingBulk.Joint.Negative
noncomputable section
open IsingBulk.Anisotropic.RegularEdges IsingBulk.Anisotropic.NegativeDominance
  Set Filter Metric
open scoped Topology BigOperators

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

private theorem cauchy_majorant_polynomial (j : ℕ) {a N K V : ℝ}
    (ha : a≠0) (hN : N≠0) :
    (j.factorial:ℝ)*(K*N^2*V)/(a/N^3)^j=
      ((j.factorial:ℝ)*K/a^j)*(N^(3*j+2)*V) := by
  rw [pow_add,pow_mul,div_pow]
  field_simp

/-- Absolute convergence with an actual common nonnegative envelope for the
complete boundary jet series, simultaneously over the compact family. -/
theorem compact_actual_odd_boundary_summable_majorants
    {b : ℝ} {Q : Set E} (curve : ℂ × E→Coupling) (amp : ℂ × E→ℂ)
    (hb : |b|<1) (hQ : IsCompact Q)
    (hc : ∀ eta∈Q, AnalyticAt ℂ curve (0,eta))
    (ha : ∀ eta∈Q, AnalyticAt ℂ amp (0,eta))
    (hS : ∀ eta∈Q, S (curve (0,eta))≠0)
    (hamp : ∀ eta∈Q, amp (0,eta)≠0)
    (he : ∀ eta∈Q, A (curve (0,eta))+T (curve (0,eta))=(b:ℂ)*S (curve (0,eta)))
    (hB : ∀ eta∈Q, 0<(-T (curve (0,eta))/S (curve (0,eta))).im) :
    ∃ G : ℕ→ℕ→ℝ, (∀ j, Summable (G j)) ∧ (∀ j m, 0≤G j m) ∧
      ∀ eta∈Q, ∀ j m : ℕ,
        ‖iteratedDeriv j
          (fun t => amp (t,eta)^(2*m+1)*continuedAngularCoefficient (2*m) (curve (t,eta))) 0‖≤G j m := by
  obtain ⟨a,r,C,M,K,haR,hr,hr1,hC,hM,hK,hbound⟩ :=
    compact_actual_odd_boundary_cauchy curve amp hb hQ hc ha hS hamp he hB
  let G : ℕ→ℕ→ℝ := fun j m =>
    ((j.factorial:ℝ)*K/a^j)*(((2*m+1:ℕ):ℝ)^(3*j+2)*particleEdgeMajorant r C M (2*m+1))
  have hi : Function.Injective (fun m : ℕ => 2*m+1) := by intro x y h; dsimp only at h; omega
  refine ⟨G,?_,?_,?_⟩
  · intro j
    exact ((particleEdgeMajorant_polynomial_summable hr hr1 hC hM (3*j+2)).comp_injective hi).mul_left _
  · intro j m
    exact mul_nonneg (by positivity)
      (mul_nonneg (by positivity) (particleEdgeMajorant_nonneg hr.le hC.le hM.le _))
  · intro eta heta j m
    have hh := hbound eta heta j (2*m) (show Odd (2*m+1) from ⟨m,by omega⟩)
    rw [cauchy_majorant_polynomial j haR.ne' (by positivity)] at hh
    exact hh

/-- A common all-index normalized Cauchy bound, suitable for the growing-low
and middle/high particle splits. No particle threshold depends on the member. -/
theorem compact_actual_odd_normalized_cauchy
    {b : ℝ} {Q : Set E} (curve : ℂ × E→Coupling) (amp : ℂ × E→ℂ)
    (hb : |b|<1) (hQ : IsCompact Q)
    (hc : ∀ eta∈Q, AnalyticAt ℂ curve (0,eta))
    (ha : ∀ eta∈Q, AnalyticAt ℂ amp (0,eta))
    (hS : ∀ eta∈Q, S (curve (0,eta))≠0)
    (hamp : ∀ eta∈Q, amp (0,eta)≠0)
    (he : ∀ eta∈Q, A (curve (0,eta))+T (curve (0,eta))=(b:ℂ)*S (curve (0,eta)))
    (hB : ∀ eta∈Q, 0<(-T (curve (0,eta))/S (curve (0,eta))).im) :
    ∃ a D : ℝ, 0<a ∧ 0<D ∧ ∀ eta∈Q, ∀ j m : ℕ,
      ‖negativePaperParticleCoefficient (fun t => curve (t,eta)) (fun t => amp (t,eta)) m j‖≤
        D*((2*m+1:ℕ):ℝ)^2*(((2*m+1:ℕ):ℝ)^3/a)^j := by
  obtain ⟨a,r,C,M,K,haR,hr,hr1,hC,hM,hK,hbound⟩ :=
    compact_actual_odd_boundary_cauchy curve amp hb hQ hc ha hS hamp he hB
  obtain ⟨H,hH,hmajor⟩ := particleEdgeMajorant_uniform_bound hr hr1 hC hM
  refine ⟨a,K*H,haR,mul_pos hK hH,?_⟩
  intro eta heta j m
  have hj : (j.factorial:ℝ)≠0 := by exact_mod_cast Nat.factorial_ne_zero j
  have hN : ((2*m+1:ℕ):ℝ)≠0 := by positivity
  unfold negativePaperParticleCoefficient
  rw [norm_div,Complex.norm_natCast]
  calc
    _ ≤ ((j.factorial:ℝ)*(K*((2*m+1:ℕ):ℝ)^2*particleEdgeMajorant r C M (2*m+1))/
        (a/((2*m+1:ℕ):ℝ)^3)^j)/(j.factorial:ℝ) :=
      div_le_div_of_nonneg_right (hbound eta heta j (2*m) ⟨m,by omega⟩) (by positivity)
    _ = K*((2*m+1:ℕ):ℝ)^2*particleEdgeMajorant r C M (2*m+1)*(((2*m+1:ℕ):ℝ)^3/a)^j := by
      rw [div_pow,div_pow]
      field_simp [haR.ne',hj,hN]
    _ ≤ K*((2*m+1:ℕ):ℝ)^2*H*(((2*m+1:ℕ):ℝ)^3/a)^j := by
      gcongr
      exact hmajor (2*m+1)
    _ = (K*H)*((2*m+1:ℕ):ℝ)^2*(((2*m+1:ℕ):ℝ)^3/a)^j := by ring

end
end IsingBulk.Joint.Negative
