import IsingBulk.Anisotropic.NegativeDominance.OddBoundaryGap

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open IsingBulk.Anisotropic.RegularEdges Set
open scoped BigOperators

/-- The actual root product loses modulus according to the sum of every
angular square, not merely one selected coordinate. -/
theorem edgeRoot_boundary_product_gaussian {b : ℝ} {B : ℂ} (hb : |b|<1) (hB : 0<B.im) :
    ∃c : ℝ,0<c ∧ ∀N : ℕ,∀q : Fin N→ℝ,(∀i,q i∈Icc (-Real.pi) Real.pi) →
      ‖∏i,edgeRoot b B (q i)‖≤Real.exp (-c*∑i,(q i)^2) := by
  obtain ⟨c,hc,hgap⟩ := edgeRoot_boundary_quadratic_gap hb hB
  refine ⟨c,hc,?_⟩
  intro N q hq
  have hf (i : Fin N) : ‖edgeRoot b B (q i)‖≤Real.exp (-c*(q i)^2) := by
    have hh := Real.add_one_le_exp (-c*(q i)^2)
    linarith [hgap (q i) (hq i)]
  rw [norm_prod]
  calc
    _ ≤ ∏i,Real.exp (-c*(q i)^2) := Finset.prod_le_prod₀ (fun _ _=>norm_nonneg _) (fun i _=>hf i)
    _ = _ := by rw [←Real.exp_sum]; congr 1; rw [Finset.mul_sum]

/-- The entire outer region has one positive boundary resolvent gap before
all particle orders and all angular configurations. -/
theorem outer_boundary_product_gap {b : ℝ} {B : ℂ} (hb : |b|<1) (hB : 0<B.im)
    (σ : ℝ) (hσ : 0<σ) :
    ∃κ : ℝ,0<κ ∧ ∀N : ℕ,∀q : Fin N→ℝ,(∀i,q i∈Icc (-Real.pi) Real.pi) →
      σ≤∑i,(q i)^2 → κ≤‖1-∏i,edgeRoot b B (q i)‖ := by
  obtain ⟨c,hc,hprod⟩ := edgeRoot_boundary_product_gaussian hb hB
  refine ⟨1-Real.exp (-c*σ),by have hh := Real.exp_lt_one_iff.mpr (by nlinarith : -c*σ<0); linarith,?_⟩
  intro N q hq hS
  have hh := (hprod N q hq).trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hS (by linarith)))
  have hg := norm_sub_norm_le (1 : ℂ) (∏i,edgeRoot b B (q i))
  rw [norm_one] at hg
  linarith

end
end IsingBulk.Anisotropic.NegativeDominance
