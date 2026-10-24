import IsingBulk.Anisotropic.NegativeDominance.OddBoundaryGap
import IsingBulk.Anisotropic.NegativeDominance.UniformRootLipschitz
import IsingBulk.Anisotropic.NegativeDominance.ProductPerturbation

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open IsingBulk.Tail IsingBulk.Anisotropic.RegularEdges Set
open scoped BigOperators

/-- The true odd resolvent remains uniformly separated from zero on a complex
disk of radius a/N³. Constants precede every particle index and angle. -/
theorem odd_negative_complex_product_gap {b : ℝ} {B : ℂ → ℂ}
    (hb : |b|<1) (hB : 0<(B 0).im) (hBa : AnalyticAt ℂ B 0) :
    ∃ a c : ℝ, 0<a ∧ 0<c ∧ ∀ (n : ℕ), Odd (n+1) → ∀ v : Fin n → ℝ,
      ∀ u : ℂ, ‖u‖<a/((n+1 : ℕ) : ℝ)^3 →
        (∀ i, AnalyticAt ℂ (fun w => edgeParamRoot b B w (negativeShiftedAngles n v i)) u) ∧
        c/((n+1 : ℕ) : ℝ)^2≤1-‖edgeRootProduct b B u (negativeShiftedAngles n v)‖ := by
  obtain ⟨κ,hκ,hboundary⟩ := odd_negative_boundary_product_gap hb hB
  obtain ⟨δ,L,hδ,hL,hroot⟩ := edgeParamRoot_uniform_lipschitz_zero hb hB hBa
  let E := Real.exp 1
  have hE : 0<E := Real.exp_pos _
  have hE1 : 1≤E := Real.one_le_exp_iff.mpr (by norm_num)
  let a := min δ (min (1/(E*L)) (κ/(2*E*L)))
  have ha : 0<a := lt_min hδ (lt_min (by positivity) (by positivity))
  have haδ : a≤δ := min_le_left _ _
  have ha1 : a≤1/(E*L) := (min_le_right _ _).trans (min_le_left _ _)
  have haκ : a≤κ/(2*E*L) := (min_le_right _ _).trans (min_le_right _ _)
  have hELa : E*L*a≤1 := by have hh := (le_div_iff₀ (mul_pos hE hL)).mp ha1; nlinarith
  have hELκ : E*L*a≤κ/2 := by have hh := (le_div_iff₀ (by positivity : 0<2*E*L)).mp haκ; nlinarith
  refine ⟨a,κ/2,ha,by positivity,?_⟩
  intro n hn v u hu
  let N : ℝ := (n+1 : ℕ)
  have hN : 1≤N := by dsimp [N]; exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n))
  have hN0 : 0<N := lt_of_lt_of_le zero_lt_one hN
  have hN2 : 1≤N^2 := one_le_pow₀ hN
  have hN3 : 1≤N^3 := one_le_pow₀ hN
  have hun : ‖u‖<a/N^3 := hu
  have hau : a/N^3≤a := (div_le_iff₀ (pow_pos hN0 _)).mpr (by nlinarith)
  have huδ : ‖u‖<δ := hun.trans_le (hau.trans haδ)
  have hscale : N*‖u‖≤a/N^2 := by
    calc
      N*‖u‖ ≤ N*(a/N^3) := mul_le_mul_of_nonneg_left hun.le hN0.le
      _ = a/N^2 := by field_simp
  have haN2 : a/N^2≤a := (div_le_iff₀ (pow_pos hN0 _)).mpr (by nlinarith)
  have hNd : N*(L*‖u‖)≤1 := by
    have hh := mul_le_mul_of_nonneg_left (hscale.trans haN2) hL.le
    have he := mul_le_mul_of_nonneg_right hE1 (show 0≤L*a by positivity)
    nlinarith
  let q := negativeShiftedAngles n v
  have hbase (i : Fin (n+1)) : ‖edgeParamRoot b B 0 (q i)‖≤1 := by
    simpa only [edgeParamRoot_zero] using (edgeRoot_bounds hb hB (q i)).1
  have hdif (i : Fin (n+1)) : ‖edgeParamRoot b B u (q i)-edgeParamRoot b B 0 (q i)‖≤L*‖u‖ :=
    (hroot u huδ (q i) (wrapAngle_mem _)).2
  have hp := norm_prod_perturbation_linear (fun i => edgeParamRoot b B u (q i))
    (fun i => edgeParamRoot b B 0 (q i)) (by positivity : 0≤L*‖u‖) hNd hbase hdif
  have herror : E*N*(L*‖u‖)≤κ/(2*N^2) := by
    calc
      E*N*(L*‖u‖) = E*L*(N*‖u‖) := by ring
      _ ≤ E*L*(a/N^2) := mul_le_mul_of_nonneg_left hscale (mul_pos hE hL).le
      _ = (E*L*a)/N^2 := by ring
      _ ≤ (κ/2)/N^2 := div_le_div_of_nonneg_right hELκ (sq_nonneg N)
      _ = κ/(2*N^2) := by ring
  have hgap := hboundary n hn v
  have htri := norm_add_le ((∏ i,edgeParamRoot b B u (q i))-(∏ i,edgeParamRoot b B 0 (q i)))
    (∏ i,edgeParamRoot b B 0 (q i))
  rw [sub_add_cancel] at htri
  simp only [edgeParamRoot_zero] at hp htri
  refine ⟨fun i => (hroot u huδ (q i) (wrapAngle_mem _)).1,?_⟩
  change (κ/2)/N^2≤1-‖∏ i,edgeParamRoot b B u (q i)‖
  have heq : κ/(2*N^2)=(κ/2)/N^2 := by ring
  have heq2 : κ/N^2=2*((κ/2)/N^2) := by ring
  change κ/N^2≤1-‖∏ i,edgeRoot b (B 0) (q i)‖ at hgap
  rw [heq2] at hgap
  rw [heq] at herror
  change ‖(∏ i,edgeParamRoot b B u (q i))-(∏ i,edgeRoot b (B 0) (q i))‖≤E*N*(L*‖u‖) at hp
  linarith

end
end IsingBulk.Anisotropic.NegativeDominance
