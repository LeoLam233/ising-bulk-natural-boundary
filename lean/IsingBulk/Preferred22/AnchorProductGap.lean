import IsingBulk.Preferred22.SelectedProductDisk

/-! Uniform product-gap preservation from one genuine compact anchor.
The radius constant precedes the particle count. -/
namespace IsingBulk.Preferred22
noncomputable section
open Filter
open scoped BigOperators Topology
set_option maxHeartbeats 800000

theorem preferred_anchor_product_relative_gap {q : ℝ} (_hq0 : 0≤q) (hq1 : q<1) :
    ∃ a : ℝ,0<a ∧ ∀ N : ℕ,0<N → ∀ z w : Fin N → ℂ,∀ anchor : Fin N,
      (∀ i,z i≠0) → (∀ i,‖z i‖≤1) → ‖z anchor‖≤q →
      (∀ i,‖w i/z i-1‖≤a/(N:ℝ)) →
      ‖∏ i,w i‖≤(1+q)/2 := by
  have hcont : ContinuousAt (fun x : ℝ => q*Real.exp x) 0 := by fun_prop
  have he : ∀ᶠ x in 𝓝 (0:ℝ),q*Real.exp x<(1+q)/2 :=
    hcont.eventually_lt continuousAt_const (by simpa using (show q<(1+q)/2 by linarith))
  obtain ⟨r,hr,hball⟩ := Metric.eventually_nhds_iff.mp he
  let a := r/2
  have ha : 0<a := by dsimp only [a]; positivity
  have haR : a<r := by dsimp only [a]; linarith
  have hexp : q*Real.exp a≤(1+q)/2 :=
    (hball (y := a) (by simpa only [dist_zero_right,Real.norm_eq_abs,abs_of_pos ha] using haR)).le
  refine ⟨a,ha,?_⟩
  intro N hN z w anchor hz hz1 hanchor hrel
  have hNr : (N:ℝ)≠0 := by exact_mod_cast hN.ne'
  have hcenter : ‖∏ i,z i‖≤q := by
    rw [norm_prod]
    calc
      _ ≤ ∏ i : Fin N,if i=anchor then q else 1 := by
        apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
        intro i _
        split_ifs with hi
        · simpa only [hi] using hanchor
        · exact hz1 i
      _ = q := by simp
  have hb := preferred_finite_product_relative_bound z w hz hrel
  have hmul : (N:ℝ)*(a/(N:ℝ))=a := by field_simp
  rw [hmul] at hb
  exact hb.trans ((mul_le_mul_of_nonneg_right hcenter (Real.exp_pos a).le).trans hexp)

end
end IsingBulk.Preferred22
