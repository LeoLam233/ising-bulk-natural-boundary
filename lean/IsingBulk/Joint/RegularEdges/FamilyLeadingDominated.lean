import IsingBulk.Anisotropic.RegularEdges.LeadingCutoff

namespace IsingBulk.Joint.RegularEdges
noncomputable section
open IsingBulk.First IsingBulk.Anisotropic.RegularEdges MeasureTheory Set Filter
open scoped Topology

theorem filtered_edge_shape_dominated_limit {α : Type*} {l : Filter α}
    [l.IsCountablyGenerated] {τ : α → ℝ} (hτ : Tendsto τ l (𝓝[>] 0)) {n k a : ℕ}
    (hbalance : n+a+(n+1)*n=2*(k+1))
    (hmajorant : Integrable (@shapeMajorant n k))
    (A D : α → ShapeSpace n → ℂ) (a₀ : ℂ) {Q M c : ℝ} {w : ℂ}
    (hQ : 0 < Q) (hw : 0 < w.re) (hM : 0 ≤ M) (hc : 0 < c) 
    (hregular : ∀ᶠ lam in l, Measurable (A lam) ∧ Measurable (D lam) ∧
      (∀ x, ‖A lam x‖ ≤ M) ∧ (∀ x, A lam x ≠ 0 →
        c*((τ lam)^2+‖x‖^2) ≤ ‖D lam x‖))
    (hAlimit : ∀ x, Tendsto (fun lam => A lam (τ lam • x)) l (𝓝 a₀))
    (hDlimit : ∀ x, Tendsto (fun lam => D lam (τ lam • x)/(τ lam : ℂ)^2)
      l (𝓝 ((Q : ℂ)+w*(‖x‖ : ℂ)^2))) :
    Tendsto (fun lam => ((τ lam)^a) • ∫ x : ShapeSpace n, localShapeQuotient k (A lam) (D lam) x)
      l (𝓝 (a₀*shapePeriodIntrinsic n k Q w)) := by
  have hrange : ∀ᶠ lam in l, 0 < τ lam ∧ Measurable (A lam) ∧ Measurable (D lam) ∧
      (∀ x, ‖A lam x‖ ≤ M) ∧ (∀ x, A lam x ≠ 0 → c*((τ lam)^2+‖x‖^2) ≤ ‖D lam x‖) :=
    (hτ.eventually self_mem_nhdsWithin).and hregular
  have hlim := tendsto_integral_filter_of_dominated_convergence
    (μ := (volume : Measure (ShapeSpace n))) (l := l)
    (F := fun lam x => rescaledShapeQuotient k (A lam) (D lam) (τ lam) x)
    (f := fun x => (shapeVandermondeSq x : ℂ)*a₀/
      ((Q : ℂ)+w*(‖x‖ : ℂ)^2)^(k+1))
    (fun x => (M/c^(k+1))*shapeMajorant k x) ?_ ?_ ?_ ?_
  · have he : (∫ x : ShapeSpace n, (shapeVandermondeSq x : ℂ)*a₀/
        ((Q : ℂ)+w*(‖x‖ : ℂ)^2)^(k+1)) =
        a₀*shapePeriodIntrinsic n k Q w := by
      rw [shapePeriodIntrinsic, ← integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by ring
    rw [he] at hlim
    apply hlim.congr'
    filter_upwards [hrange] with lam hlam
    exact (integral_edgeShapeQuotient_rescale hbalance (A lam) (D lam) hlam.1).symm
  · filter_upwards [hrange] with lam hlam
    exact (rescaledShapeQuotient_measurable k (τ lam) _ _ hlam.2.1 hlam.2.2.1).aestronglyMeasurable
  · filter_upwards [hrange] with lam hlam
    exact Eventually.of_forall fun x => norm_rescaledShapeQuotient_le hlam.1 hM hc _ _
      hlam.2.2.2.1 hlam.2.2.2.2 x
  · exact hmajorant.const_mul _
  · apply Eventually.of_forall
    intro x
    have hzero : (Q : ℂ)+w*(‖x‖ : ℂ)^2 ≠ 0 := by
      have hr : 0 < ((Q:ℂ)+w*(‖x‖:ℂ)^2).re := by
        simpa [pow_two,Complex.mul_re] using
          add_pos_of_pos_of_nonneg hQ (mul_nonneg hw.le (sq_nonneg ‖x‖))
      intro he
      rw [he] at hr
      exact lt_irrefl 0 hr
    exact ((tendsto_const_nhds.mul (hAlimit x)).div ((hDlimit x).pow (k+1))
      (pow_ne_zero _ hzero))


end
end IsingBulk.Joint.RegularEdges
