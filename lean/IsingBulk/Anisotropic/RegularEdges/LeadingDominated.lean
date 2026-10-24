import IsingBulk.First.ShapeDominatedLimit

namespace IsingBulk.Anisotropic.RegularEdges
noncomputable section
open IsingBulk.First MeasureTheory Set Filter
open scoped Topology

theorem edgeShapeQuotient_scale {n k a : ℕ}
    (hbalance : n+a+(n+1)*n=2*(k+1))
    (A D : ShapeSpace n→ℂ) (t : ℝ) (x : ShapeSpace n) :
    (t^(n+a)) • localShapeQuotient k A D (t • x)=rescaledShapeQuotient k A D t x := by
  simp only [localShapeQuotient,rescaledShapeQuotient,shapeVandermondeSq_homogeneous,
    Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_pow]
  rw [div_pow,div_div_eq_mul_div]
  have hp : (t:ℂ)^(n+a)*(t:ℂ)^((n+1)*n)=((t:ℂ)^2)^(k+1) := by
    rw [←pow_add,hbalance,pow_mul]
  linear_combination (shapeVandermondeSq x:ℂ)*A (t • x)/D (t • x)^(k+1)*hp

theorem integral_edgeShapeQuotient_rescale {n k a : ℕ}
    (hbalance : n+a+(n+1)*n=2*(k+1)) (A D : ShapeSpace n→ℂ)
    {t : ℝ} (ht : 0<t) :
    (t^a) • (∫ x : ShapeSpace n,localShapeQuotient k A D x)=
      ∫ x : ShapeSpace n,rescaledShapeQuotient k A D t x := by
  have hs := (volume : Measure (ShapeSpace n)).integral_comp_smul_of_nonneg
    (localShapeQuotient k A D) t (hR := ht.le)
  rw [finrank_shapeSpace] at hs
  have he : (∫ x : ShapeSpace n,localShapeQuotient k A D x)=
      t^n • ∫ x : ShapeSpace n,localShapeQuotient k A D (t • x) := by
    rw [hs,smul_smul,mul_inv_cancel₀ (pow_ne_zero _ ht.ne'),one_smul]
  rw [he,smul_smul,←pow_add,add_comm a n,←integral_smul]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => edgeShapeQuotient_scale hbalance A D t x

theorem edge_shape_dominated_limit {n k a : ℕ}
    (hbalance : n+a+(n+1)*n=2*(k+1))
    (hmajorant : Integrable (@shapeMajorant n k))
    (A D : ℝ → ShapeSpace n → ℂ) (a₀ : ℂ) {Q M c lam₀ : ℝ} {w : ℂ}
    (hQ : 0 < Q) (hw : 0 < w.re) (hM : 0 ≤ M) (hc : 0 < c) (hlam₀ : 0 < lam₀)
    (hAmeas : ∀ lam ∈ Ioo 0 lam₀, Measurable (A lam))
    (hDmeas : ∀ lam ∈ Ioo 0 lam₀, Measurable (D lam))
    (hAbound : ∀ lam ∈ Ioo 0 lam₀, ∀ x, ‖A lam x‖ ≤ M)
    (hDbound : ∀ lam ∈ Ioo 0 lam₀, ∀ x, A lam x ≠ 0 →
      c*(lam^2+‖x‖^2) ≤ ‖D lam x‖)
    (hAlimit : ∀ x, Tendsto (fun lam => A lam (lam • x)) (𝓝[>] 0) (𝓝 a₀))
    (hDlimit : ∀ x, Tendsto (fun lam => D lam (lam • x)/(lam : ℂ)^2)
      (𝓝[>] 0) (𝓝 ((Q : ℂ)+w*(‖x‖ : ℂ)^2))) :
    Tendsto (fun lam => (lam^a) • ∫ x : ShapeSpace n, localShapeQuotient k (A lam) (D lam) x)
      (𝓝[>] 0) (𝓝 (a₀*shapePeriodIntrinsic n k Q w)) := by
  have hrange : ∀ᶠ lam : ℝ in 𝓝[>] 0, lam ∈ Ioo 0 lam₀ := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hlam₀).filter_mono nhdsWithin_le_nhds] with lam hpos hlt
    exact ⟨hpos, hlt⟩
  have hlim := tendsto_integral_filter_of_dominated_convergence
    (μ := (volume : Measure (ShapeSpace n))) (l := 𝓝[>] (0 : ℝ))
    (F := fun lam x => rescaledShapeQuotient k (A lam) (D lam) lam x)
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
    exact (rescaledShapeQuotient_measurable k lam _ _ (hAmeas _ hlam) (hDmeas _ hlam)).aestronglyMeasurable
  · filter_upwards [hrange] with lam hlam
    exact Eventually.of_forall fun x => norm_rescaledShapeQuotient_le hlam.1 hM hc _ _
      (hAbound _ hlam) (hDbound _ hlam) x
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
end IsingBulk.Anisotropic.RegularEdges
