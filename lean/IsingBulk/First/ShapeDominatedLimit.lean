import IsingBulk.First.ShapeRescaling
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Post-mean dominated limits for the genuine constrained shape space.
The physical amplitude, denominator estimates and local limits are explicit
application obligations; none is counted as proved by this generic bridge. -/
namespace IsingBulk.First
noncomputable section
open MeasureTheory Set Filter
open scoped Topology

/-- A bound for the actual constrained quotient with a separated scaled denominator. -/
theorem norm_shapeQuotient_le {n k : ℕ} {M c : ℝ} (hM : 0 ≤ M) (hc : 0 < c)
    (x : ShapeSpace n) (a z : ℂ) (ha : ‖a‖ ≤ M)
    (hz : c*(1+‖x‖^2) ≤ ‖z‖) :
    ‖(shapeVandermondeSq x : ℂ)*a/z^(k+1)‖ ≤
      (M/(c^(k+1))) * shapeMajorant k x := by
  have hx := shapeVandermondeSq_nonneg x
  rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx, norm_pow]
  calc
    shapeVandermondeSq x * ‖a‖ / ‖z‖^(k+1)
        ≤ shapeVandermondeSq x * M / (c*(1+‖x‖^2))^(k+1) := by
      calc
        _ ≤ shapeVandermondeSq x * M / ‖z‖^(k+1) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ha hx) (by positivity)
        _ ≤ _ := div_le_div_of_nonneg_left (mul_nonneg hx hM) (by positivity)
          (pow_le_pow_left₀ (by positivity) hz _)
    _ = (M/(c^(k+1))) * shapeMajorant k x := by
      simp only [shapeMajorant, mul_pow, div_eq_mul_inv, mul_inv_rev]
      ring

/-- The nonlinear physical gap yields a fixed scaled denominator lower bound. -/
theorem scaled_shapeDenominator_lower {n : ℕ} {lam c : ℝ} (hlam : 0 < lam)
    (x : ShapeSpace n) (D : ShapeSpace n → ℂ)
    (hD : c*(lam^2+‖lam • x‖^2) ≤ ‖D (lam • x)‖) :
    c*(1+‖x‖^2) ≤ ‖D (lam • x)/(lam : ℂ)^2‖ := by
  have hn : ‖lam • x‖^2 = lam^2*‖x‖^2 := by rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [le_div_iff₀ (sq_pos_of_pos hlam)]
  rw [hn] at hD
  convert hD using 1; ring

/-- The actual rescaled quotient is uniformly controlled by the already proved
integrable source majorant, including points outside the amplitude support. -/
theorem norm_rescaledShapeQuotient_le {n k : ℕ} {lam M c : ℝ}
    (hlam : 0 < lam) (hM : 0 ≤ M) (hc : 0 < c)
    (A D : ShapeSpace n → ℂ)
    (hA : ∀ x, ‖A x‖ ≤ M)
    (hD : ∀ x, A x ≠ 0 → c*(lam^2+‖x‖^2) ≤ ‖D x‖)
    (x : ShapeSpace n) :
    ‖rescaledShapeQuotient k A D lam x‖ ≤ (M/c^(k+1))*shapeMajorant k x := by
  by_cases hx : A (lam • x) = 0
  · simp only [rescaledShapeQuotient, hx, mul_zero, zero_div, norm_zero]
    exact mul_nonneg (div_nonneg hM (pow_nonneg hc.le _))
      (div_nonneg (shapeVandermondeSq_nonneg x) (by positivity))
  · exact norm_shapeQuotient_le hM hc x _ _ (hA _)
      (scaled_shapeDenominator_lower hlam x D (hD _ hx))

/-- Measurability of the actual rescaled expression follows from its two
measurable source factors and the fixed continuous shape polynomial. -/
theorem rescaledShapeQuotient_measurable {n : ℕ} (k : ℕ) (lam : ℝ)
    (A D : ShapeSpace n → ℂ) (hA : Measurable A) (hD : Measurable D) :
    Measurable (rescaledShapeQuotient k A D lam) := by
  have hp := (shapeVandermondeSq_continuous n).measurable
  have ha := hA.comp (continuous_const_smul lam).measurable
  have hd := hD.comp (continuous_const_smul lam).measurable
  unfold rescaledShapeQuotient
  exact ((Complex.continuous_ofReal.measurable.comp hp).mul ha).div
    ((hd.div_const _).pow_const _)

/-- A dominated limit of the post-mean shape integral. The hypotheses are
pointwise/local coefficient limits and parameter-independent physical bounds;
this theorem never moves an angular cutoff through the mean contour. -/
theorem postMean_shape_dominated_limit {n k : ℕ} (hn : 1 ≤ n)
    (hdegree : n-1+(n+1)*n = 2*k)
    (A D : ℝ → ShapeSpace n → ℂ) (a₀ : ℂ) {Q d M c lam₀ : ℝ}
    (hQ : 0 < Q) (hd : 0 < d) (hM : 0 ≤ M) (hc : 0 < c) (hlam₀ : 0 < lam₀)
    (hAmeas : ∀ lam ∈ Ioo 0 lam₀, Measurable (A lam))
    (hDmeas : ∀ lam ∈ Ioo 0 lam₀, Measurable (D lam))
    (hAbound : ∀ lam ∈ Ioo 0 lam₀, ∀ x, ‖A lam x‖ ≤ M)
    (hDbound : ∀ lam ∈ Ioo 0 lam₀, ∀ x, A lam x ≠ 0 →
      c*(lam^2+‖x‖^2) ≤ ‖D lam x‖)
    (hAlimit : ∀ x, Tendsto (fun lam => A lam (lam • x)) (𝓝[>] 0) (𝓝 a₀))
    (hDlimit : ∀ x, Tendsto (fun lam => D lam (lam • x)/(lam : ℂ)^2)
      (𝓝[>] 0) (𝓝 ((Q : ℂ)-Complex.I*d*(‖x‖ : ℂ)^2))) :
    Tendsto (fun lam => lam • ∫ x : ShapeSpace n, localShapeQuotient k (A lam) (D lam) x)
      (𝓝[>] 0) (𝓝 (a₀*shapePeriodIntrinsic n k Q (-Complex.I*d))) := by
  have hrange : ∀ᶠ lam : ℝ in 𝓝[>] 0, lam ∈ Ioo 0 lam₀ := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hlam₀).filter_mono nhdsWithin_le_nhds] with lam hpos hlt
    exact ⟨hpos, hlt⟩
  have hlim := tendsto_integral_filter_of_dominated_convergence
    (μ := (volume : Measure (ShapeSpace n))) (l := 𝓝[>] (0 : ℝ))
    (F := fun lam x => rescaledShapeQuotient k (A lam) (D lam) lam x)
    (f := fun x => (shapeVandermondeSq x : ℂ)*a₀/
      ((Q : ℂ)-Complex.I*d*(‖x‖ : ℂ)^2)^(k+1))
    (fun x => (M/c^(k+1))*shapeMajorant k x) ?_ ?_ ?_ ?_
  · have he : (∫ x : ShapeSpace n, (shapeVandermondeSq x : ℂ)*a₀/
        ((Q : ℂ)-Complex.I*d*(‖x‖ : ℂ)^2)^(k+1)) =
        a₀*shapePeriodIntrinsic n k Q (-Complex.I*d) := by
      rw [shapePeriodIntrinsic, ← integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by ring
    rw [he] at hlim
    apply hlim.congr'
    filter_upwards [hrange] with lam hlam
    exact (integral_localShapeQuotient_rescale hn hdegree (A lam) (D lam) hlam.1).symm
  · filter_upwards [hrange] with lam hlam
    exact (rescaledShapeQuotient_measurable k lam _ _ (hAmeas _ hlam) (hDmeas _ hlam)).aestronglyMeasurable
  · filter_upwards [hrange] with lam hlam
    exact Eventually.of_forall fun x => norm_rescaledShapeQuotient_le hlam.1 hM hc _ _
      (hAbound _ hlam) (hDbound _ hlam) x
  · exact (shapeMajorant_integrable hn hdegree).const_mul _
  · apply Eventually.of_forall
    intro x
    have hzero : (Q : ℂ)-Complex.I*d*(‖x‖ : ℂ)^2 ≠ 0 := by
      simpa [shapeQuadratic, sub_eq_add_neg] using
        shapeQuadratic_boundary_ne_zero hQ hd (δ := 0) (le_refl 0) ‖x‖
    exact ((tendsto_const_nhds.mul (hAlimit x)).div ((hDlimit x).pow (k+1))
      (pow_ne_zero _ hzero))

end
end IsingBulk.First
