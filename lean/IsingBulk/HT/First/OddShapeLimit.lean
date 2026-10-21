import IsingBulk.First.ShapeDominatedLimit
import IsingBulk.HT.First.OddShapeIntegrability

/-!
HT shape-rescaling and dominated convergence. Existing LT quotient definitions,
measurability, norm bounds, and weighted polar measure are reused. The new
geometric identity yields λ²=ε rather than λ=√ε as the normalization.
-/
namespace IsingBulk.HT.First
noncomputable section
open MeasureTheory Set Filter IsingBulk.First
open scoped Topology

theorem odd_localShapeQuotient_scale {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hdegree : n-1+(n+1)*n = 2*k-1)
    (A D : ShapeSpace n → ℂ) (lam : ℝ) (x : ShapeSpace n) :
    (lam^(n+2)) • localShapeQuotient k A D (lam • x) =
      rescaledShapeQuotient k A D lam x := by
  have hexp : n+2+(n+1)*n = 2*(k+1) := by omega
  simp only [localShapeQuotient,rescaledShapeQuotient,shapeVandermondeSq_homogeneous,
    Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_pow]
  rw [div_pow,div_div_eq_mul_div]
  have hp : (lam:ℂ)^(n+2)*(lam:ℂ)^((n+1)*n) = ((lam:ℂ)^2)^(k+1) := by
    rw [← pow_add,hexp,pow_mul]
  linear_combination (shapeVandermondeSq x:ℂ)*A (lam • x)/D (lam • x)^(k+1)*hp

theorem odd_integral_localShapeQuotient_rescale {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hdegree : n-1+(n+1)*n = 2*k-1) (A D : ShapeSpace n → ℂ)
    {lam : ℝ} (hlam : 0 < lam) :
    (lam^2) • (∫ x : ShapeSpace n,localShapeQuotient k A D x) =
      ∫ x : ShapeSpace n,rescaledShapeQuotient k A D lam x := by
  have hs := (volume:Measure (ShapeSpace n)).integral_comp_smul_of_nonneg
    (localShapeQuotient k A D) lam (hR := hlam.le)
  rw [finrank_shapeSpace] at hs
  have hchange : (∫ x : ShapeSpace n,localShapeQuotient k A D x) =
      lam^n • ∫ x : ShapeSpace n,localShapeQuotient k A D (lam • x) := by
    rw [hs,smul_smul,mul_inv_cancel₀ (pow_ne_zero _ hlam.ne'),one_smul]
  rw [hchange,smul_smul,← pow_add,show 2+n=n+2 by omega,← integral_smul]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => odd_localShapeQuotient_scale hn hk hdegree A D lam x

/-- Odd-order counterpart of the LT generic post-mean bridge. The analytic
bounds remain explicit premises here and must be instantiated from the actual
density; this helper is not a replacement for the physical FIRST theorem. -/
theorem postMean_odd_shape_dominated_limit {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hdegree : n-1+(n+1)*n = 2*k-1)
    (A D : ℝ → ShapeSpace n → ℂ) (a₀ : ℂ) {Q d M c lam₀ : ℝ}
    (hQ : 0 < Q) (hd : d ≠ 0) (hM : 0 ≤ M) (hc : 0 < c) (hlam₀ : 0 < lam₀)
    (hAmeas : ∀ lam ∈ Ioo 0 lam₀,Measurable (A lam))
    (hDmeas : ∀ lam ∈ Ioo 0 lam₀,Measurable (D lam))
    (hAbound : ∀ lam ∈ Ioo 0 lam₀,∀ x,‖A lam x‖ ≤ M)
    (hDbound : ∀ lam ∈ Ioo 0 lam₀,∀ x,A lam x ≠ 0 →
      c*(lam^2+‖x‖^2) ≤ ‖D lam x‖)
    (hAlimit : ∀ x,Tendsto (fun lam => A lam (lam • x)) (𝓝[>] 0) (𝓝 a₀))
    (hDlimit : ∀ x,Tendsto (fun lam => D lam (lam • x)/(lam:ℂ)^2)
      (𝓝[>] 0) (𝓝 ((Q:ℂ)-Complex.I*d*(‖x‖:ℂ)^2))) :
    Tendsto (fun lam => (lam^2) • ∫ x : ShapeSpace n,localShapeQuotient k (A lam) (D lam) x)
      (𝓝[>] 0) (𝓝 (a₀*shapePeriodIntrinsic n k Q (-Complex.I*d))) := by
  have hrange : ∀ᶠ lam : ℝ in 𝓝[>] 0,lam ∈ Ioo 0 lam₀ := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hlam₀).filter_mono nhdsWithin_le_nhds] with lam hp ht
    exact ⟨hp,ht⟩
  have hlim := tendsto_integral_filter_of_dominated_convergence
    (μ := (volume:Measure (ShapeSpace n))) (l := 𝓝[>] (0:ℝ))
    (F := fun lam x => rescaledShapeQuotient k (A lam) (D lam) lam x)
    (f := fun x => (shapeVandermondeSq x:ℂ)*a₀/
      ((Q:ℂ)-Complex.I*d*(‖x‖:ℂ)^2)^(k+1))
    (fun x => (M/c^(k+1))*shapeMajorant k x) ?_ ?_ ?_ ?_
  · have he : (∫ x : ShapeSpace n,(shapeVandermondeSq x:ℂ)*a₀/
        ((Q:ℂ)-Complex.I*d*(‖x‖:ℂ)^2)^(k+1)) =
        a₀*shapePeriodIntrinsic n k Q (-Complex.I*d) := by
      rw [shapePeriodIntrinsic,← integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by ring
    rw [he] at hlim
    apply hlim.congr'
    filter_upwards [hrange] with lam hlam
    exact (odd_integral_localShapeQuotient_rescale hn hk hdegree (A lam) (D lam) hlam.1).symm
  · filter_upwards [hrange] with lam hlam
    exact (rescaledShapeQuotient_measurable k lam _ _ (hAmeas _ hlam)
      (hDmeas _ hlam)).aestronglyMeasurable
  · filter_upwards [hrange] with lam hlam
    exact Eventually.of_forall fun x => norm_rescaledShapeQuotient_le hlam.1 hM hc _ _
      (hAbound _ hlam) (hDbound _ hlam) x
  · exact (odd_shapeMajorant_integrable hn hk hdegree).const_mul _
  · apply Eventually.of_forall
    intro x
    have hz : (Q:ℂ)-Complex.I*d*(‖x‖:ℂ)^2 ≠ 0 := by
      simpa [shapeQuadratic,sub_eq_add_neg] using odd_shapeQuadratic_ne_zero hQ hd ‖x‖
    exact (tendsto_const_nhds.mul (hAlimit x)).div ((hDlimit x).pow (k+1))
      (pow_ne_zero _ hz)

end
end IsingBulk.HT.First
