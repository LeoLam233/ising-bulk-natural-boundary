import IsingBulk.First.ShapeDominatedLimit
import Mathlib.Analysis.Asymptotics.Lemmas

/-! Exact coordinate and radial-parameter transfers for post-mean shape limits. -/
namespace IsingBulk.First
noncomputable section
open MeasureTheory Set Filter
open scoped Topology

theorem coordinate_normalized_shape_limit {n : ℕ} {F : ℝ → ShapeSpace n → ℂ} {L : ℂ}
    (h : Tendsto (fun lam : ℝ => lam • ∫ x : ShapeSpace n, F lam x)
      (𝓝[>] 0) (𝓝 L)) :
    Tendsto (fun lam : ℝ => lam • ∫ t : Fin n → ℝ,
        F lam (shapeCoordinateEquiv n (WithLp.toLp 2 t)))
      (𝓝[>] 0) (𝓝 ((Real.sqrt (n+1))⁻¹ • L)) := by
  have ht := h.const_smul (Real.sqrt (n+1))⁻¹
  apply ht.congr'
  exact Eventually.of_forall fun lam => by
    dsimp only
    rw [integral_shapeExtend n (F lam), smul_comm]

/-- Conversion from the square-root variable to the actual ε→0+ radial parameter. -/
theorem normalized_sqrt_limit_of_scale_limit {F : ℝ → ℂ} {L : ℂ}
    (h : Tendsto (fun lam : ℝ => lam • F (lam^2)) (𝓝[>] 0) (𝓝 L)) :
    Tendsto (fun epsilon : ℝ => Real.sqrt epsilon • F epsilon) (𝓝[>] 0) (𝓝 L) := by
  have hs : Tendsto Real.sqrt (𝓝[>] (0 : ℝ)) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · simpa using (Real.continuous_sqrt.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with epsilon he
      exact Real.sqrt_pos.mpr he
  have ht := h.comp hs
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with epsilon he
  simp only [Function.comp_apply, Real.sq_sqrt (le_of_lt he)]

/-- The normalized limit is precisely the source leading asymptotic, with the
square-root inverse written explicitly. -/
theorem normalized_sqrt_limit_isLittleO {F : ℝ → ℂ} {L : ℂ}
    (h : Tendsto (fun epsilon : ℝ => Real.sqrt epsilon • F epsilon) (𝓝[>] 0) (𝓝 L)) :
    Asymptotics.IsLittleO (𝓝[>] (0 : ℝ))
      (fun epsilon => F epsilon - ((Real.sqrt epsilon : ℂ)⁻¹)*L)
      (fun epsilon => (Real.sqrt epsilon : ℂ)⁻¹) := by
  apply (Asymptotics.isLittleO_iff_tendsto' ?_).mpr
  · have hz : Tendsto (fun epsilon : ℝ => Real.sqrt epsilon • F epsilon - L)
        (𝓝[>] 0) (𝓝 0) := by simpa using h.sub_const L
    apply hz.congr'
    filter_upwards [self_mem_nhdsWithin] with epsilon he
    have hn : (Real.sqrt epsilon : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr he).ne'
    simp only [Complex.real_smul]
    field_simp
  · filter_upwards [self_mem_nhdsWithin] with epsilon he
    have hn : (Real.sqrt epsilon : ℂ)⁻¹ ≠ 0 :=
      inv_ne_zero (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr he).ne')
    exact fun hx => False.elim (hn hx)

/-- Agreement with the manuscript's real negative-half-power convention. -/
theorem inverse_sqrt_eq_negative_half_rpow {epsilon : ℝ} (he : 0 < epsilon) :
    (Real.sqrt epsilon)⁻¹ = epsilon ^ (-1/2 : ℝ) := by
  rw [show (-1/2 : ℝ) = -(1/2) by ring, Real.rpow_neg he.le, Real.sqrt_eq_rpow]

end
end IsingBulk.First
