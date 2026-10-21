import IsingBulk.HT.Final.OriginDecay

/-! Internally constructed full HT analytic germ on the complete unit disk.
The origin is filled using a proved source bound and the removable singularity
theorem. The physical representation only identifies its positive real germ. -/
namespace IsingBulk.HT.Final
noncomputable section
open IsingBulk.First IsingBulk.Tail Set Filter Metric Function
open scoped Topology BigOperators

def interiorRawSeries (s : ℂ) : ℂ := s⁻¹*exteriorOddSeries (s⁻¹)

def regularInteriorSeries : ℂ → ℂ :=
  update interiorRawSeries 0 (limUnder (𝓝[≠] (0:ℂ)) interiorRawSeries)

def interiorFourthFactor (s : ℂ) : ℂ := (1-s^4)^(1/4:ℂ)

def interiorFullBulk (s : ℂ) : ℂ := interiorFourthFactor s*regularInteriorSeries s

theorem interiorRawSeries_analyticAt {s : ℂ} (hs0 : s ≠ 0) (hs : ‖s‖ < 1) :
    AnalyticAt ℂ interiorRawSeries s := by
  have hi : 1 < ‖s⁻¹‖ := by
    rw [norm_inv]
    exact (one_lt_inv₀ (norm_pos_iff.mpr hs0)).mpr hs
  exact (analyticAt_id.inv hs0).mul
    ((exteriorOddSeries_analyticAt hi).comp (analyticAt_id.inv hs0))

theorem interiorRawSeries_bound {s : ℂ} (hs0 : s ≠ 0) (hs : ‖s‖ < 1/16) :
    ‖interiorRawSeries s‖ ≤ originMajorant := by
  have hi : 16 < ‖s⁻¹‖ := by
    rw [norm_inv,inv_eq_one_div]
    apply (lt_div_iff₀ (norm_pos_iff.mpr hs0)).mpr
    linarith
  exact exteriorOddSeries_scaled_bound hi

theorem regularInteriorSeries_eq {s : ℂ} (hs : s ≠ 0) :
    regularInteriorSeries s = interiorRawSeries s := by
  exact update_of_ne hs _ _

theorem regularInteriorSeries_analyticAt_zero : AnalyticAt ℂ regularInteriorSeries 0 := by
  let U : Set ℂ := ball 0 (1/16)
  have hU : U ∈ 𝓝 (0:ℂ) := ball_mem_nhds _ (by norm_num)
  have hd : DifferentiableOn ℂ interiorRawSeries (U \ {0}) := by
    intro s hs
    have hs0 : s ≠ 0 := hs.2
    have hn : ‖s‖ < 1/16 := by simpa only [U,mem_ball,dist_zero_right] using hs.1
    exact (interiorRawSeries_analyticAt hs0 (by linarith)).differentiableAt.differentiableWithinAt
  have hb : BddAbove (norm ∘ interiorRawSeries '' (U \ {0})) := by
    refine ⟨originMajorant,?_⟩
    rintro y ⟨s,hs,rfl⟩
    have hn : ‖s‖ < 1/16 := by simpa only [U,mem_ball,dist_zero_right] using hs.1
    exact interiorRawSeries_bound hs.2 hn
  exact (Complex.differentiableOn_update_limUnder_of_bddAbove hU hd hb).analyticAt hU

theorem regularInteriorSeries_analyticOn :
    AnalyticOnNhd ℂ regularInteriorSeries {s : ℂ | ‖s‖ < 1} := by
  intro s hs
  by_cases hs0 : s = 0
  · simpa only [hs0] using regularInteriorSeries_analyticAt_zero
  · apply (interiorRawSeries_analyticAt hs0 hs).congr
    filter_upwards [eventually_ne_nhds hs0] with t ht
    exact (regularInteriorSeries_eq ht).symm

theorem interiorFourthFactor_analyticAt {s : ℂ} (hs : ‖s‖ < 1) :
    AnalyticAt ℂ interiorFourthFactor s := by
  have hp : 0 < (1-s^4).re := by
    have hpow : ‖s^4‖ < 1 := by
      rw [norm_pow]
      exact pow_lt_one₀ (norm_nonneg _) hs (by norm_num)
    have hre := Complex.re_le_norm (s^4)
    simp only [Complex.sub_re,Complex.one_re]
    linarith
  have ha : AnalyticAt ℂ (fun t : ℂ => 1-t^4) s := analyticAt_const.sub (analyticAt_id.pow 4)
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  have he := ha.eventually_analyticAt
  have hplane := ha.continuousAt.eventually
    (Complex.isOpen_slitPlane.mem_nhds (Or.inl hp : 1-s^4 ∈ Complex.slitPlane))
  filter_upwards [he,hplane] with t ht htp
  exact ht.differentiableAt.cpow_const htp

/-- The full disk analyticity is constructed internally, including s=0. -/
theorem interiorFullBulk_analyticOn :
    AnalyticOnNhd ℂ interiorFullBulk {s : ℂ | ‖s‖ < 1} := by
  intro s hs
  exact (interiorFourthFactor_analyticAt hs).mul (regularInteriorSeries_analyticOn s hs)

/-- On the punctured disk this is exactly inversion of the full-site odd
exterior source, including the prescribed HT fourth-root factor. -/
theorem interiorFullBulk_eq_exterior {s : ℂ} (hs0 : s ≠ 0) :
    interiorFullBulk s = exteriorFullBulk (s⁻¹) := by
  rw [interiorFullBulk,regularInteriorSeries_eq hs0]
  simp only [interiorFourthFactor,interiorRawSeries,exteriorFullBulk,
    exteriorPrefactor,magnetizationSquared,inv_pow,inv_inv]
  ring

/-- The only external physical input is the stated real bulk expansion.
It identifies the internally proved analytic germ, not its boundary theorem. -/
theorem interiorFullBulk_physical_real_germ {X : ℂ → ℂ}
    (hrep : RealFullBulkRepresentation X) {x : ℝ} (hx : 0 < x) (hxsmall : x < 1/16) :
    X (x:ℂ) = interiorFullBulk (x:ℂ) := by
  have hx0 : (x:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hi : 16 < ‖((x:ℂ)⁻¹)‖ := by
    rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hx,inv_eq_one_div]
    apply (lt_div_iff₀ hx).mpr
    linarith
  rw [interiorFullBulk_eq_exterior hx0,exteriorFullBulk_eq_quarter_far hi]
  exact normalized_real_germ_identification hrep hx hxsmall

end
end IsingBulk.HT.Final
