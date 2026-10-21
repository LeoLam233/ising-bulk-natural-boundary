import IsingBulk.First.ShapeLimitTransfer

/-! Radial transfer of the genuinely odd λ² limit. -/
namespace IsingBulk.HT.First
noncomputable section
open Filter Set
open scoped Topology

/-- The odd shape normalization λ² transfers to the physical ε parameter. -/
theorem normalized_epsilon_limit_of_scale_limit {F : ℝ → ℂ} {L : ℂ}
    (h : Tendsto (fun lam : ℝ => (lam^2) • F (lam^2)) (𝓝[>] 0) (𝓝 L)) :
    Tendsto (fun epsilon : ℝ => epsilon • F epsilon) (𝓝[>] 0) (𝓝 L) := by
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
inverse written explicitly. -/
theorem normalized_epsilon_limit_isLittleO {F : ℝ → ℂ} {L : ℂ}
    (h : Tendsto (fun epsilon : ℝ => epsilon • F epsilon) (𝓝[>] 0) (𝓝 L)) :
    Asymptotics.IsLittleO (𝓝[>] (0 : ℝ))
      (fun epsilon => F epsilon - ((epsilon : ℂ)⁻¹)*L)
      (fun epsilon => (epsilon : ℂ)⁻¹) := by
  apply (Asymptotics.isLittleO_iff_tendsto' ?_).mpr
  · have hz : Tendsto (fun epsilon : ℝ => epsilon • F epsilon - L)
        (𝓝[>] 0) (𝓝 0) := by simpa using h.sub_const L
    apply hz.congr'
    filter_upwards [self_mem_nhdsWithin] with epsilon he
    have hn : (epsilon : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr he.ne'
    simp only [Complex.real_smul]
    field_simp
  · filter_upwards [self_mem_nhdsWithin] with epsilon he
    have hn : (epsilon : ℂ)⁻¹ ≠ 0 :=
      inv_ne_zero (Complex.ofReal_ne_zero.mpr he.ne')
    exact fun hx => False.elim (hn hx)

/-- Any LT mean-error estimate o(ε⁻¹ᐟ²) is also negligible on the HT ε⁻¹ scale.
This is a limit transfer only; the actual mean-error estimate is reused. -/
theorem epsilon_limit_of_sqrt_limit_zero {F : ℝ → ℂ}
    (h : Tendsto (fun epsilon : ℝ => Real.sqrt epsilon • F epsilon)
      (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun epsilon : ℝ => epsilon • F epsilon) (𝓝[>] 0) (𝓝 0) := by
  have hs : Tendsto Real.sqrt (𝓝[>] (0:ℝ)) (𝓝 0) := by
    simpa only [Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds
  have ht := hs.smul h
  simp only [zero_smul] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with epsilon he
  rw [smul_smul,← pow_two,Real.sq_sqrt he.le]

/-- Any actually bounded radial term is negligible on the ε⁻¹ scale. -/
theorem bounded_radial_term_epsilon_isLittleO {f : ℝ → ℂ} {C e : ℝ}
    (he : 0 < e) (hb : ∀ epsilon : ℝ,0 < epsilon → epsilon ≤ e → ‖f epsilon‖ ≤ C) :
    Asymptotics.IsLittleO (𝓝[>] (0:ℝ)) f (fun epsilon => (epsilon:ℂ)⁻¹) := by
  have hid : Tendsto (fun epsilon : ℝ => epsilon) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hbounded : IsBoundedUnder (· ≤ ·) (𝓝[>] (0:ℝ)) (norm ∘ f) := by
    refine ⟨C,eventually_map.mpr ?_⟩
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds he).filter_mono nhdsWithin_le_nhds] with epsilon hp hs
    exact hb epsilon hp hs.le
  have hz : Tendsto (fun epsilon : ℝ => epsilon • f epsilon) (𝓝[>] 0) (𝓝 (0:ℂ)) := by
    simpa only [Pi.smul_apply] using!
      NormedField.tendsto_zero_smul_of_tendsto_zero_of_bounded hid hbounded
  simpa only [mul_zero,sub_zero] using normalized_epsilon_limit_isLittleO hz

end
end IsingBulk.HT.First
