import IsingBulk.HT.First.OddRemainderLimit

/-! ε-normalized subcritical poles. This includes the critical logarithmic
lower derivative without asserting that its unscaled integral is bounded. -/
namespace IsingBulk.HT.First
noncomputable section
open MeasureTheory Set Metric Filter IsingBulk.First
open scoped Topology

theorem subcritical_pole_setIntegral_epsilon_limit {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hdegree : 2*(k-1) ≤ n-1+(n+1)*n)
    (A D : ℝ → ShapeSpace n → ℂ) {R M c epsilon₀ : ℝ}
    (hM : 0 ≤ M) (hc : 0 < c) (hepsilon₀ : 0 < epsilon₀)
    (hAcont : ∀ epsilon ∈ Ioo 0 epsilon₀,ContinuousOn (A epsilon) (ball 0 R))
    (hDcont : ∀ epsilon ∈ Ioo 0 epsilon₀,ContinuousOn (D epsilon) (ball 0 R))
    (hAbound : ∀ epsilon ∈ Ioo 0 epsilon₀,∀ x ∈ ball 0 R,‖A epsilon x‖ ≤ M)
    (hDbound : ∀ epsilon ∈ Ioo 0 epsilon₀,∀ x ∈ ball 0 R,
      c*(epsilon+‖x‖^2) ≤ ‖D epsilon x‖) :
    Tendsto (fun epsilon : ℝ => epsilon • ∫ x : ShapeSpace n in ball 0 R,
      (shapeVandermondeSq x:ℂ)*A epsilon x/(D epsilon x)^k)
      (𝓝[>] 0) (𝓝 0) := by
  have hrange : ∀ᶠ epsilon : ℝ in 𝓝[>] 0,epsilon ∈ Ioo 0 epsilon₀ := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hepsilon₀).filter_mono nhdsWithin_le_nhds] with e hp ht
    exact ⟨hp,ht⟩
  have hi := (shape_power_integrableOn hn (ell := k-1) hdegree R).const_mul (M/c^k)
  have hlim := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (ball (0:ShapeSpace n) R)) (l := 𝓝[>] (0:ℝ))
    (F := fun epsilon x => epsilon • ((shapeVandermondeSq x:ℂ)*A epsilon x/(D epsilon x)^k))
    (f := fun _ => (0:ℂ))
    (fun x => (M/c^k)*(shapeVandermondeSq x/‖x‖^(2*(k-1)))) ?_ ?_ hi ?_
  · simpa only [integral_zero,integral_smul] using hlim
  · filter_upwards [hrange] with epsilon he
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_ball
    have hcont : ContinuousOn (fun x : ShapeSpace n =>
        (shapeVandermondeSq x:ℂ)*A epsilon x/(D epsilon x)^k) (ball 0 R) := by
      apply ((Complex.continuous_ofReal.comp (shapeVandermondeSq_continuous n)).continuousOn.mul
        (hAcont epsilon he)).div ((hDcont epsilon he).pow k)
      intro x hx
      apply pow_ne_zero
      apply norm_pos_iff.mp
      exact lt_of_lt_of_le
        (mul_pos hc (add_pos_of_pos_of_nonneg he.1 (sq_nonneg ‖x‖)))
        (hDbound epsilon he x hx)
    convert! hcont.const_smul epsilon using 1
  · filter_upwards [hrange] with epsilon he
    filter_upwards [self_mem_ae_restrict measurableSet_ball] with x hx
    exact norm_epsilon_shape_pole_le hn hk he.1 hM hc x _ _
      (hAbound epsilon he x hx) (hDbound epsilon he x hx)
  · filter_upwards [self_mem_ae_restrict measurableSet_ball] with x hx
    by_cases hx0 : x = 0
    · subst x
      simpa only [shapeVandermondeSq_zero hn,Complex.ofReal_zero,zero_mul,zero_div,smul_zero]
        using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0:ℂ)) (𝓝[>] 0) (𝓝 0))
    · have hg : 0 < c*‖x‖^2 := mul_pos hc (sq_pos_of_pos (norm_pos_iff.mpr hx0))
      apply squeeze_zero_norm' (a := fun epsilon : ℝ =>
        epsilon*(shapeVandermondeSq x*M/(c*‖x‖^2)^k))
      · filter_upwards [hrange] with epsilon he
        rw [norm_smul,Real.norm_eq_abs,abs_of_pos he.1]
        apply mul_le_mul_of_nonneg_left _ he.1.le
        apply norm_shape_pole_le hM hg x _ _ (hAbound epsilon he x hx)
        have hb := hDbound epsilon he x hx
        nlinarith [mul_pos hc he.1]
      · have hzero : Tendsto (fun epsilon : ℝ => epsilon) (𝓝[>] 0) (𝓝 0) :=
          tendsto_id.mono_left nhdsWithin_le_nhds
        simpa only [zero_mul] using hzero.mul_const
          (shapeVandermondeSq x*M/(c*‖x‖^2)^k)


end
end IsingBulk.HT.First
