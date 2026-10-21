import IsingBulk.HT.First.OddShapeLowerOrders
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! The critical HT remainder need not be uniformly bounded: its ε-normalized
integral vanishes by a fixed-ball majorant of radial degree one. This avoids
assuming or importing the false HT analogue of the LT bounded-remainder lemma. -/
namespace IsingBulk.HT.First
noncomputable section
open MeasureTheory Set Metric Filter IsingBulk.First
open scoped Topology

private theorem damped_power_bound {epsilon t : ℝ} (he : 0 < epsilon)
    (ht : 0 < t) {k : ℕ} (hk : 1 ≤ k) :
    epsilon/(epsilon+t)^k ≤ 1/t^(k-1) := by
  rw [div_le_div_iff₀ (pow_pos (add_pos he ht) _) (pow_pos ht _),one_mul]
  calc
    epsilon*t^(k-1) ≤ (epsilon+t)*(epsilon+t)^(k-1) :=
      mul_le_mul (le_add_of_nonneg_right ht.le)
        (pow_le_pow_left₀ ht.le (le_add_of_nonneg_left he.le) _) (by positivity) (by positivity)
    _ = (epsilon+t)^k := by rw [← pow_succ',Nat.sub_add_cancel hk]

theorem norm_shape_pole_le {n k : ℕ} {M g : ℝ} (hM : 0 ≤ M)
    (hg : 0 < g) (x : ShapeSpace n) (a z : ℂ)
    (ha : ‖a‖ ≤ M) (hz : g ≤ ‖z‖) :
    ‖(shapeVandermondeSq x:ℂ)*a/z^k‖ ≤ shapeVandermondeSq x*M/g^k := by
  have hv := shapeVandermondeSq_nonneg x
  rw [norm_div,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hv,norm_pow]
  calc
    shapeVandermondeSq x*‖a‖/‖z‖^k ≤ shapeVandermondeSq x*M/‖z‖^k :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ha hv) (by positivity)
    _ ≤ shapeVandermondeSq x*M/g^k := div_le_div_of_nonneg_left
      (mul_nonneg hv hM) (pow_pos hg _) (pow_le_pow_left₀ hg.le hz _)

/-- Pointwise bound by the locally integrable pole of one lower order. -/
theorem norm_epsilon_shape_pole_le {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k)
    {epsilon M c : ℝ} (he : 0 < epsilon) (hM : 0 ≤ M) (hc : 0 < c)
    (x : ShapeSpace n) (a z : ℂ) (ha : ‖a‖ ≤ M)
    (hz : c*(epsilon+‖x‖^2) ≤ ‖z‖) :
    ‖epsilon • ((shapeVandermondeSq x:ℂ)*a/z^k)‖ ≤
      (M/c^k)*(shapeVandermondeSq x/‖x‖^(2*(k-1))) := by
  by_cases hx : x = 0
  · subst x
    simp [shapeVandermondeSq_zero hn]
  have ht : 0 < ‖x‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
  have hv := shapeVandermondeSq_nonneg x
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos he]
  calc
    epsilon*‖(shapeVandermondeSq x:ℂ)*a/z^k‖ ≤
        epsilon*(shapeVandermondeSq x*M/(c*(epsilon+‖x‖^2))^k) :=
      mul_le_mul_of_nonneg_left (norm_shape_pole_le hM (by positivity) x a z ha hz) he.le
    _ = ((M/c^k)*shapeVandermondeSq x)*(epsilon/(epsilon+‖x‖^2)^k) := by
      simp only [mul_pow,div_eq_mul_inv,mul_inv_rev]
      ring
    _ ≤ ((M/c^k)*shapeVandermondeSq x)*(1/(‖x‖^2)^(k-1)) :=
      mul_le_mul_of_nonneg_left (damped_power_bound he ht hk) (by positivity)
    _ = (M/c^k)*(shapeVandermondeSq x/‖x‖^(2*(k-1))) := by
      rw [pow_mul]
      ring

/-- Generic critical-pole limit on a fixed shape ball. Only local continuity,
a bounded amplitude, and the physical positive gap are required; no remainder
asymptotic or bounded integral is assumed. -/
theorem odd_remainder_setIntegral_epsilon_limit {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hdegree : n-1+(n+1)*n = 2*k-1)
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
  have hi := (shape_power_integrableOn hn (ell := k-1) (by omega) R).const_mul (M/c^k)
  have hlim := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (ball (0:ShapeSpace n) R)) (l := 𝓝[>] (0:ℝ))
    (F := fun epsilon x => epsilon • ((shapeVandermondeSq x:ℂ)*A epsilon x/(D epsilon x)^k))
    (f := fun _ => (0:ℂ))
    (fun x => (M/c^k)*(shapeVandermondeSq x/‖x‖^(2*(k-1)))) ?_ ?_ hi ?_
  · simpa only [integral_zero,integral_smul] using hlim
  · filter_upwards [hrange] with epsilon he
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_ball
    change ContinuousOn ((fun _ : ShapeSpace n => epsilon) •
      (fun x => (shapeVandermondeSq x:ℂ)*A epsilon x/(D epsilon x)^k)) (ball 0 R)
    apply continuousOn_const.smul
    apply ((Complex.continuous_ofReal.comp (shapeVandermondeSq_continuous n)).continuousOn.mul
      (hAcont epsilon he)).div ((hDcont epsilon he).pow k)
    intro x hx
    apply pow_ne_zero
    apply norm_pos_iff.mp
    exact lt_of_lt_of_le
      (mul_pos hc (add_pos_of_pos_of_nonneg he.1 (sq_nonneg ‖x‖)))
      (hDbound epsilon he x hx)
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
      · have hlim : Tendsto (fun epsilon : ℝ => epsilon) (𝓝[>] 0) (𝓝 0) :=
          tendsto_id.mono_left nhdsWithin_le_nhds
        simpa only [zero_mul] using hlim.mul_const
          (shapeVandermondeSq x*M/(c*‖x‖^2)^k)

end
end IsingBulk.HT.First
