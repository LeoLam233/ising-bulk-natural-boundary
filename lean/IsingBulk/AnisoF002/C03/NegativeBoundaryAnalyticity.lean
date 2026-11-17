import IsingBulk.AnisoF002.C03.NegativeLowParticleSum

/-!
# What an analytic continuation would force on the full physical Taylor sum

The complete physical inward jets were proved by dominated differentiation.
Here an alleged analytic germ is compared with those actual jets, giving
one geometric coefficient bound at every order.  The conclusion refers to
the full infinite odd-particle sum, not a selected model or partial sum.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set Filter IsingBulk.AnisoF002.RegularTail.C03
open scoped Topology BigOperators

theorem physicalOddTaylorCoefficient_norm_summable {b B : ℂ → ℂ} {φ : ℝ}
    (hb : AnalyticAt ℂ b 0) (hB : AnalyticAt ℂ B 0)
    (hφ : 0 < φ) (hπ : φ < Real.pi) (hBi : (B 0).im < 0)
    (hbsq : ∀ t, b t ^ 2 = B t) (j : ℕ) :
    Summable (fun n => ‖physicalOddTaylorCoefficient b B φ j n‖) := by
  have hs := (physical_oddSum_boundary_jets hb hB hφ hπ hBi hbsq j).1
  simpa only [physicalOddTaylorCoefficient, norm_div, norm_natCast] using
    hs.div_const (j.factorial : ℝ)

theorem actual_complete_taylor_coefficient_of_inward_germ {b B g : ℂ → ℂ} {φ : ℝ}
    (hb : AnalyticAt ℂ b 0) (hB : AnalyticAt ℂ B 0)
    (hφ : 0 < φ) (hπ : φ < Real.pi) (hBi : (B 0).im < 0)
    (hbsq : ∀ t, b t ^ 2 = B t) (hg : AnalyticAt ℂ g 0)
    (heq : ∀ᶠ eps : ℝ in 𝓝[>] (0 : ℝ),
      negativePhysicalOddSum b B φ =ᶠ[𝓝 (-(eps : ℂ))] g) (j : ℕ) :
    (∑' n : ℕ, physicalOddTaylorCoefficient b B φ j n) =
      iteratedDeriv j g 0 / (j.factorial : ℂ) := by
  have hp := (physical_oddSum_boundary_jets hb hB hφ hπ hBi hbsq j).2
  have hgc : ContinuousAt (iteratedDeriv j g) 0 := by
    simpa only [iteratedDeriv_eq_iterate] using (hg.iterated_deriv j).continuousAt
  have hpath : Tendsto (fun eps : ℝ => -(eps : ℂ)) (𝓝[>] 0) (𝓝 (0 : ℂ)) := by
    simpa only [Complex.ofReal_zero, neg_zero] using
      ((Complex.continuous_ofReal.tendsto (0 : ℝ)).neg.mono_left nhdsWithin_le_nhds)
  have hgj := hgc.tendsto.comp hpath
  have hpg : Tendsto (fun eps : ℝ => iteratedDeriv j g (-(eps : ℂ)))
      (𝓝[>] 0)
      (𝓝 (∑' n : ℕ, iteratedDeriv j (negativePhysicalCoefficient b B φ (2 * n)) 0)) := by
    apply hp.congr'
    filter_upwards [heq] with eps he
    exact he.iteratedDeriv_eq j
  have hjet := tendsto_nhds_unique hpg hgj
  simp only [physicalOddTaylorCoefficient, tsum_div_const, hjet]

theorem analytic_germ_geometric_normalized_jet_bound {g : ℂ → ℂ}
    (hg : AnalyticAt ℂ g 0) :
    ∃ M R : ℝ, 0 < M ∧ 0 < R ∧ ∀ j : ℕ,
      ‖iteratedDeriv j g 0 / (j.factorial : ℂ)‖ ≤ M / R ^ j := by
  let M : ℝ := ‖g 0‖ + 1
  have hM : 0 < M := by dsimp [M]; positivity
  have hb : ∀ᶠ z in 𝓝 (0 : ℂ), ‖g z‖ < M :=
    hg.continuousAt.norm.eventually (Iio_mem_nhds (by dsimp [M]; linarith))
  obtain ⟨r, hr, hh⟩ := Metric.eventually_nhds_iff.mp (hg.eventually_analyticAt.and hb)
  have hsub : Metric.closedBall (0 : ℂ) (r / 2) ⊆ Metric.ball 0 r :=
    Metric.closedBall_subset_ball (by linarith)
  have hga : AnalyticOnNhd ℂ g (Metric.closedBall 0 (r / 2)) :=
    fun z hz => (hh (Metric.mem_ball.mp (hsub hz))).1
  have hgb : ∀ z ∈ Metric.closedBall (0 : ℂ) (r / 2), ‖g z‖ ≤ M :=
    fun z hz => (hh (Metric.mem_ball.mp (hsub hz))).2.le
  refine ⟨M, (r / 2) / 2, hM, by positivity, ?_⟩
  intro j
  have hj := common_disk_iteratedDeriv_bound (half_pos hr) hga hgb
    (Metric.mem_closedBall_self (by positivity : 0 ≤ (r / 2) / 2)) j
  rw [norm_div, norm_natCast]
  apply (div_le_iff₀ (by exact_mod_cast j.factorial_pos : (0 : ℝ) < j.factorial)).mpr
  convert hj using 1
  ring

theorem actual_complete_taylor_geometric_bound_of_inward_germ {b B g : ℂ → ℂ} {φ : ℝ}
    (hb : AnalyticAt ℂ b 0) (hB : AnalyticAt ℂ B 0)
    (hφ : 0 < φ) (hπ : φ < Real.pi) (hBi : (B 0).im < 0)
    (hbsq : ∀ t, b t ^ 2 = B t) (hg : AnalyticAt ℂ g 0)
    (heq : ∀ᶠ eps : ℝ in 𝓝[>] (0 : ℝ),
      negativePhysicalOddSum b B φ =ᶠ[𝓝 (-(eps : ℂ))] g) :
    ∃ M R : ℝ, 0 < M ∧ 0 < R ∧ ∀ j : ℕ,
      ‖∑' n : ℕ, physicalOddTaylorCoefficient b B φ j n‖ ≤ M / R ^ j := by
  obtain ⟨M, R, hM, hR, hbnd⟩ := analytic_germ_geometric_normalized_jet_bound hg
  refine ⟨M, R, hM, hR, ?_⟩
  intro j
  rw [actual_complete_taylor_coefficient_of_inward_germ hb hB hφ hπ hBi hbsq hg heq j]
  exact hbnd j

theorem no_analytic_inward_germ_of_actual_taylor_growth {b B : ℂ → ℂ} {φ : ℝ}
    (hb : AnalyticAt ℂ b 0) (hB : AnalyticAt ℂ B 0)
    (hφ : 0 < φ) (hπ : φ < Real.pi) (hBi : (B 0).im < 0)
    (hbsq : ∀ t, b t ^ 2 = B t)
    (hgrowth : ∀ M R : ℝ, 0 < M → 0 < R → ∃ j : ℕ,
      M / R ^ j < ‖∑' n : ℕ, physicalOddTaylorCoefficient b B φ j n‖) :
    ¬ ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧
      ∀ᶠ eps : ℝ in 𝓝[>] (0 : ℝ),
        negativePhysicalOddSum b B φ =ᶠ[𝓝 (-(eps : ℂ))] g := by
  rintro ⟨g, hg, heq⟩
  obtain ⟨M, R, hM, hR, hbound⟩ :=
    actual_complete_taylor_geometric_bound_of_inward_germ hb hB hφ hπ hBi hbsq hg heq
  obtain ⟨j, hj⟩ := hgrowth M R hM hR
  exact (not_lt_of_ge (hbound j)) hj

end
end IsingBulk.AnisoF002.NegativeHT
