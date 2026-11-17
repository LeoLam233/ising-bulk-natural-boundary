import IsingBulk.AnisoF002.C03.NegativeUniformPole

/-!
# Analyticity of the uniformly constructed constrained poles

Uniqueness on the fixed temperature disk patches local analytic implicit
functions.  Continuity or analyticity of the globally selected zero is
proved by this argument and is not assumed.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set Filter
open scoped Topology BigOperators

theorem analyticAt_of_unique_implicit_zeros
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {F : E × ℂ → ℂ} {T : E → ℂ} {V : Set E} {U : Set ℂ} {x : E}
    (hV : V ∈ 𝓝 x) (hU : IsOpen U) (hTx : T x ∈ U)
    (hF : AnalyticAt ℂ F (x, T x))
    (hD : fderiv ℂ F (x, T x) (0, 1) ≠ 0)
    (hzero : ∀ y ∈ V, F (y, T y) = 0)
    (hunique : ∀ y ∈ V, ∀ t ∈ U, F (y, t) = 0 → t = T y) :
    AnalyticAt ℂ T x := by
  have hx : x ∈ V := mem_of_mem_nhds hV
  obtain ⟨S, hSa, hSx, hSe, _⟩ := exists_analytic_scalar_implicit
    F (x, T x) (fderiv ℂ F (x, T x)) hF hF.differentiableAt.hasFDerivAt hD
  have hSin : ∀ᶠ y in 𝓝 x, S y ∈ U :=
    hSa.continuousAt.eventually (hU.mem_nhds (by simpa only [hSx] using hTx))
  apply hSa.congr
  filter_upwards [hV, hSin, hSe] with y hy hSy he
  exact hunique y hy (S y) hSy (by simpa only [hzero x hx] using he)

def zeroSumDisplacements (n : ℕ) : Submodule ℂ (Fin n → ℂ) := (angleSum n).ker

theorem zeroSumDisplacements_sum {n : ℕ} (v : zeroSumDisplacements n) :
    (∑ i, (v : Fin n → ℂ) i) = 0 := by
  have hv := v.property
  change angleSum n (v : Fin n → ℂ) = 0 at hv
  rwa [angleSum_apply] at hv

def constrainedPhaseAverage (n : ℕ) (g : ℂ × ℂ → ℂ) (γ d : ℂ)
    (a : zeroSumDisplacements n × ℂ) : ℂ :=
  centeredPhaseAverage n g γ d (a.1 : Fin n → ℂ) a.2

theorem constrainedPhaseAverage_analyticAt (n : ℕ) (g : ℂ × ℂ → ℂ) (γ d : ℂ)
    (a : zeroSumDisplacements n × ℂ)
    (hg : ∀ i, AnalyticAt ℂ g (a.2, d + (a.1 : Fin n → ℂ) i)) :
    AnalyticAt ℂ (constrainedPhaseAverage n g γ d) a := by
  let proj (i : Fin n) : zeroSumDisplacements n →L[ℂ] ℂ :=
    (ContinuousLinearMap.proj i).comp (zeroSumDisplacements n).subtypeL
  have hs : AnalyticAt ℂ
      (fun a : zeroSumDisplacements n × ℂ =>
        ∑ i, (g (a.2, d + (a.1 : Fin n → ℂ) i) - γ)) a := by
    apply Finset.analyticAt_fun_sum
    intro i _
    have hi : AnalyticAt ℂ
        (fun a : zeroSumDisplacements n × ℂ => (a.2, d + (a.1 : Fin n → ℂ) i)) a :=
      analyticAt_snd.prod (analyticAt_const.add (((proj i).analyticAt _).comp analyticAt_fst))
    exact ((hg i).comp_of_eq hi rfl).sub analyticAt_const
  exact hs.div_const

theorem constrainedPhaseAverage_temp_deriv (n : ℕ) (g : ℂ × ℂ → ℂ) (γ d : ℂ)
    (v : zeroSumDisplacements n) (t : ℂ)
    (hF : DifferentiableAt ℂ (constrainedPhaseAverage n g γ d) (v, t)) :
    deriv (centeredPhaseAverage n g γ d (v : Fin n → ℂ)) t =
      fderiv ℂ (constrainedPhaseAverage n g γ d) (v, t) (0, 1) := by
  exact (hF.hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_const t v).prodMk (hasDerivAt_id t))).deriv

theorem exists_uniform_analytic_zero_sum_poles {g : ℂ × ℂ → ℂ}
    (hg : AnalyticAt ℂ g (0, 0))
    (hc : fderiv ℂ g (0, 0) (1, 0) ≠ 0) :
    ∃ r σ C : ℝ, 0 < r ∧ 0 < σ ∧ 0 < C ∧
      ∀ (n : ℕ), 0 < n → ∀ τ d γ : ℂ,
        ‖τ‖ < r / 4 → ‖d‖ < r / 4 → g (τ, d) = γ →
        ∃ T : zeroSumDisplacements n → ℂ,
          AnalyticOnNhd ℂ T (Metric.ball 0 σ) ∧ T 0 = τ ∧
          ∀ v ∈ Metric.ball 0 σ,
            (∑ i, g (T v, d + (v : Fin n → ℂ) i)) = (n : ℂ) * γ ∧
            ‖T v - τ‖ ≤ r / 8 ∧
            ‖T v - τ‖ ≤ C * displacementSquare n (v : Fin n → ℂ) / (n : ℝ) ∧
            deriv (centeredPhaseAverage n g γ d (v : Fin n → ℂ)) (T v) ≠ 0 ∧
            ∀ u ∈ Metric.closedBall τ (r / 4),
              (∑ i, g (u, d + (v : Fin n → ℂ) i)) = (n : ℂ) * γ → u = T v := by
  classical
  obtain ⟨r, σ, C, hr, hσ, hC, hσr, hga, hex⟩ := exists_uniform_zero_sum_phase_zeros hg hc
  refine ⟨r, σ, C, hr, hσ, hC, ?_⟩
  intro n hn τ d γ hτ hd hcenter
  have hex' (v : zeroSumDisplacements n) (hv : v ∈ Metric.ball 0 σ) :=
    hex n hn τ d γ hτ hd hcenter (v : Fin n → ℂ) (zeroSumDisplacements_sum v)
      (fun i => (norm_le_pi_norm (v : Fin n → ℂ) i).trans_lt
        (by simpa only [Metric.mem_ball, dist_zero_right, Submodule.norm_coe] using hv))
  let T : zeroSumDisplacements n → ℂ := fun v =>
    if hv : v ∈ Metric.ball 0 σ then (hex' v hv).choose else τ
  have hT (v : zeroSumDisplacements n) (hv : v ∈ Metric.ball 0 σ) :
      (∑ i, g (T v, d + (v : Fin n → ℂ) i)) = (n : ℂ) * γ ∧
      ‖T v - τ‖ ≤ r / 8 ∧
      ‖T v - τ‖ ≤ C * displacementSquare n (v : Fin n → ℂ) / (n : ℝ) ∧
      deriv (centeredPhaseAverage n g γ d (v : Fin n → ℂ)) (T v) ≠ 0 ∧
      ∀ u ∈ Metric.closedBall τ (r / 4),
        (∑ i, g (u, d + (v : Fin n → ℂ) i)) = (n : ℂ) * γ → u = T v := by
    simpa only [T, dite_eq_left hv] using (hex' v hv).choose_spec
  refine ⟨T, ?_, ?_, hT⟩
  · intro v hv
    let F := constrainedPhaseAverage n g γ d
    have hpair (i : Fin n) : (T v, d + (v : Fin n → ℂ) i) ∈ Metric.ball (0, 0) r := by
      have htt := (hT v hv).2.1
      have htn : ‖T v‖ ≤ ‖T v - τ‖ + ‖τ‖ := by
        simpa only [sub_add_cancel] using norm_add_le (T v - τ) τ
      have hvi : ‖(v : Fin n → ℂ) i‖ < σ :=
        (norm_le_pi_norm _ i).trans_lt
          (by simpa only [Metric.mem_ball, dist_zero_right, Submodule.norm_coe] using hv)
      have hsum := norm_add_le d ((v : Fin n → ℂ) i)
      rw [Metric.mem_ball, dist_eq_norm]
      simp only [Prod.mk_sub_mk, sub_zero, Prod.norm_def, max_lt_iff]
      constructor <;> linarith
    have hFa : AnalyticAt ℂ F (v, T v) :=
      constrainedPhaseAverage_analyticAt n g γ d (v, T v) (fun i => hga _ (hpair i))
    have hD : fderiv ℂ F (v, T v) (0, 1) ≠ 0 := by
      rw [← constrainedPhaseAverage_temp_deriv n g γ d v (T v) hFa.differentiableAt]
      exact (hT v hv).2.2.2.1
    have hTx : T v ∈ Metric.ball τ (r / 4) := by
      rw [Metric.mem_ball, dist_eq_norm]
      exact lt_of_le_of_lt (hT v hv).2.1 (by linarith)
    apply analyticAt_of_unique_implicit_zeros (F := F) (T := T)
      (V := Metric.ball 0 σ) (U := Metric.ball τ (r / 4))
      (Metric.isOpen_ball.mem_nhds hv) Metric.isOpen_ball hTx hFa hD
    · intro y hy
      exact (centeredPhaseAverage_eq_zero_iff hn g γ d (y : Fin n → ℂ) (T y)).mpr
        (hT y hy).1
    · intro y hy t ht hzero
      exact (hT y hy).2.2.2.2 t (Metric.ball_subset_closedBall ht)
        ((centeredPhaseAverage_eq_zero_iff hn g γ d (y : Fin n → ℂ) t).mp hzero)
  · have h := (hT 0 (Metric.mem_ball_self hσ)).2.2.1
    simp only [Submodule.coe_zero, Pi.zero_apply, displacementSquare, norm_zero, zero_pow
      (by norm_num : (2 : ℕ) ≠ 0), Finset.sum_const_zero, mul_zero, zero_div] at h
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h (norm_nonneg _)))

end
end IsingBulk.AnisoF002.NegativeHT
