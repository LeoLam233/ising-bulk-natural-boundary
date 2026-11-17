import IsingBulk.AnisoF002.C03.NegativeAngularJets

/-!
# Full zero-sum phase expansion with the even cubic improvement

All constants are obtained from the single analytic phase before the
particle number is selected.  The expansion keeps every angular variable;
the linear contribution cancels only by the actual zero-sum constraint.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set
open scoped Topology BigOperators

theorem angular_quadratic_remainder {g : ℂ × ℂ → ℂ} {r M : ℝ}
    (hM : 0 ≤ M) (ha : AnalyticOnNhd ℂ g (Metric.ball (0, 0) r))
    (hfour : ∀ p ∈ Metric.ball (0, 0) r, ‖angularJet 4 g p‖ ≤ M)
    (hthree : ∀ t d : ℂ, (t, d) ∈ Metric.ball (0, 0) r →
      ‖angularJet 3 g (t, d)‖ ≤ M * ‖d‖)
    {t d v : ℂ} (hp : (t, d) ∈ Metric.ball (0, 0) r)
    (hq : (t, d + v) ∈ Metric.ball (0, 0) r) :
    ‖g (t, d + v) - g (t, d) - angularJet 1 g (t, d) * v -
      (angularJet 2 g (t, d) / 2) * v ^ 2‖ ≤
        M * (‖d‖ * ‖v‖ ^ 3 + ‖v‖ ^ 4) := by
  have htd : ‖t‖ < r ∧ ‖d‖ < r := by
    simpa [Metric.mem_ball, dist_eq_norm, Prod.norm_def] using hp
  have hdv : ‖d + v‖ < r := (le_max_right ‖t‖ ‖d + v‖).trans_lt
    (by simpa [Metric.mem_ball, dist_eq_norm, Prod.norm_def] using hq)
  have hpair (δ : ℂ) (hδ : δ ∈ Metric.ball 0 r) :
      (t, δ) ∈ Metric.ball (0, 0) r := by
    simpa [Metric.mem_ball, dist_eq_norm, Prod.norm_def] using
      And.intro htd.1 (show ‖δ‖ < r by simpa [Metric.mem_ball, dist_eq_norm] using hδ)
  have hslice : AnalyticOnNhd ℂ (fun δ : ℂ => g (t, δ)) (Metric.ball 0 r) := by
    intro δ hδ
    exact (ha (t, δ) (hpair δ hδ)).comp_of_eq (analyticAt_const.prod analyticAt_id) rfl
  have hf (δ : ℂ) (hδ : δ ∈ Metric.ball 0 r) :
      ‖deriv (deriv (deriv (deriv (fun δ : ℂ => g (t, δ))))) δ‖ ≤ M := by
    simpa only [angularJet, iteratedDeriv_succ, iteratedDeriv_zero] using
      hfour (t, δ) (hpair δ hδ)
  have hh := scalar_third_taylor_remainder (convex_ball (0 : ℂ) r) hslice
    (show d ∈ Metric.ball 0 r by simpa [Metric.mem_ball, dist_eq_norm] using htd.2)
    hM hf (d + v) (by simpa [Metric.mem_ball, dist_eq_norm] using hdv)
  have hr : ‖g (t, d + v) - g (t, d) - angularJet 1 g (t, d) * v -
      (angularJet 2 g (t, d) / 2) * v ^ 2 -
      (angularJet 3 g (t, d) / 6) * v ^ 3‖ ≤ M * ‖v‖ ^ 4 := by
    simpa only [angularJet, iteratedDeriv_succ, iteratedDeriv_zero, add_sub_cancel_left] using hh
  have hc : ‖angularJet 3 g (t, d) / 6‖ ≤ M * ‖d‖ := by
    rw [norm_div, show ‖(6 : ℂ)‖ = (6 : ℝ) by norm_num]
    exact (div_le_self (norm_nonneg _) (by norm_num : (1 : ℝ) ≤ 6)).trans (hthree t d hp)
  calc
    _ = ‖(g (t, d + v) - g (t, d) - angularJet 1 g (t, d) * v -
        (angularJet 2 g (t, d) / 2) * v ^ 2 -
        (angularJet 3 g (t, d) / 6) * v ^ 3) +
        (angularJet 3 g (t, d) / 6) * v ^ 3‖ := by congr 1; ring
    _ ≤ ‖g (t, d + v) - g (t, d) - angularJet 1 g (t, d) * v -
        (angularJet 2 g (t, d) / 2) * v ^ 2 -
        (angularJet 3 g (t, d) / 6) * v ^ 3‖ +
        ‖(angularJet 3 g (t, d) / 6) * v ^ 3‖ := norm_add_le
        (g (t, d + v) - g (t, d) - angularJet 1 g (t, d) * v -
          (angularJet 2 g (t, d) / 2) * v ^ 2 -
          (angularJet 3 g (t, d) / 6) * v ^ 3)
        ((angularJet 3 g (t, d) / 6) * v ^ 3)
    _ ≤ M * ‖v‖ ^ 4 + (M * ‖d‖) * ‖v‖ ^ 3 :=
      add_le_add hr (by rw [norm_mul, norm_pow]; gcongr)
    _ = _ := by ring

theorem full_phase_angular_remainder {g : ℂ × ℂ → ℂ} {r M : ℝ}
    (hM : 0 ≤ M) (ha : AnalyticOnNhd ℂ g (Metric.ball (0, 0) r))
    (hfour : ∀ p ∈ Metric.ball (0, 0) r, ‖angularJet 4 g p‖ ≤ M)
    (hthree : ∀ t d : ℂ, (t, d) ∈ Metric.ball (0, 0) r →
      ‖angularJet 3 g (t, d)‖ ≤ M * ‖d‖)
    (n : ℕ) {t d : ℂ} {v : Fin n → ℂ} (hsum : (∑ i, v i) = 0)
    (hp : (t, d) ∈ Metric.ball (0, 0) r)
    (hv : ∀ i, (t, d + v i) ∈ Metric.ball (0, 0) r) :
    ‖(∑ i, g (t, d + v i)) - (n : ℂ) * g (t, d) -
      (angularJet 2 g (t, d) / 2) * (∑ i, v i ^ 2)‖ ≤
      M * (‖d‖ * (∑ i, ‖v i‖ ^ 3) + ∑ i, ‖v i‖ ^ 4) := by
  have he : (∑ i, g (t, d + v i)) - (n : ℂ) * g (t, d) -
      (angularJet 2 g (t, d) / 2) * (∑ i, v i ^ 2) =
      ∑ i, (g (t, d + v i) - g (t, d) - angularJet 1 g (t, d) * v i -
        (angularJet 2 g (t, d) / 2) * v i ^ 2) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, hsum, mul_zero, sub_zero]
  rw [he]
  calc
    _ ≤ ∑ i, ‖g (t, d + v i) - g (t, d) - angularJet 1 g (t, d) * v i -
        (angularJet 2 g (t, d) / 2) * v i ^ 2‖ := norm_sum_le _ _
    _ ≤ ∑ i, M * (‖d‖ * ‖v i‖ ^ 3 + ‖v i‖ ^ 4) :=
      Finset.sum_le_sum (fun i _ => angular_quadratic_remainder hM ha hfour hthree hp (hv i))
    _ = _ := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
      simp_rw [← Finset.mul_sum]

end
end IsingBulk.AnisoF002.NegativeHT
