import IsingBulk.AnisoF002.C03.NegativeScalarLogAssembly

/-!
# The complete numerator logarithm at the common zero-angle center

This construction has no zero-sum displacement hypothesis.  The evenness
of the actual scalar phase eliminates every angular linear term at the
origin.  Every b-power, one-body factor and pair factor is retained in
the exact filled numerator before estimating its logarithm.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open IsingBulk.AnisoF002.Isotropic Set Filter
open scoped Topology BigOperators

def originNumeratorLog {b : ℂ → ℂ} {γ : ℂ} (L : CompleteDensityScalarLogs b γ)
    (n : ℕ) (g : ℂ × ℂ → ℂ) (t : ℂ) (v : Fin n → ℂ) : ℂ :=
  completeNumeratorLog n (L.Lb t) (fun i => L.Lh (g (t, v i)))
    (fun ij => L.Ls ((v ij.1 - v ij.2) / 2) -
      L.Lh ((g (t, v ij.1) + g (t, v ij.2)) / 2))

theorem originNumeratorLog_identity {b : ℂ → ℂ} {γ : ℂ}
    (L : CompleteDensityScalarLogs b γ) {n : ℕ} {g : ℂ × ℂ → ℂ} {t : ℂ} {v : Fin n → ℂ}
    (hcenter : g (0, 0) = γ) (ht : t ∈ Metric.ball 0 L.r)
    (hphase : ∀ i, g (t, v i) ∈ Metric.ball γ L.r)
    (hsinc : ∀ ij ∈ indexPairs n, (v ij.1 - v ij.2) / 2 ∈ Metric.ball 0 L.r) :
    filledNegativeNumerator n b g 0 t v =
      filledNegativeNumerator n b g 0 0 0 * Complex.exp (originNumeratorLog L n g t v) := by
  have hγ := (L.h_exp γ (Metric.mem_ball_self L.r_pos)).1
  have hb0 := (L.b_exp 0 (Metric.mem_ball_self L.r_pos)).1
  apply filledNegativeNumerator_eq_center_exp (fun i => L.Lh (g (t, v i)))
    (fun ij => L.Ls ((v ij.1 - v ij.2) / 2))
    (fun ij => L.Lh ((g (t, v ij.1) + g (t, v ij.2)) / 2)) hcenter
  · have he := (L.b_exp t ht).2
    exact (eq_div_iff hb0).mp he |>.symm.trans (mul_comm _ _)
  · intro i
    simp only [zero_add]
    have he := (L.h_exp _ (hphase i)).2
    exact (eq_div_iff hγ).mp he |>.symm.trans (mul_comm _ _)
  · intro ij hij
    exact (L.s_exp _ (hsinc ij hij)).2.symm
  · intro ij _
    simp only [zero_add]
    have he := (L.h_exp _ (average_mem_complex_ball (hphase ij.1) (hphase ij.2))).2
    exact (eq_div_iff hγ).mp he |>.symm.trans (mul_comm _ _)

theorem originNumeratorLog_cost {b : ℂ → ℂ} {γ : ℂ}
    (L : CompleteDensityScalarLogs b γ) {n : ℕ} {g : ℂ × ℂ → ℂ} {t : ℂ} {v : Fin n → ℂ}
    (ht : t ∈ Metric.ball 0 L.r)
    (hphase : ∀ i, g (t, v i) ∈ Metric.ball γ L.r)
    (hsinc : ∀ ij ∈ indexPairs n, (v ij.1 - v ij.2) / 2 ∈ Metric.ball 0 L.r) :
    ‖originNumeratorLog L n g t v‖ ≤
      (n : ℝ) ^ 2 * L.K * ‖t‖ + L.K * (∑ i, ‖g (t, v i) - γ‖) +
        4 * L.K * (n : ℝ) * (displacementSquare n v + ∑ i, ‖g (t, v i) - γ‖) := by
  have hp (ij : Fin n × Fin n) (hij : ij ∈ indexPairs n) :
      ‖L.Ls ((v ij.1 - v ij.2) / 2) - L.Lh ((g (t, v ij.1) + g (t, v ij.2)) / 2)‖ ≤
        L.K * ((‖v ij.1‖ ^ 2 + ‖g (t, v ij.1) - γ‖) +
          (‖v ij.2‖ ^ 2 + ‖g (t, v ij.2) - γ‖)) := by
    have hs := (L.s_bound _ (hsinc ij hij)).trans
      (mul_le_mul_of_nonneg_left (norm_half_difference_sq_le _ _) L.K_pos.le)
    have hh := (L.h_bound _ (average_mem_complex_ball (hphase ij.1) (hphase ij.2))).trans
      (mul_le_mul_of_nonneg_left (norm_average_sub_le _ _ γ) L.K_pos.le)
    have htri := norm_sub_le (L.Ls ((v ij.1 - v ij.2) / 2))
      (L.Lh ((g (t, v ij.1) + g (t, v ij.2)) / 2))
    have hn := mul_nonneg L.K_pos.le
      (add_nonneg (norm_nonneg (g (t, v ij.1) - γ)) (norm_nonneg (g (t, v ij.2) - γ)))
    nlinarith
  have hb : ‖L.Lb t‖ ≤ L.K * ‖t‖ := by
    simpa only [L.b_center, sub_zero] using L.b_lip t ht 0 (Metric.mem_ball_self L.r_pos)
  exact completeNumeratorLog_norm_le L.K_pos.le (fun i => norm_nonneg (g (t, v i) - γ))
    hb (fun i => L.h_bound _ (hphase i)) hp

theorem exists_uniform_even_origin_numerator_bound {b : ℂ → ℂ} {g : ℂ × ℂ → ℂ} {γ : ℂ}
    (hb : AnalyticAt ℂ b 0) (hb0 : b 0 ≠ 0)
    (hg : AnalyticAt ℂ g (0, 0)) (hg0 : g (0, 0) = γ)
    (hc : phaseTemperatureDerivative g (0, 0) ≠ 0)
    (heven : ∀ t d : ℂ, g (t, -d) = g (t, d)) (hγ : Complex.sinh γ ≠ 0) :
    ∃ L : CompleteDensityScalarLogs b γ, ∃ σ K : ℝ, 0 < σ ∧ 0 < K ∧
      ∀ n : ℕ, 0 < n → ∀ v : Fin n → ℂ, displacementSquare n v < σ ^ 2 →
        ∀ t : ℂ, ‖t‖ ≤ displacementSquare n v / (n : ℝ) →
          filledNegativeNumerator n b g 0 0 0 ≠ 0 ∧
          filledNegativeNumerator n b g 0 t v = filledNegativeNumerator n b g 0 0 0 *
            Complex.exp (originNumeratorLog L n g t v) ∧
          ‖originNumeratorLog L n g t v‖ ≤ K * (n : ℝ) * displacementSquare n v ∧
          ‖filledNegativeNumerator n b g 0 t v‖ ≤ ‖filledNegativeNumerator n b g 0 0 0‖ *
            Real.exp (K * (n : ℝ) * displacementSquare n v) := by
  obtain ⟨L⟩ := exists_complete_density_scalar_logs hb hb0 hγ
  obtain ⟨rv, A, hrv, _, hA, _, hvar⟩ := exists_uniform_even_phase_variation hg hc heven
  have hgt : Tendsto g (𝓝 (0, 0)) (𝓝 γ) := by simpa only [hg0] using hg.continuousAt.tendsto
  obtain ⟨rg, hrg, hgn⟩ := Metric.eventually_nhds_iff.mp
    (hgt.eventually (Metric.ball_mem_nhds γ L.r_pos))
  let R := min rv (min rg L.r)
  let σ := min (R / 2) 1
  let K := L.K * (5 + 10 * A) + 1
  have hR : 0 < R := lt_min hrv (lt_min hrg L.r_pos)
  have hσ : 0 < σ := lt_min (half_pos hR) zero_lt_one
  have hσ1 : σ ≤ 1 := min_le_right _ _
  have hσR : σ < R := (min_le_left _ _).trans_lt (half_lt_self hR)
  have hRrv : R ≤ rv := min_le_left _ _
  have hRrg : R ≤ rg := (min_le_right _ _).trans (min_le_left _ _)
  have hRr : R ≤ L.r := (min_le_right _ _).trans (min_le_right _ _)
  have hLK : 0 < L.K := L.K_pos
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨L, σ, K, hσ, hK, ?_⟩
  intro n hn v hQ t ht
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hQ0 := displacementSquare_nonneg n v
  have hQdiv : displacementSquare n v / (n : ℝ) ≤ displacementSquare n v := div_le_self hQ0 hn1
  have hσsq : σ ^ 2 ≤ σ := by nlinarith
  have htn : ‖t‖ < σ := ht.trans_lt ((hQdiv.trans_lt hQ).trans_le hσsq)
  have hvi (i : Fin n) : ‖v i‖ < σ := by
    have hi : ‖v i‖ ^ 2 ≤ displacementSquare n v :=
      Finset.single_le_sum (fun j _ => sq_nonneg ‖v j‖) (Finset.mem_univ i)
    nlinarith [norm_nonneg (v i)]
  have hpoint (i : Fin n) : (t, v i) ∈ Metric.ball (0, 0) R := by
    simpa only [Metric.mem_ball, dist_eq_norm, Prod.mk_sub_mk, sub_zero, Prod.norm_def,
      max_lt_iff] using And.intro (htn.trans hσR) ((hvi i).trans hσR)
  have hphase (i : Fin n) : g (t, v i) ∈ Metric.ball γ L.r :=
    hgn (Metric.mem_ball.mp (Metric.ball_subset_ball hRrg (hpoint i)))
  have htb : t ∈ Metric.ball 0 L.r := by
    simpa only [Metric.mem_ball, dist_zero_right] using (htn.trans hσR).trans_le hRr
  have hsinc (ij : Fin n × Fin n) (_ : ij ∈ indexPairs n) :
      (v ij.1 - v ij.2) / 2 ∈ Metric.ball (0 : ℂ) L.r := by
    rw [Metric.mem_ball, dist_zero_right, norm_div, show ‖(2 : ℂ)‖ = 2 by norm_num]
    have hh := norm_sub_le (v ij.1) (v ij.2)
    have hi := hvi ij.1
    have hj := hvi ij.2
    have hs : σ < L.r := hσR.trans_le hRr
    linarith
  have heq := originNumeratorLog_identity L hg0 htb hphase hsinc
  have hsum : (∑ i, ‖g (t, v i) - γ‖) ≤ 2 * A * displacementSquare n v := by
    have hh := sum_even_phase_variation hg0 hA.le (fun i =>
      hvar 0 0 t (v i) (Metric.mem_ball_self hrv)
        (by simpa only [zero_add] using Metric.ball_subset_ball hRrv (hpoint i))
        (by simpa only [sub_zero] using htn.le.trans hσ1))
    simp only [sub_zero, norm_zero, zero_mul, add_zero, zero_add] at hh
    have ht' : (n : ℝ) * ‖t‖ ≤ displacementSquare n v := by
      simpa only [mul_comm] using (le_div_iff₀ hnR).mp ht
    have hm := mul_le_mul_of_nonneg_left (show (n : ℝ) * ‖t‖ + displacementSquare n v ≤
      2 * displacementSquare n v by linarith) hA.le
    exact hh.trans (by nlinarith)
  have hlog : ‖originNumeratorLog L n g t v‖ ≤ K * (n : ℝ) * displacementSquare n v := by
    have hcost := originNumeratorLog_cost L htb hphase hsinc
    have ht' : (n : ℝ) * ‖t‖ ≤ displacementSquare n v := by
      simpa only [mul_comm] using (le_div_iff₀ hnR).mp ht
    have hpower : (n : ℝ) ^ 2 * L.K * ‖t‖ ≤ L.K * (n : ℝ) * displacementSquare n v := by
      have hh := mul_le_mul_of_nonneg_left ht' (show 0 ≤ L.K * (n : ℝ) by positivity)
      nlinarith
    have hsumN : (∑ i, ‖g (t, v i) - γ‖) ≤ 2 * A * ((n : ℝ) * displacementSquare n v) := by
      apply hsum.trans
      nlinarith [mul_nonneg (show 0 ≤ 2 * A by positivity) hQ0]
    have hbody := mul_le_mul_of_nonneg_left hsumN L.K_pos.le
    have hpair := mul_le_mul_of_nonneg_left hsum (show 0 ≤ 4 * L.K * (n : ℝ) by positivity)
    have hnon : 0 ≤ (n : ℝ) * displacementSquare n v := mul_nonneg hnR.le hQ0
    dsimp [K]
    nlinarith
  refine ⟨filledNegativeNumerator_center_ne_zero n b g 0 0 γ hg0 hb0 hγ, heq, hlog, ?_⟩
  rw [heq, norm_mul, Complex.norm_exp]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans hlog)

end
end IsingBulk.AnisoF002.NegativeHT
