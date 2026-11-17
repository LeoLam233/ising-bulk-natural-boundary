import IsingBulk.AnisoF002.C03.NegativePoleAnalytic

/-!
# Uniform analytic moving poles of the actual negative-edge dispersion

This joins the constructed physical parameter and branch to the
dimension-uniform constrained implicit construction.  All pole angles
remain in the actual common dispersion neighborhood.  The complete
residue density, its logarithmic estimate, and the higher-order pole
error are separate subsequent assertions.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open IsingBulk.Anisotropic IsingBulk.AnisoF002.Geometry Set Filter
open scoped Topology BigOperators

theorem tendsto_complex_winding_centers :
    Tendsto (fun n : ℕ => ((windingTau n : ℂ), ((Real.pi / (n : ℝ) : ℝ) : ℂ)))
      atTop (𝓝 (0, 0)) := by
  have ht : Tendsto (fun n : ℕ => (windingTau n : ℂ)) atTop (𝓝 (0 : ℂ)) := by
    simpa only [Function.comp_def, Complex.ofReal_zero] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp tendsto_windingTau_zero
  have hd : Tendsto (fun n : ℕ => ((Real.pi / (n : ℝ) : ℝ) : ℂ))
      atTop (𝓝 (0 : ℂ)) := by
    simpa only [Function.comp_def, Complex.ofReal_zero] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp
        (tendsto_const_div_atTop_nhds_zero_nat Real.pi)
  exact ht.prodMk_nhds hd

theorem physical_negative_phase_temperature_derivative_ne_zero
    {B : ℂ → ℂ} {g : ℂ × ℂ → ℂ} {φ : ℝ}
    (hφ : Real.sin φ ≠ 0) (hB : AnalyticAt ℂ B 0) (hB0 : B 0 ≠ 0)
    (hg : AnalyticAt ℂ g (0, 0)) (hg0 : g (0, 0) = (φ : ℂ) * Complex.I)
    (he : ∀ᶠ a in 𝓝 (0, 0), Complex.cosh (g a) = localNegativeDispersion B φ a) :
    fderiv ℂ g (0, 0) (1, 0) ≠ 0 := by
  have hd := local_negative_phase_derivative_unique B φ 0 hφ
    (by simpa using hB) (by simpa using hg) (by simpa using hg0) (by simpa using he)
  have hv : fderiv ℂ g (0, 0) (1, 0) = ((Real.sin φ : ℂ) * Complex.I)⁻¹ * B 0 := by
    have hd' := hd.fderiv
    simpa using congrArg (fun L : (ℂ × ℂ) →L[ℂ] ℂ => L (1, 0)) hd'
  rw [hv]
  exact mul_ne_zero (inv_ne_zero (mul_ne_zero (by exact_mod_cast hφ) Complex.I_ne_zero)) hB0

theorem displacementSquare_div_le_of_component_le {n : ℕ} (hn : 0 < n)
    (v : Fin n → ℂ) {σ : ℝ} (hσ : 0 ≤ σ) (hv : ∀ i, ‖v i‖ ≤ σ) :
    displacementSquare n v / (n : ℝ) ≤ σ ^ 2 := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hQ : displacementSquare n v ≤ (n : ℝ) * σ ^ 2 := by
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      show ‖v i‖ ^ 2 ≤ σ ^ 2 by nlinarith [hv i, norm_nonneg (v i)])
    simpa only [displacementSquare, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] using hh
  exact (div_le_iff₀ hnR).mpr (by simpa only [mul_comm] using hQ)

theorem exists_actual_uniform_moving_poles {lam φ : ℝ} {z : ℂ}
    (hlam : 0 < lam) (hx : z.re ≠ 0) (hφ0 : 0 < φ) (hφpi : φ < Real.pi)
    (hinc : spectralA lam z = spectralS z * (Real.cos φ : ℂ) + spectralT lam z * (-1))
    (hside : (spectralT lam z / spectralS z).im < 0) :
    ∃ (Z B : ℂ → ℂ) (g : ℂ × ℂ → ℂ) (σ C : ℝ),
      AnalyticAt ℂ Z 0 ∧ Z 0 = z ∧ AnalyticAt ℂ B 0 ∧
      B 0 = spectralT lam z / spectralS z ∧ B 0 ≠ 0 ∧
      (∀ t, B t = spectralT lam (Z t) / spectralS (Z t)) ∧
      (∀ δ : ℂ, g (1 - Complex.cos δ, δ) = (φ : ℂ) * Complex.I) ∧
      (∀ t δ : ℂ, g (t, -δ) = g (t, δ)) ∧
      (∀ᶠ a : ℝ × ℝ in 𝓝 (0, 0), a.1 < 0 →
        0 < (g (realPairToComplex a)).re ∧
        Complex.exp (-g (realPairToComplex a)) =
          spectralSmallRootF002 lam (Z (a.1 : ℂ)) (Real.pi + a.2)) ∧
      0 < σ ∧ 0 < C ∧
      ∀ᶠ n : ℕ in atTop, ∃ T : zeroSumDisplacements n → ℂ,
        AnalyticOnNhd ℂ T (Metric.ball 0 σ) ∧ T 0 = (windingTau n : ℂ) ∧
        ∀ v ∈ Metric.ball 0 σ,
          (∑ i, g (T v, ((Real.pi / (n : ℝ) : ℝ) : ℂ) + (v : Fin n → ℂ) i)) =
            (n : ℂ) * ((φ : ℂ) * Complex.I) ∧
          ‖T v - (windingTau n : ℂ)‖ ≤
            C * displacementSquare n (v : Fin n → ℂ) / (n : ℝ) ∧
          deriv (centeredPhaseAverage n g ((φ : ℂ) * Complex.I)
            ((Real.pi / (n : ℝ) : ℝ) : ℂ) (v : Fin n → ℂ)) (T v) ≠ 0 ∧
          ∀ i : Fin n,
            AnalyticAt ℂ g (T v, ((Real.pi / (n : ℝ) : ℝ) : ℂ) + (v : Fin n → ℂ) i) ∧
            spectralS (Z (T v)) ≠ 0 ∧
            Complex.cosh (g (T v, ((Real.pi / (n : ℝ) : ℝ) : ℂ) + (v : Fin n → ℂ) i)) =
              (spectralA lam (Z (T v)) - spectralT lam (Z (T v)) *
                Complex.cos ((Real.pi : ℂ) + ((Real.pi / (n : ℝ) : ℝ) : ℂ) +
                  (v : Fin n → ℂ) i)) / spectralS (Z (T v)) := by
  obtain ⟨Z, B, g, hZa, hZ0, hBa, hB0, hBne, hBe, hgcent, hgeven,
    ⟨r₀, hr₀, hphysical⟩, hroot, _, _⟩ :=
    exists_uniform_negative_physical_phase hlam hx hφ0 hφpi hinc hside
  have hg : AnalyticAt ℂ g (0, 0) := (hphysical (0, 0) (Metric.mem_ball_self hr₀)).1
  have hg0 : g (0, 0) = (φ : ℂ) * Complex.I := by simpa using hgcent 0
  have hball : ∀ᶠ a : ℂ × ℂ in 𝓝 (0, 0), a ∈ Metric.ball (0, 0) r₀ :=
    Metric.ball_mem_nhds _ hr₀
  have he : ∀ᶠ a in 𝓝 (0, 0), Complex.cosh (g a) = localNegativeDispersion B φ a :=
    hball.mono (fun a ha => (hphysical a ha).2.2.1)
  have hc := physical_negative_phase_temperature_derivative_ne_zero
    (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hφ0 hφpi)) hBa hBne hg hg0 he
  obtain ⟨r, σ₀, C, hr, hσ₀, hC, hPoles⟩ := exists_uniform_analytic_zero_sum_poles hg hc
  let σ : ℝ := min σ₀ (min (r₀ / 4) (min 1 (r₀ / (8 * C))))
  have hσ : 0 < σ := lt_min hσ₀ (lt_min (by positivity) (lt_min zero_lt_one (by positivity)))
  have hσσ : σ ≤ σ₀ := min_le_left _ _
  have hσr : σ ≤ r₀ / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hσ1 : σ ≤ 1 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hσC : σ ≤ r₀ / (8 * C) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hCσ : C * σ ^ 2 ≤ r₀ / 8 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 8 * C)).mp hσC
    have hs : σ ^ 2 ≤ σ := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hs hC.le]
  refine ⟨Z, B, g, σ, C, hZa, hZ0, hBa, hB0, hBne, hBe,
    hgcent, hgeven, hroot, hσ, hC, ?_⟩
  have hcN : ∀ᶠ n : ℕ in atTop,
      ((windingTau n : ℂ), ((Real.pi / (n : ℝ) : ℝ) : ℂ)) ∈
        Metric.ball (0, 0) (min (r / 4) (r₀ / 4)) :=
    tendsto_complex_winding_centers.eventually
      (Metric.ball_mem_nhds _ (lt_min (by positivity) (by positivity)))
  filter_upwards [hcN, eventually_gt_atTop (0 : ℕ)] with n hnball hn
  have hcenternorm : max ‖(windingTau n : ℂ)‖ ‖((Real.pi / (n : ℝ) : ℝ) : ℂ)‖ <
      min (r / 4) (r₀ / 4) := by
    simpa only [Metric.mem_ball, dist_eq_norm, Prod.mk_sub_mk, sub_zero, Prod.norm_def] using hnball
  have hτr : ‖(windingTau n : ℂ)‖ < r / 4 :=
    (lt_of_le_of_lt (le_max_left _ _) hcenternorm).trans_le (min_le_left _ _)
  have hdr : ‖((Real.pi / (n : ℝ) : ℝ) : ℂ)‖ < r / 4 :=
    (lt_of_le_of_lt (le_max_right _ _) hcenternorm).trans_le (min_le_left _ _)
  have hτ₀ : ‖(windingTau n : ℂ)‖ < r₀ / 4 :=
    (lt_of_le_of_lt (le_max_left _ _) hcenternorm).trans_le (min_le_right _ _)
  have hd₀ : ‖((Real.pi / (n : ℝ) : ℝ) : ℂ)‖ < r₀ / 4 :=
    (lt_of_le_of_lt (le_max_right _ _) hcenternorm).trans_le (min_le_right _ _)
  have hcenter : g ((windingTau n : ℂ), ((Real.pi / (n : ℝ) : ℝ) : ℂ)) =
      (φ : ℂ) * Complex.I := by
    simpa only [windingTau, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_cos]
      using hgcent ((Real.pi / (n : ℝ) : ℝ) : ℂ)
  obtain ⟨T, hTa, hT0, hTv⟩ := hPoles n hn (windingTau n : ℂ)
    ((Real.pi / (n : ℝ) : ℝ) : ℂ) ((φ : ℂ) * Complex.I) hτr hdr hcenter
  refine ⟨T, hTa.mono (Metric.ball_subset_ball hσσ), hT0, ?_⟩
  intro v hv
  have hv₀ := Metric.ball_subset_ball hσσ hv
  obtain ⟨hlevel, _, hcoarse, hderiv, _⟩ := hTv v hv₀
  refine ⟨hlevel, hcoarse, hderiv, ?_⟩
  have hvi (i : Fin n) : ‖(v : Fin n → ℂ) i‖ < σ :=
    (norm_le_pi_norm _ i).trans_lt
      (by simpa only [Metric.mem_ball, dist_zero_right, Submodule.norm_coe] using hv)
  have hQ := displacementSquare_div_le_of_component_le hn (v : Fin n → ℂ) hσ.le
    (fun i => (hvi i).le)
  have hsmall : ‖T v - (windingTau n : ℂ)‖ ≤ r₀ / 8 := by
    calc
      ‖T v - (windingTau n : ℂ)‖ ≤ C * displacementSquare n (v : Fin n → ℂ) / (n : ℝ) := hcoarse
      _ = C * (displacementSquare n (v : Fin n → ℂ) / (n : ℝ)) := by ring
      _ ≤ C * σ ^ 2 := mul_le_mul_of_nonneg_left hQ hC.le
      _ ≤ r₀ / 8 := hCσ
  intro i
  have hpoint : (T v, ((Real.pi / (n : ℝ) : ℝ) : ℂ) + (v : Fin n → ℂ) i) ∈
      Metric.ball (0, 0) r₀ := by
    have ht : ‖T v‖ ≤ ‖T v - (windingTau n : ℂ)‖ + ‖(windingTau n : ℂ)‖ := by
      simpa only [sub_add_cancel] using norm_add_le (T v - (windingTau n : ℂ)) (windingTau n : ℂ)
    have hvn := hvi i
    have hsum := norm_add_le ((Real.pi / (n : ℝ) : ℝ) : ℂ) ((v : Fin n → ℂ) i)
    rw [Metric.mem_ball, dist_eq_norm]
    simp only [Prod.mk_sub_mk, sub_zero, Prod.norm_def, max_lt_iff]
    constructor <;> linarith
  obtain ⟨ha, hs, _, heq⟩ := hphysical _ hpoint
  exact ⟨ha, hs, by simpa only [add_assoc] using heq⟩

end
end IsingBulk.AnisoF002.NegativeHT
