import IsingBulk.AnisoF002.C03.IsotropicSeriesLocalNormality
import IsingBulk.AnisoF002.C03.IsotropicRadialExtensionBounds
import IsingBulk.AnisoF002.C03.IsotropicLogarithmicRemainder

/-!
# Every jet of a putative radial germ is the complete physical jet series

All particles are included. Local uniform summability is proved from the
actual complete tails and the finite original coefficients. A nonzero
scaled limit of that entire jet series therefore excludes an analytic
germ of the original complete susceptibility series.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set Filter Metric
open scoped Topology BigOperators

theorem isotropicRadialParameter_tendsto_zero_right {α : ℝ}
    (hα : 0 < α ∧ α < Real.pi) :
    Tendsto (isotropicRadialParameter α) (𝓝[>] (0 : ℝ))
      (𝓝 ((2 * Real.cos α : ℝ) : ℂ)) := by
  apply Metric.tendsto_nhds.mpr
  intro e he
  have hb : 0 < min 1 (e / 4) := lt_min zero_lt_one (by positivity)
  have hev : ∀ᶠ ε : ℝ in 𝓝 (0 : ℝ), ε < min 1 (e / 4) := Iio_mem_nhds hb
  filter_upwards [self_mem_nhdsWithin,
    hev.filter_mono nhdsWithin_le_nhds] with ε hε hsmall
  have hh := isotropicRadialParameter_estimates α ε hα hε
    (hsmall.le.trans (min_le_left _ _))
  exact hh.2.2.2.2.trans_lt (by have := hsmall.trans_le (min_le_right _ _); linarith)

theorem exists_actual_complete_series_extension_jets (α b : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ m : ℕ, ∀ σ : ℂ, σ = 1 ∨ σ = -1 →
      ∀ a : ℝ, a = 0 ∨ a = Real.pi → ∀ F : ℂ → ℂ,
      AnalyticAt ℂ F ((2 * Real.cos α : ℝ) : ℂ) →
      (∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), F (isotropicRadialParameter α ε) =
        isotropicFullParticleSeries m a σ (isotropicRadialParameter α ε)) →
      ∃ d : ℝ, 0 < d ∧ d ≤ δ ∧ ∀ j : ℕ, ∀ ε ∈ Ioo 0 d,
        Summable (fun n : ℕ => iteratedDeriv j (isotropicFullParticleCoefficient (m + 2 * n) a σ)
          (isotropicRadialParameter α ε)) ∧
        iteratedDeriv j F (isotropicRadialParameter α ε) =
          ∑' n : ℕ, iteratedDeriv j (isotropicFullParticleCoefficient (m + 2 * n) a σ)
            (isotropicRadialParameter α ε) := by
  obtain ⟨δ, hδ, hδ1, hmajor⟩ := exists_actual_complete_series_local_jet_majorants α b hα hb hpoint
  refine ⟨δ, hδ, hδ1, ?_⟩
  intro m σ hσ a ha F hF heq
  have hσnorm : ‖σ‖ ≤ 1 := by rcases hσ with rfl | rfl <;> simp
  have hFa : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), AnalyticAt ℂ F (isotropicRadialParameter α ε) :=
    (isotropicRadialParameter_tendsto_zero_right hα).eventually hF.eventually_analyticAt
  obtain ⟨e, he, hev⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (hFa.and heq)
  let d := min δ e
  have hd : 0 < d := lt_min hδ he
  have hdδ : d ≤ δ := min_le_left _ _
  have hde : d ≤ e := min_le_right _ _
  have hsub : Ioo 0 d ⊆ Ioo 0 δ := fun t ht => ⟨ht.1, ht.2.trans_le hdδ⟩
  have hF' (t : ℝ) (ht : t ∈ Ioo 0 d) : AnalyticAt ℂ F (isotropicRadialParameter α t) :=
    (hev ⟨ht.1, ht.2.trans_le hde⟩).1
  have heq' (t : ℝ) (ht : t ∈ Ioo 0 d) : F (isotropicRadialParameter α t) =
      ∑' n : ℕ, isotropicFullParticleCoefficient (m + 2 * n) a σ (isotropicRadialParameter α t) :=
    (hev ⟨ht.1, ht.2.trans_le hde⟩).2
  have hf (n : ℕ) (t : ℝ) (ht : t ∈ Ioo 0 d) :
      AnalyticAt ℂ (isotropicFullParticleCoefficient (m + 2 * n) a σ) (isotropicRadialParameter α t) :=
    isotropicFullParticleCoefficient_analyticAt _ a σ _ hσnorm
      ((isotropicRadialParameter_estimates α t hα ht.1 ((hsub ht).2.le.trans hδ1)).2.2.2.1)
  have hlocal (j : ℕ) (x : ℝ) (hx : x ∈ Ioo 0 d) :
      ∃ r : ℝ, 0 < r ∧ ball x r ⊆ Ioo 0 d ∧ ∃ M : ℕ → ℝ, Summable M ∧
        ∀ n : ℕ, ∀ t ∈ ball x r,
          ‖iteratedDeriv j (isotropicFullParticleCoefficient (m + 2 * n) a σ)
            (isotropicRadialParameter α t)‖ ≤ M n := by
    obtain ⟨r, hr, _, M, hM, hbM⟩ := hmajor m j σ hσ a ha x (hsub hx)
    obtain ⟨u, hu, hub⟩ := Metric.isOpen_iff.mp isOpen_Ioo x hx
    refine ⟨min r u, lt_min hr hu, ?_, M, hM, ?_⟩
    · exact fun t ht => hub (ball_subset_ball (min_le_right _ _) ht)
    · exact fun n t ht => hbM n t (ball_subset_ball (min_le_left _ _) ht)
  refine ⟨d, hd, hdδ, ?_⟩
  intro j ε hε
  obtain ⟨r, hr, _, M, hM, hbM⟩ := hlocal j ε hε
  refine ⟨hM.of_norm_bounded (fun n => hbM n ε (mem_ball_self hr)), ?_⟩
  exact (radial_tsum_identifies_extension_jets
    (fun n => isotropicFullParticleCoefficient (m + 2 * n) a σ) F
    (isotropicRadialParameter α) (isotropicRadialDerivative α) (Ioo 0 d) isOpen_Ioo j
    (by norm_num : (0 : ℝ) ≤ 2) hf hF'
    (fun t ht => isotropicRadialParameter_hasDerivAt α t ht.1)
    (fun t ht => isotropicRadialDerivative_ne_zero α t ht.1)
    (fun t ht => isotropicRadialDerivative_norm_le α t ht.1) heq'
    (fun k _ x hx => hlocal k x hx) j le_rfl ε hε).symm

theorem actual_complete_series_no_radial_germ_of_scaled_jet_limit (α b : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α)
    (m : ℕ) (σ : ℂ) (hσ : σ = 1 ∨ σ = -1) (a : ℝ) (ha : a = 0 ∨ a = Real.pi)
    (j l : ℕ) (hl : 0 < l) (A : ℂ) (hA : A ≠ 0)
    (hlim : Tendsto (fun s : ℝ => (s : ℂ) ^ l *
      ∑' n : ℕ, iteratedDeriv j (isotropicFullParticleCoefficient (m + 2 * n) a σ)
        (isotropicRadialParameter α (s ^ 2))) (𝓝[>] (0 : ℝ)) (𝓝 A)) :
    ¬ ∃ F : ℂ → ℂ, AnalyticAt ℂ F ((2 * Real.cos α : ℝ) : ℂ) ∧
      (∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), F (isotropicRadialParameter α ε) =
        isotropicFullParticleSeries m a σ (isotropicRadialParameter α ε)) := by
  rintro ⟨F, hF, heq⟩
  obtain ⟨δ, _, _, hjet⟩ := exists_actual_complete_series_extension_jets α b hα hb hpoint
  obtain ⟨d, hd, _, hj⟩ := hjet m σ hσ a ha F hF heq
  obtain ⟨e, B, he, hB, hbF⟩ := analytic_upper_extension_radial_jet_bound (f := F)
    hα zero_lt_one hF (fun _ _ _ => rfl) j
  have hbound (ε : ℝ) (hε : ε ∈ Ioo 0 e) :
      ‖iteratedDeriv j F (isotropicRadialParameter α ε)‖ ≤ B * (1 + |Real.log ε|) :=
    (hbF ε hε).trans (by nlinarith [abs_nonneg (Real.log ε)])
  have hz := radial_logarithmic_remainder_scaled_zero he hl hbound
  have hsmall : ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ), s ^ 2 < d :=
    ((show ContinuousAt (fun s : ℝ => s ^ 2) 0 by fun_prop).eventually
      (Iio_mem_nhds (by simpa using hd))).filter_mono nhdsWithin_le_nhds
  have hz' : Tendsto (fun s : ℝ => (s : ℂ) ^ l *
      ∑' n : ℕ, iteratedDeriv j (isotropicFullParticleCoefficient (m + 2 * n) a σ)
        (isotropicRadialParameter α (s ^ 2))) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    apply hz.congr'
    filter_upwards [self_mem_nhdsWithin, hsmall] with s hs hsd
    rw [(hj j (s ^ 2) ⟨sq_pos_of_pos hs, hsd⟩).2]
  exact hA (tendsto_nhds_unique hlim hz')

end
end IsingBulk.AnisoF002.Isotropic
