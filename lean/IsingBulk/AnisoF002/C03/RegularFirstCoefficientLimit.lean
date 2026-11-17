import IsingBulk.AnisoF002.C03.RegularCollisionCoefficient

/-!
# First-singularity limits of complete fixed-particle coefficients

The entire coefficient is split into its actual collision ball and its
analytic exterior.  The scaled local integral limit, including its exact
normalization, survives after the exterior is added back.  Both printed
odd and even top derivative orders are represented.  Nonvanishing of the
remaining explicit rational period is a separate subsequent theorem.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators

def regularFirstAmplitude (b : ℝ) (a : ℂ → ℂ) (n j : ℕ) : ℂ :=
  regularCoefficientNormalization n *
    ∫ q : Fin n → ℝ, collisionLeadingJet b a j (flatConstrainedAngles q)

theorem analytic_scaled_jet_zero {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0)
    (j l : ℕ) (hl : 0 < l) :
    Tendsto (fun s : ℝ => (s : ℂ) ^ l *
      iteratedDeriv j f (((s ^ 2 : ℝ) : ℂ) * Complex.I)) (𝓝 (0 : ℝ)) (𝓝 0) := by
  have hj : AnalyticAt ℂ (iteratedDeriv j f) 0 := by
    simpa only [iteratedDeriv_eq_iterate] using hf.iterated_deriv j
  have hpath : Tendsto (fun s : ℝ => (((s ^ 2 : ℝ) : ℂ) * Complex.I)) (𝓝 (0 : ℝ)) (𝓝 (0 : ℂ)) := by
    convert (show ContinuousAt (fun s : ℝ => (((s ^ 2 : ℝ) : ℂ) * Complex.I)) 0 by fun_prop).tendsto using 1
    simp
  have hp : Tendsto (fun s : ℝ => (s : ℂ) ^ l) (𝓝 (0 : ℝ)) (𝓝 (0 : ℂ)) := by
    simpa only [Complex.ofReal_zero, zero_pow (ne_of_gt hl)] using
      (Complex.continuous_ofReal.continuousAt.tendsto (x := (0 : ℝ))).pow l
  simpa only [zero_mul, Function.comp_def] using hp.mul (hj.continuousAt.tendsto.comp hpath)

theorem collision_scaling_ratio_eq {n j l : ℕ} {s : ℝ} (hs : s ≠ 0)
    (hdegree : 2 * j + 2 = n + 2 * (n + 1).choose 2 + l) :
    (s : ℂ) ^ (2 * j + 2) / (s : ℂ) ^ (n + 2 * (n + 1).choose 2) = (s : ℂ) ^ l := by
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs
  rw [hdegree, pow_add, mul_div_cancel_left₀ _ (pow_ne_zero _ hsC)]

theorem constrained_collision_degree (n : ℕ) :
    n + 2 * (n + 1).choose 2 + 1 = (n + 1) ^ 2 := by
  have h := Nat.add_one_mul_choose_eq n 1
  simp only [Nat.choose_one_right] at h
  nlinarith

theorem odd_first_scaling_degree {n : ℕ} (hn : Odd (n + 1)) :
    2 * oddTopOrder (n + 1) + 2 = n + 2 * (n + 1).choose 2 + 2 := by
  have hodd : Odd ((n + 1) ^ 2) := hn.pow
  obtain ⟨k, hk⟩ := hodd
  have hd := constrained_collision_degree n
  unfold oddTopOrder
  omega

theorem even_first_scaling_degree {n : ℕ} (hn : Even (n + 1)) :
    2 * evenTopOrder (n + 1) + 2 = n + 2 * (n + 1).choose 2 + 1 := by
  have heven : Even ((n + 1) ^ 2) := hn.pow_of_ne_zero (by norm_num : (2 : ℕ) ≠ 0)
  obtain ⟨k, hk⟩ := heven
  have hd := constrained_collision_degree n
  unfold evenTopOrder
  omega

namespace RegularEdgeCompleteControl
variable {b : ℝ} {a : ℂ → ℂ} (d : RegularEdgeCompleteControl b a)

theorem particleCoefficient_collision_jet_decomposition (n j : ℕ) (delta : ℝ) {eps : ℝ}
    (he : 0 < eps) (he0 : eps ≤ d.eps0) :
    iteratedDeriv j (edgeParticleCoefficient (affineEdgeCenter b) a n) ((eps : ℂ) * Complex.I) =
      iteratedDeriv j (edgeLocalCollisionCoefficient (affineEdgeCenter b) a n delta)
          ((eps : ℂ) * Complex.I) +
        iteratedDeriv j (edgeOffCollisionCoefficient (affineEdgeCenter b) a n delta)
          ((eps : ℂ) * Complex.I) := by
  have hP := d.restricted_particle_iteratedDeriv n j univ he he0
  simp only [Measure.restrict_univ] at hP
  have hL := d.restricted_particle_iteratedDeriv n j (Metric.ball 0 delta) he he0
  have hO := d.restricted_particle_iteratedDeriv n j (collisionExterior n delta) he he0
  change iteratedDeriv j (edgeParticleCoefficient (affineEdgeCenter b) a n) _ = _ at hP
  change iteratedDeriv j (edgeLocalCollisionCoefficient (affineEdgeCenter b) a n delta) _ = _ at hL
  change iteratedDeriv j (edgeOffCollisionCoefficient (affineEdgeCenter b) a n delta) _ = _ at hO
  rw [hP, hL, hO]
  have hf : Integrable (fun q : Fin n → ℝ =>
      iteratedDeriv j (fun u => edgeFullDensity (affineEdgeCenter b) a u (flatConstrainedAngles q))
        ((eps : ℂ) * Complex.I)) (regularAngularProbability n) :=
    integrable_of_carried_compact (regularAngularBox_compact n) (regularAngularProbability_ae_mem n)
      (((d.fullDensity_jet_continuous_inward (Nat.succ_pos n) he he0 j).comp
        (flatConstrainedAngles_continuous n)).continuousOn)
  have hm : (regularAngularProbability n).restrict (Metric.ball (0 : Fin n → ℝ) delta)ᶜ =
      (regularAngularProbability n).restrict (collisionExterior n delta) := by
    apply Measure.restrict_congr_set
    filter_upwards [regularAngularProbability_ae_mem n] with q hq
    simp [collisionExterior, hq]
  have hs := integral_add_compl (μ := regularAngularProbability n)
    (s := Metric.ball (0 : Fin n → ℝ) delta) Metric.isOpen_ball.measurableSet hf
  rw [hm] at hs
  rw [← mul_add, hs]

include d in
theorem localCoefficient_scaled_limit {n j l : ℕ} (hl : 0 < l)
    (hdegree : 2 * j + 2 = n + 2 * (n + 1).choose 2 + l)
    (hb : |b| < 1) (ha : 0 < (a 0).im)
    (hres : upperEdgeRoot (b : ℂ) ^ (n + 1) = 1) {delta : ℝ}
    (hd : 0 < delta) (hdpi : delta ≤ Real.pi / ((n : ℝ) + 1)) :
    Tendsto (fun s : ℝ => (s : ℂ) ^ l *
      iteratedDeriv j (edgeLocalCollisionCoefficient (affineEdgeCenter b) a n delta)
        (((s ^ 2 : ℝ) : ℂ) * Complex.I)) (𝓝[>] (0 : ℝ))
      (𝓝 (regularFirstAmplitude b a n j)) := by
  have hbudget : n + 2 * (n + 1).choose 2 < 2 * (j + 1) := by omega
  have hint := d.collisionScaledLocal_integral_limit j hb ha hres hd hdpi hbudget
  have hlim := hint.const_mul (regularCoefficientNormalization n)
  have hdp : delta ≤ Real.pi := hdpi.trans
    (div_le_self Real.pi_pos.le (by have hn := Nat.cast_nonneg (α := ℝ) n; linarith))
  have hsq : ContinuousAt (fun s : ℝ => s ^ 2) 0 := by fun_prop
  have hsmall : ∀ᶠ s : ℝ in 𝓝 (0 : ℝ), s ^ 2 < d.eps0 :=
    hsq.eventually (gt_mem_nhds (by simpa using d.eps0_pos))
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin, hsmall.filter_mono nhdsWithin_le_nhds] with s hs he
  rw [d.localCoefficient_scaled_integral n j hdp hs he.le,
    collision_scaling_ratio_eq (ne_of_gt hs) hdegree]

include d in
/-- Limit of the complete physical angular coefficient, including the
analytic exterior of its single collision neighborhood. -/
theorem particleCoefficient_scaled_limit {n j l : ℕ} (hl : 0 < l)
    (hdegree : 2 * j + 2 = n + 2 * (n + 1).choose 2 + l)
    (hb : |b| < 1) (ha : 0 < (a 0).im)
    (hres : upperEdgeRoot (b : ℂ) ^ (n + 1) = 1) :
    Tendsto (fun s : ℝ => (s : ℂ) ^ l *
      iteratedDeriv j (edgeParticleCoefficient (affineEdgeCenter b) a n)
        (((s ^ 2 : ℝ) : ℂ) * Complex.I)) (𝓝[>] (0 : ℝ))
      (𝓝 (regularFirstAmplitude b a n j)) := by
  let delta : ℝ := Real.pi / ((n : ℝ) + 1)
  have hd : 0 < delta := div_pos Real.pi_pos (by positivity)
  have hlocal := d.localCoefficient_scaled_limit hl hdegree hb ha hres hd (le_refl delta)
  have hoff0 := analytic_scaled_jet_zero (d.offCollisionCoefficient_analytic (n := n) hb ha hd) j l hl
  have hoff := hoff0.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have hsum := hlocal.add hoff
  simp only [add_zero] at hsum
  have hsq : ContinuousAt (fun s : ℝ => s ^ 2) 0 := by fun_prop
  have hsmall : ∀ᶠ s : ℝ in 𝓝 (0 : ℝ), s ^ 2 < d.eps0 :=
    hsq.eventually (gt_mem_nhds (by simpa using d.eps0_pos))
  apply hsum.congr'
  filter_upwards [self_mem_nhdsWithin, hsmall.filter_mono nhdsWithin_le_nhds] with s hs he
  rw [d.particleCoefficient_collision_jet_decomposition n j delta (sq_pos_of_pos hs) he.le,
    mul_add]

include d in
theorem odd_complete_coefficient_first_limit {n : ℕ} (hn : Odd (n + 1))
    (hb : |b| < 1) (ha : 0 < (a 0).im) (hres : upperEdgeRoot (b : ℂ) ^ (n + 1) = 1) :
    Tendsto (fun s : ℝ => (s : ℂ) ^ 2 *
      iteratedDeriv (oddTopOrder (n + 1)) (edgeParticleCoefficient (affineEdgeCenter b) a n)
        (((s ^ 2 : ℝ) : ℂ) * Complex.I)) (𝓝[>] (0 : ℝ))
      (𝓝 (regularFirstAmplitude b a n (oddTopOrder (n + 1)))) :=
  d.particleCoefficient_scaled_limit (by norm_num) (odd_first_scaling_degree hn) hb ha hres

include d in
theorem even_complete_coefficient_first_limit {n : ℕ} (hn : Even (n + 1))
    (hb : |b| < 1) (ha : 0 < (a 0).im) (hres : upperEdgeRoot (b : ℂ) ^ (n + 1) = 1) :
    Tendsto (fun s : ℝ => (s : ℂ) *
      iteratedDeriv (evenTopOrder (n + 1)) (edgeParticleCoefficient (affineEdgeCenter b) a n)
        (((s ^ 2 : ℝ) : ℂ) * Complex.I)) (𝓝[>] (0 : ℝ))
      (𝓝 (regularFirstAmplitude b a n (evenTopOrder (n + 1)))) := by
  simpa only [pow_one] using
    d.particleCoefficient_scaled_limit (by norm_num : 0 < 1) (even_first_scaling_degree hn) hb ha hres

end RegularEdgeCompleteControl
end
end IsingBulk.AnisoF002.RegularTail.C03
