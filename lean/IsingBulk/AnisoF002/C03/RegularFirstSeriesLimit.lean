import IsingBulk.AnisoF002.C03.RegularFirstCoefficientLimit
import IsingBulk.AnisoF002.C03.RegularTailSum
import IsingBulk.AnisoF002.C03.RegularResonance

/-!
# First-singularity limits of the complete parity particle series

The exact infinite series is split into every lower coefficient, its
first resonant coefficient, and every larger same-parity coefficient.
Normal convergence justifies all actual derivatives.  Analytic lower
coefficients and the bounded complete differentiated tail vanish under
the same singular scaling, leaving the genuine constrained period.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open Set Filter
open scoped Topology BigOperators

theorem bounded_scaled_zero {f : ℝ → ℂ} {M : ℝ} {l : ℕ} (hl : 0 < l)
    (hf : ∀ᶠ s in 𝓝[>] (0 : ℝ), ‖f s‖ ≤ M) :
    Tendsto (fun s : ℝ => (s : ℂ) ^ l * f s) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  apply squeeze_zero_norm' (a := fun s : ℝ => ‖(s : ℂ)‖ ^ l * M)
  · filter_upwards [hf] with s hs
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left hs (pow_nonneg (norm_nonneg _) _)
  · have hc : ContinuousAt (fun s : ℝ => ‖(s : ℂ)‖ ^ l * M) 0 := by fun_prop
    simpa only [Complex.ofReal_zero, norm_zero, zero_pow (ne_of_gt hl), zero_mul] using
      hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))

namespace RegularEdgeCompleteControl
variable {b : ℝ} {a : ℂ → ℂ} (d : RegularEdgeCompleteControl b a)

theorem particle_jets_summable (m j : ℕ) {eps : ℝ}
    (he : 0 < eps) (he0 : eps ≤ d.eps0) :
    Summable (fun r : ℕ => iteratedDeriv j
      (edgeParticleCoefficient (affineEdgeCenter b) a (m + 2 * r))
        ((eps : ℂ) * Complex.I)) := by
  obtain ⟨R, hR, M, hM, hf, hb⟩ := d.exists_particle_subseries_common_disk m he he0
  apply (hM.mul_left ((j.factorial : ℝ) / (R / 2) ^ j)).of_norm_bounded
  intro r
  convert common_disk_iteratedDeriv_bound hR (hf r) (hb r)
    (Metric.mem_closedBall_self (half_pos hR).le) j using 1
  ring

theorem particleTail_derivative_split (m k j : ℕ) {eps : ℝ}
    (he : 0 < eps) (he0 : eps ≤ d.eps0) :
    iteratedDeriv j (edgeParticleTail (affineEdgeCenter b) a m) ((eps : ℂ) * Complex.I) =
      (∑ r ∈ Finset.range k, iteratedDeriv j
        (edgeParticleCoefficient (affineEdgeCenter b) a (m + 2 * r))
          ((eps : ℂ) * Complex.I)) +
      iteratedDeriv j (edgeParticleCoefficient (affineEdgeCenter b) a (m + 2 * k))
        ((eps : ℂ) * Complex.I) +
      iteratedDeriv j (edgeParticleTail (affineEdgeCenter b) a (m + 2 * (k + 1)))
        ((eps : ℂ) * Complex.I) := by
  rw [d.particleTail_iteratedDeriv_inward m j he he0,
    d.particleTail_iteratedDeriv_inward (m + 2 * (k + 1)) j he he0]
  have h := (d.particle_jets_summable m j he he0).sum_add_tsum_nat_add (k + 1)
  rw [Finset.sum_range_succ] at h
  convert h.symm using 2
  apply tsum_congr
  intro r
  congr 2
  omega

include d in
theorem selected_tail_scaled_zero {N j l : ℕ} (hN : 1 ≤ N)
    (hj : 2 * j ≤ N ^ 2) (hl : 0 < l) :
    Tendsto (fun s : ℝ => (s : ℂ) ^ l *
      iteratedDeriv j (edgeParticleTail (affineEdgeCenter b) a (N + 1))
        (((s ^ 2 : ℝ) : ℂ) * Complex.I)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  obtain ⟨M, _, hM⟩ := d.selected_tail_derivative_uniform hN hj
  apply bounded_scaled_zero hl (M := M)
  have hsq : ContinuousAt (fun s : ℝ => s ^ 2) 0 := by fun_prop
  have hsmall : ∀ᶠ s : ℝ in 𝓝 (0 : ℝ), s ^ 2 < d.eps0 :=
    hsq.eventually (gt_mem_nhds (by simpa using d.eps0_pos))
  filter_upwards [self_mem_nhdsWithin, hsmall.filter_mono nhdsWithin_le_nhds] with s hs he
  exact hM (s ^ 2) (sq_pos_of_pos hs) he.le

include d in
/-- Complete particle-series limit, including all lower coefficients
and the full differentiated infinite tail of the same parity. -/
theorem particleSeries_first_limit {m k j l : ℕ} (hl : 0 < l)
    (hdegree : 2 * j + 2 = (m + 2 * k) + 2 * (m + 2 * k + 1).choose 2 + l)
    (hj : 2 * j ≤ (m + 2 * k + 1) ^ 2)
    (hb : |b| < 1) (ha : 0 < (a 0).im)
    (hres : upperEdgeRoot (b : ℂ) ^ (m + 2 * k + 1) = 1)
    (hlower : ∀ r < k, upperEdgeRoot (b : ℂ) ^ (m + 2 * r + 1) ≠ 1) :
    Tendsto (fun s : ℝ => (s : ℂ) ^ l *
      iteratedDeriv j (edgeParticleTail (affineEdgeCenter b) a m)
        (((s ^ 2 : ℝ) : ℂ) * Complex.I)) (𝓝[>] (0 : ℝ))
      (𝓝 (regularFirstAmplitude b a (m + 2 * k) j)) := by
  have hfirst := d.particleCoefficient_scaled_limit hl hdegree hb ha hres
  have hlowerlim : Tendsto (fun s : ℝ => ∑ r ∈ Finset.range k,
      (s : ℂ) ^ l * iteratedDeriv j
        (edgeParticleCoefficient (affineEdgeCenter b) a (m + 2 * r))
          (((s ^ 2 : ℝ) : ℂ) * Complex.I)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hterm (r : ℕ) (hr : r ∈ Finset.range k) :=
      analytic_scaled_jet_zero (d.nonresonant_particle_analytic hb ha
        (hlower r (Finset.mem_range.mp hr))) j l hl
    simpa only [Finset.sum_const_zero] using
      (tendsto_finsetSum (Finset.range k) fun r hr =>
        (hterm r hr).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ))))
  have htail := d.selected_tail_scaled_zero (by omega : 1 ≤ m + 2 * k + 1) hj hl
  have hsum := (hlowerlim.add hfirst).add htail
  simp only [zero_add, add_zero] at hsum
  have hsq : ContinuousAt (fun s : ℝ => s ^ 2) 0 := by fun_prop
  have hsmall : ∀ᶠ s : ℝ in 𝓝 (0 : ℝ), s ^ 2 < d.eps0 :=
    hsq.eventually (gt_mem_nhds (by simpa using d.eps0_pos))
  apply hsum.congr'
  filter_upwards [self_mem_nhdsWithin, hsmall.filter_mono nhdsWithin_le_nhds] with s hs he
  rw [d.particleTail_derivative_split m k j (sq_pos_of_pos hs) he.le,
    mul_add, mul_add, Finset.mul_sum]
  congr 2

end RegularEdgeCompleteControl
end
end IsingBulk.AnisoF002.RegularTail.C03
