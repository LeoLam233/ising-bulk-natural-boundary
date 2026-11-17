import IsingBulk.AnisoF002.C03.PhysicalContourRadius
import IsingBulk.AnisoF002.C03.PhysicalContourBound
import IsingBulk.AnisoF002.C03.PhysicalHadamardSummability
import IsingBulk.AnisoF002.C03.PhysicalPrefactors
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Complete original physical series on their full domains

The normal envelope is derived from one actual annulus and one scalar
kernel bound before all particle numbers.  Both complete original parity
sums, their original integer powers of sinh(z)sinh(lambda z), and their
chosen physical prefactors are retained.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open Set Filter IsingBulk.Anisotropic IsingBulk.Anisotropic.FormFactors
  IsingBulk.AnisoF002.Geometry
open scoped Topology

theorem literal_coefficient_hadamard_bound {N : ℕ} (hN : 0 < N)
    {lam r M : ℝ} {z : ℂ} (hz : z ∉ spectralSetF002 lam)
    (ha : ContourAnnulus lam z r)
    (hD : ∀ x y : ℂ, ‖x‖ = r → ‖y‖ = r → ‖(sliceDispersion lam z x y)⁻¹‖ ≤ M) :
    ‖unscaledFullCoefficient N lam z‖ ≤
      ((2 / (1 - r)) ^ 2 * literalContourKernelBound r) *
        literalHadamardEnvelope (literalContourPairBound r * M) N := by
  have hh := literal_fixedCoefficient_bound hN ha.1 ha.2.1 hD
    (fun x y hx hy => literal_circle_pairProduct_bound N hN ha.1 ha.2.1 x y hx hy)
  rw [literal_chosenCoefficient_eq_fixed hN hz ha]
  convert hh using 1
  unfold literalHadamardEnvelope
  rw [mul_pow]
  ring

theorem literal_local_fullCoefficient_envelope {lam : ℝ} {z : ℂ}
    (hz : z ∉ spectralSetF002 lam) :
    ∃ D C : ℝ, 0 < D ∧ 0 < C ∧ ∀ᶠ w in 𝓝 z, ∀ N : ℕ, 0 < N →
      ‖unscaledFullCoefficient N lam w‖ ≤ D * literalHadamardEnvelope C N := by
  obtain ⟨r, ha⟩ := literal_contourAnnulus_exists hz
  obtain ⟨M, hM, hlocal⟩ := literal_local_inverse_dispersion_bound ha
  refine ⟨(2 / (1 - r)) ^ 2 * literalContourKernelBound r,
    literalContourPairBound r * M, ?_, ?_, ?_⟩
  · have hc := literalContourKernelBound_ge_one ha.1.le ha.2.1
    have hd : 0 < 1 - r := by linarith [ha.2.1]
    positivity
  · have hc := literalContourKernelBound_ge_one ha.1.le ha.2.1
    unfold literalContourPairBound
    exact mul_pos (div_pos (mul_pos (by norm_num) (zero_lt_one.trans_le hc)) (sq_pos_of_pos ha.1)) hM
  · filter_upwards [hlocal, literal_contourAnnulus_eventually ha,
      (isClosed_spectralSetF002 lam).isOpen_compl.mem_nhds hz] with w hw hwa hwc
    intro N hN
    exact literal_coefficient_hadamard_bound hN hwc hwa hw

theorem literal_weighted_envelope {D C P : ℝ} (hP : 1 ≤ P)
    {a b : ℂ} {k N : ℕ} (hk : k ≤ N) (ha : ‖a‖ ≤ P)
    (hb : ‖b‖ ≤ D * literalHadamardEnvelope C N) :
    ‖a ^ k * b‖ ≤ D * literalHadamardEnvelope (C * P) N := by
  have hp : ‖a ^ k‖ ≤ P ^ N := by
    rw [norm_pow]
    exact (pow_le_pow_left₀ (norm_nonneg _) ha k).trans (pow_le_pow_right₀ hP hk)
  have hh := mul_le_mul hp hb (norm_nonneg _) (by positivity : 0 ≤ P ^ N)
  rw [norm_mul]
  convert hh using 1
  unfold literalHadamardEnvelope
  rw [mul_pow]
  ring

theorem literal_selectedSeries_summable {lam : ℝ} {z : ℂ}
    (hz : z ∉ spectralSetF002 lam) (N k : ℕ → ℕ)
    (hN : ∀ n, 0 < N n) (hk : ∀ n, k n ≤ N n)
    (hs : ∀ C : ℝ, 0 ≤ C → Summable (fun n => literalHadamardEnvelope C (N n))) :
    Summable (fun n => spectralProduct lam z ^ (k n) * unscaledFullCoefficient (N n) lam z) := by
  obtain ⟨D, C, hD, hC, he⟩ := literal_local_fullCoefficient_envelope hz
  have hzbound := he.self_of_nhds
  let P : ℝ := ‖spectralProduct lam z‖ + 1
  have hP : 1 ≤ P := by dsimp [P]; linarith [norm_nonneg (spectralProduct lam z)]
  apply ((hs (C * P) (mul_nonneg hC.le (zero_le_one.trans hP))).mul_left D).of_norm_bounded
  intro n
  exact literal_weighted_envelope hP (hk n) (by dsimp [P]; linarith) (hzbound (N n) (hN n))

theorem literal_selectedSeries_analyticOnNhd (lam : ℝ) (N k : ℕ → ℕ)
    (hN : ∀ n, 0 < N n) (hk : ∀ n, k n ≤ N n)
    (hs : ∀ C : ℝ, 0 ≤ C → Summable (fun n => literalHadamardEnvelope C (N n))) :
    AnalyticOnNhd ℂ
      (fun w => ∑' n, spectralProduct lam w ^ (k n) * unscaledFullCoefficient (N n) lam w)
      (spectralSetF002 lam)ᶜ := by
  intro z hz
  obtain ⟨D, C, hD, hC, he⟩ := literal_local_fullCoefficient_envelope hz
  let P : ℝ := ‖spectralProduct lam z‖ + 2
  have hP : 1 ≤ P := by dsimp [P]; linarith [norm_nonneg (spectralProduct lam z)]
  have hprod : ∀ᶠ w in 𝓝 z, ‖spectralProduct lam w‖ ≤ P := by
    apply ((Physical.spectralProduct_analytic lam z).continuousAt.norm.eventually_lt continuousAt_const ?_).mono
    · intro w hw
      exact hw.le
    · dsimp [P]
      linarith
  have hevent : ∀ᶠ w in 𝓝 z, w ∈ (spectralSetF002 lam)ᶜ ∧
      ∀ n, ‖spectralProduct lam w ^ (k n) * unscaledFullCoefficient (N n) lam w‖ ≤
        D * literalHadamardEnvelope (C * P) (N n) := by
    filter_upwards [he, hprod, (isClosed_spectralSetF002 lam).isOpen_compl.mem_nhds hz] with w hw hp hwc
    exact ⟨hwc, fun n => literal_weighted_envelope hP (hk n) hp (hw (N n) (hN n))⟩
  obtain ⟨U, hUsub, hU, hzU⟩ := mem_nhds_iff.mp hevent
  apply (Complex.differentiableOn_tsum_of_summable_norm ((hs (C * P) (by positivity)).mul_left D)
    (fun n w hw => (((Physical.spectralProduct_analytic lam w).pow (k n)).mul
      (literal_coefficient_analyticOnNhd (N n) (hN n) lam w (hUsub hw).1)).differentiableAt.differentiableWithinAt)
    hU (fun n w hw => (hUsub hw).2 n)).analyticOnNhd hU z hzU

theorem literal_highSeries_analyticOnNhd (lam : ℝ) :
    AnalyticOnNhd ℂ (fun w => ∑' n, spectralProduct lam w ^ n * unscaledFullCoefficient (2 * n + 1) lam w)
      (spectralSetF002 lam)ᶜ :=
  literal_selectedSeries_analyticOnNhd lam (fun n => 2 * n + 1) id
    (fun _ => by omega) (fun _ => by dsimp; omega)
    (fun _ hC => literalHadamardEnvelope_odd_summable hC)

theorem literal_lowSeries_analyticOnNhd (lam : ℝ) :
    AnalyticOnNhd ℂ (fun w => ∑' n, spectralProduct lam w ^ (n + 1) * unscaledFullCoefficient (2 * n + 2) lam w)
      (spectralSetF002 lam)ᶜ := by
  apply literal_selectedSeries_analyticOnNhd lam (fun n => 2 * n + 2) (fun n => n + 1)
    (fun _ => by omega) (fun _ => by omega)
  intro C hC
  have hh := (literalHadamardEnvelope_even_summable hC).comp_injective Nat.succ_injective
  change Summable (fun n => literalHadamardEnvelope C (2 * (n + 1))) at hh
  simpa only [mul_add, mul_one] using hh

theorem literal_highNormalizedBulk_analyticOnNhd {lam : ℝ} (hlam : 0 < lam) :
    AnalyticOnNhd ℂ (highNormalizedBulk lam) (omegaH lam) := by
  intro z hz
  exact ((Physical.highPrefactor_spec hlam).1 z hz).mul
    (literal_highSeries_analyticOnNhd lam z (omegaHF002_subset_complement hlam hz))

theorem literal_lowNormalizedBulk_analyticOnNhd {lam : ℝ} (hlam : 0 < lam) :
    AnalyticOnNhd ℂ (lowNormalizedBulk lam) (omegaL lam) := by
  intro z hz
  exact ((Physical.lowPrefactor_spec hlam).1 z hz).mul
    (literal_lowSeries_analyticOnNhd lam z (omegaLF002_subset_complement hlam hz))

end
end IsingBulk.AnisoF002.RegularTail.C03
