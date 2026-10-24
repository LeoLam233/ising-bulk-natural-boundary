import IsingBulk.Anisotropic.FormFactors.SchurContourBound
import IsingBulk.Anisotropic.FormFactors.HadamardSummability
import IsingBulk.Anisotropic.FormFactors.KernelBound
import IsingBulk.Anisotropic.FormFactors.FiniteHolomorphy
import Mathlib.Analysis.Complex.LocallyUniformLimit

namespace IsingBulk.Anisotropic.FormFactors
noncomputable section
open Set Filter
open scoped Topology

theorem fullCoefficient_hadamard_bound (N : ℕ) (hN : 0 < N)
    {lam r M : ℝ} {z : ℂ} (ha : ContourAnnulus lam z r) (hM : 0 ≤ M)
    (hD : ∀ x y : ℂ, ‖x‖=r → ‖y‖=r → ‖(sliceDispersion lam z x y)⁻¹‖ ≤ M) :
    ‖unscaledFullCoefficient N lam z‖ ≤
      ((2/(1-r))^2*contourKernelBound r)*hadamardEnvelope (contourPairBound r*M) N := by
  have hh := unscaledFullCoefficientAtRadius_norm_le N hN ha.1 ha.2.1 hM hD
    (fun x y hx hy => circle_pairProduct_bound N hN ha.1 ha.2.1 x y hx hy)
  have he : unscaledFullCoefficient N lam z = unscaledFullCoefficientAtRadius N r lam z :=
    unscaledFullCoefficient_radius_independent N hN (contourRadius_spec ⟨r,ha⟩) ha
  rw [he]
  convert hh using 1
  unfold hadamardEnvelope
  rw [mul_pow]
  ring

/-- A genuine local all-particle normal envelope, derived from the spectral
pole exclusion and proved special-Schur/Hadamard inequalities. -/
theorem local_fullCoefficient_envelope {lam : ℝ} {z : ℂ} (hz : z ∉ spectralSet lam) :
    ∃ D C : ℝ, 0 < D ∧ 0 < C ∧ ∀ᶠ w in 𝓝 z, ∀ N : ℕ, 0 < N →
      ‖unscaledFullCoefficient N lam w‖ ≤ D*hadamardEnvelope C N := by
  obtain ⟨r,ha⟩ := contourAnnulus_exists hz
  obtain ⟨M,hM,hlocal⟩ := local_inverse_dispersion_bound ha
  refine ⟨(2/(1-r))^2*contourKernelBound r,contourPairBound r*M,?_,?_,?_⟩
  · have hc := contourKernelBound_ge_one ha.1.le ha.2.1
    have hd : 0 < 1-r := by linarith [ha.2.1]
    positivity
  · have hc := contourKernelBound_ge_one ha.1.le ha.2.1
    unfold contourPairBound
    exact mul_pos (div_pos (mul_pos (by norm_num) (lt_of_lt_of_le zero_lt_one hc)) (sq_pos_of_pos ha.1)) hM
  · filter_upwards [hlocal,contourAnnulus_eventually ha] with w hw hwa
    intro N hN
    exact fullCoefficient_hadamard_bound N hN hwa hM.le hw

theorem spectralProduct_analyticAt_ff (lam : ℝ) (z : ℂ) :
    AnalyticAt ℂ (spectralProduct lam) z := by
  exact (Complex.analyticAt_sinh).mul
    (Complex.analyticAt_sinh.comp ((analyticAt_const (v := (lam:ℂ))).mul analyticAt_id))

theorem weighted_envelope {D C P : ℝ} (_hD : 0 ≤ D) (_hC : 0 ≤ C) (hP : 1 ≤ P)
    {a b : ℂ} {k N : ℕ} (hk : k ≤ N) (ha : ‖a‖ ≤ P)
    (hb : ‖b‖ ≤ D*hadamardEnvelope C N) :
    ‖a^k*b‖ ≤ D*hadamardEnvelope (C*P) N := by
  have hpow : ‖a^k‖ ≤ P^N := by
    rw [norm_pow]
    exact (pow_le_pow_left₀ (norm_nonneg _) ha k).trans (pow_le_pow_right₀ hP hk)
  have hh := mul_le_mul hpow hb (norm_nonneg _) (by positivity : 0 ≤ P^N)
  rw [norm_mul]
  convert hh using 1
  unfold hadamardEnvelope
  rw [mul_pow]
  ring

/-- Holomorphy of any selected parity series with the physical integer
powers. The only indexing premise is summability of the explicit numerical
envelope, proved separately for each actual parity. -/
theorem selected_particleSeries_analyticOnNhd (lam : ℝ) (N k : ℕ → ℕ)
    (hN : ∀ n, 0 < N n) (hk : ∀ n, k n ≤ N n)
    (hs : ∀ C : ℝ, 0 ≤ C → Summable (fun n => hadamardEnvelope C (N n))) :
    AnalyticOnNhd ℂ (fun w => ∑' n, (spectralProduct lam w)^(k n)*unscaledFullCoefficient (N n) lam w)
      (spectralSet lam)ᶜ := by
  intro z hz
  obtain ⟨D,C,hD,hC,he⟩ := local_fullCoefficient_envelope hz
  let P : ℝ := ‖spectralProduct lam z‖+2
  have hP : 1 ≤ P := by dsimp [P]; linarith [norm_nonneg (spectralProduct lam z)]
  have hprod : ∀ᶠ w in 𝓝 z, ‖spectralProduct lam w‖ ≤ P := by
    apply ((spectralProduct_analyticAt_ff lam z).continuousAt.norm.eventually_lt continuousAt_const _).mono
    · intro w hw
      exact hw.le
    · dsimp [P]
      linarith
  have hevent : ∀ᶠ w in 𝓝 z, w ∈ (spectralSet lam)ᶜ ∧
      ∀ n, ‖(spectralProduct lam w)^(k n)*unscaledFullCoefficient (N n) lam w‖ ≤
        D*hadamardEnvelope (C*P) (N n) := by
    filter_upwards [he,hprod,(spectralSet_isClosed lam).isOpen_compl.mem_nhds hz] with w hw hp hwc
    exact ⟨hwc,fun n => weighted_envelope hD.le hC.le hP (hk n) hp (hw (N n) (hN n))⟩
  obtain ⟨U,hUsub,hU,hzU⟩ := mem_nhds_iff.mp hevent
  apply (Complex.differentiableOn_tsum_of_summable_norm ((hs (C*P) (by positivity)).mul_left D)
    (fun n w hw => (((spectralProduct_analyticAt_ff lam w).pow (k n)).mul
      (unscaledFullCoefficient_analyticOnNhd (N n) (hN n) lam w (hUsub hw).1)).differentiableAt.differentiableWithinAt)
    hU (fun n w hw => (hUsub hw).2 n)).analyticOnNhd hU z hzU

theorem high_particleSeries_analyticOnNhd (lam : ℝ) :
    AnalyticOnNhd ℂ (fun w => ∑' n, (spectralProduct lam w)^n*unscaledFullCoefficient (2*n+1) lam w)
      (spectralSet lam)ᶜ :=
  selected_particleSeries_analyticOnNhd lam (fun n => 2*n+1) id
    (fun _ => by omega) (fun _ => by dsimp; omega) (fun _ hC => hadamardEnvelope_odd_summable hC)

theorem low_particleSeries_analyticOnNhd (lam : ℝ) :
    AnalyticOnNhd ℂ (fun w => ∑' n, (spectralProduct lam w)^(n+1)*unscaledFullCoefficient (2*n+2) lam w)
      (spectralSet lam)ᶜ := by
  apply selected_particleSeries_analyticOnNhd lam (fun n => 2*n+2) (fun n => n+1)
    (fun _ => by omega) (fun _ => by omega)
  intro C hC
  have hh := (hadamardEnvelope_even_summable hC).comp_injective Nat.succ_injective
  change Summable (fun n => hadamardEnvelope C (2*(n+1))) at hh
  simpa only [mul_add,mul_one] using hh
end
end IsingBulk.Anisotropic.FormFactors
