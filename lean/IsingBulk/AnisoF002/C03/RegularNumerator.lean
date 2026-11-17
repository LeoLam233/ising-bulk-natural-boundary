import IsingBulk.AnisoF002.C03.RegularSpectralMatching
import Mathlib.Analysis.Complex.Liouville

/-!
# Complete spectral numerator and its parameter jets

The all-angle matched bound is attached to `fullRootNumeratorF002` itself,
including the literal `b^N` and every one-body factor.  Cauchy's estimate
is applied only to this analytic numerator on a common parameter disk.
The site-sum rational factor and its possible pole are not differentiated
by this argument.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open IsingBulk.Anisotropic IsingBulk.AnisoF002.Geometry IsingBulk.AnisoF002.Isotropic
open scoped BigOperators Topology

theorem fullRootNumeratorF002_norm_le {N : ℕ} (lam : ℝ) (z b : ℂ)
    (x : Fin N → ℝ) {M E : ℝ} (hM : 0 ≤ M)
    (hbody : ∀ a : ℝ, ‖spectralOneBodyF002 lam z a‖ ≤ M)
    (hp : ‖∏ ij ∈ indexPairs N, spectralCanceledPairF002 lam z (x ij.1) (x ij.2)‖ ≤ E) :
    ‖fullRootNumeratorF002 lam z b x‖ ≤ (‖b‖ * M) ^ N * E := by
  have hprod : ‖∏ i, spectralOneBodyF002 lam z (x i)‖ ≤ M ^ N := by
    simpa only [List.map_ofFn, List.prod_ofFn, List.length_ofFn, Function.comp_def, id_eq] using
      norm_list_prod_le_pow (List.ofFn (id : Fin N → _))
        (fun i => spectralOneBodyF002 lam z (x i)) hM (fun i _ => hbody (x i))
  unfold fullRootNumeratorF002
  rw [norm_mul, norm_mul, norm_pow, mul_pow]
  exact mul_le_mul (mul_le_mul_of_nonneg_left hprod (pow_nonneg (norm_nonneg b) N)) hp
    (norm_nonneg _) (mul_nonneg (pow_nonneg (norm_nonneg b) N) (pow_nonneg hM N))

theorem fullRootNumeratorF002_even_norm_le {lam : ℝ} {z : ℂ}
    (hz : z ∉ spectralSetF002 lam) (hS : spectralS z ≠ 0)
    {q C M : ℝ} (hq : 0 ≤ q) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hroot : ∀ a b : ℝ,
      ‖schur (spectralSmallRootF002 lam z a) (spectralSmallRootF002 lam z b)‖ ≤ q)
    (hpair : ∀ a b : ℝ, ‖spectralCanceledPairF002 lam z a b‖ ≤ C)
    (hbody : ∀ a : ℝ, ‖spectralOneBodyF002 lam z a‖ ≤ M)
    (n : ℕ) (b : ℂ) (x : Fin (2 * n) → ℝ) :
    ‖fullRootNumeratorF002 lam z b x‖ ≤
      (‖b‖ * M) ^ (2 * n) *
        ((matchingNumber n : ℝ) * C ^ n * q ^ (2 * n * (n - 1))) := by
  exact fullRootNumeratorF002_norm_le lam z b x hM hbody
    (spectral_pairs_even_norm_le hz hS hq hC hroot hpair n x)

theorem fullRootNumeratorF002_odd_norm_le {lam : ℝ} {z : ℂ}
    (hz : z ∉ spectralSetF002 lam) (hS : spectralS z ≠ 0)
    {q C M : ℝ} (hq : 0 < q) (hC : 0 < C) (hM : 0 ≤ M)
    (hroot : ∀ a b : ℝ,
      ‖schur (spectralSmallRootF002 lam z a) (spectralSmallRootF002 lam z b)‖ ≤ q)
    (hpair : ∀ a b : ℝ, ‖spectralCanceledPairF002 lam z a b‖ ≤ C)
    (hbody : ∀ a : ℝ, ‖spectralOneBodyF002 lam z a‖ ≤ M)
    (n : ℕ) (b : ℂ) (x : Fin (2 * n + 1) → ℝ) :
    ‖fullRootNumeratorF002 lam z b x‖ ≤
      (‖b‖ * M) ^ (2 * n + 1) *
        ((matchingNumber (n + 1) : ℝ) * C ^ n * q ^ (2 * n * n)) := by
  exact fullRootNumeratorF002_norm_le lam z b x hM hbody
    (spectral_pairs_odd_norm_le hz hS hq hC hroot hpair n x)

/-- The actual full numerator is bounded on the same closed disk for
every angular tuple and particle index.  Its jets at the center therefore
retain precisely the same particle suppression with the Cauchy factor. -/
theorem fullRootNumeratorF002_even_jet_norm_le {lam : ℝ} {z : ℂ}
    {R q C M B : ℝ} (hR : 0 < R) (hq : 0 ≤ q) (hC : 0 ≤ C)
    (hM : 0 ≤ M) (b : ℂ → ℂ)
    (hb : AnalyticOnNhd ℂ b (Metric.closedBall z R))
    (hgeom : ∀ w ∈ Metric.closedBall z R, w ∉ spectralSetF002 lam ∧ spectralS w ≠ 0)
    (hroot : ∀ w ∈ Metric.closedBall z R, ∀ a c : ℝ,
      ‖schur (spectralSmallRootF002 lam w a) (spectralSmallRootF002 lam w c)‖ ≤ q)
    (hpair : ∀ w ∈ Metric.closedBall z R, ∀ a c : ℝ,
      ‖spectralCanceledPairF002 lam w a c‖ ≤ C)
    (hbody : ∀ w ∈ Metric.closedBall z R, ∀ a : ℝ, ‖spectralOneBodyF002 lam w a‖ ≤ M)
    (hbnd : ∀ w ∈ Metric.closedBall z R, ‖b w‖ ≤ B)
    (r n : ℕ) (x : Fin (2 * n) → ℝ) :
    ‖iteratedDeriv r (fun w => fullRootNumeratorF002 lam w (b w) x) z‖ ≤
      r.factorial * ((B * M) ^ (2 * n) *
        ((matchingNumber n : ℝ) * C ^ n * q ^ (2 * n * (n - 1)))) / R ^ r := by
  apply Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le r hR
  · apply DifferentiableOn.diffContOnCl
    rw [closure_ball _ hR.ne']
    intro w hw
    exact (fullRootNumeratorF002_analyticAt b x (hb w hw)
      (hgeom w hw).1 (hgeom w hw).2).differentiableAt.differentiableWithinAt
  · intro w hw
    have hw' : w ∈ Metric.closedBall z R := Metric.sphere_subset_closedBall hw
    apply (fullRootNumeratorF002_even_norm_le (hgeom w hw').1 (hgeom w hw').2
      hq hC hM (hroot w hw') (hpair w hw') (hbody w hw') n (b w) x).trans
    apply mul_le_mul_of_nonneg_right
    · exact pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) hM)
        (mul_le_mul_of_nonneg_right (hbnd w hw') hM) _
    · positivity

theorem fullRootNumeratorF002_odd_jet_norm_le {lam : ℝ} {z : ℂ}
    {R q C M B : ℝ} (hR : 0 < R) (hq : 0 < q) (hC : 0 < C)
    (hM : 0 ≤ M) (b : ℂ → ℂ)
    (hb : AnalyticOnNhd ℂ b (Metric.closedBall z R))
    (hgeom : ∀ w ∈ Metric.closedBall z R, w ∉ spectralSetF002 lam ∧ spectralS w ≠ 0)
    (hroot : ∀ w ∈ Metric.closedBall z R, ∀ a c : ℝ,
      ‖schur (spectralSmallRootF002 lam w a) (spectralSmallRootF002 lam w c)‖ ≤ q)
    (hpair : ∀ w ∈ Metric.closedBall z R, ∀ a c : ℝ,
      ‖spectralCanceledPairF002 lam w a c‖ ≤ C)
    (hbody : ∀ w ∈ Metric.closedBall z R, ∀ a : ℝ, ‖spectralOneBodyF002 lam w a‖ ≤ M)
    (hbnd : ∀ w ∈ Metric.closedBall z R, ‖b w‖ ≤ B)
    (r n : ℕ) (x : Fin (2 * n + 1) → ℝ) :
    ‖iteratedDeriv r (fun w => fullRootNumeratorF002 lam w (b w) x) z‖ ≤
      r.factorial * ((B * M) ^ (2 * n + 1) *
        ((matchingNumber (n + 1) : ℝ) * C ^ n * q ^ (2 * n * n))) / R ^ r := by
  apply Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le r hR
  · apply DifferentiableOn.diffContOnCl
    rw [closure_ball _ hR.ne']
    intro w hw
    exact (fullRootNumeratorF002_analyticAt b x (hb w hw)
      (hgeom w hw).1 (hgeom w hw).2).differentiableAt.differentiableWithinAt
  · intro w hw
    have hw' : w ∈ Metric.closedBall z R := Metric.sphere_subset_closedBall hw
    apply (fullRootNumeratorF002_odd_norm_le (hgeom w hw').1 (hgeom w hw').2
      hq hC hM (hroot w hw') (hpair w hw') (hbody w hw') n (b w) x).trans
    apply mul_le_mul_of_nonneg_right
    · exact pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) hM)
        (mul_le_mul_of_nonneg_right (hbnd w hw') hM) _
    · positivity

end
end IsingBulk.AnisoF002.RegularTail.C03
