import IsingBulk.AnisoF002.C03.RegularRetained

/-!
# Every fixed numerator derivative retains the actual sine collision block

The exact C02 analytic quotient is differentiated on a common parameter
disk.  Its complete complementary matching estimate includes every cross
pair and particle label.  Multiplication by the fixed angular sine block
then gives the derivative of the original full numerator, even on the
collision set where pointwise division is unavailable.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open IsingBulk.Anisotropic IsingBulk.AnisoF002.Geometry IsingBulk.AnisoF002.Isotropic
open scoped BigOperators Topology

theorem fullRootNumeratorF002_iteratedDeriv_retained {N : ℕ}
    (m r : ℕ) (lam : ℝ) (b : ℂ → ℂ) (x : Fin N → ℝ) (z : ℂ) :
    iteratedDeriv r (fun w => fullRootNumeratorF002 lam w (b w) x) z =
      embeddedSineBlock m x * iteratedDeriv r
        (fun w => retainedNumeratorQuotientF002 m lam w (b w) x) z := by
  have he : (fun w => fullRootNumeratorF002 lam w (b w) x) =
      fun w => embeddedSineBlock m x * retainedNumeratorQuotientF002 m lam w (b w) x := by
    funext w
    exact fullRootNumeratorF002_retained_factorization m lam w (b w) x
  rw [he, iteratedDeriv_const_mul_field]

theorem embeddedSineBlock_norm_eq {m N : ℕ} (hm : m ≤ N) (x : Fin N → ℝ) :
    ‖embeddedSineBlock m x‖ = retainedSineBlock (fun i : Fin m => x (i.castLE hm)) := by
  rw [embeddedSineBlock_eq_retainedSineBlock hm, Complex.norm_real, Real.norm_of_nonneg]
  exact Finset.prod_nonneg fun _ _ => sq_nonneg _

theorem fullRootNumeratorF002_fixed_block_jet_norm_le {m N : ℕ} (hm : m ≤ N)
    {lam : ℝ} {z : ℂ} {R H : ℝ} (hR : 0 < R) (b : ℂ → ℂ) (x : Fin N → ℝ)
    (hb : AnalyticOnNhd ℂ b (Metric.closedBall z R))
    (hgeom : ∀ w ∈ Metric.closedBall z R, w ∉ spectralSetF002 lam ∧ spectralS w ≠ 0)
    (hquot : ∀ w ∈ Metric.sphere z R, ‖retainedNumeratorQuotientF002 m lam w (b w) x‖ ≤ H)
    (r : ℕ) :
    ‖iteratedDeriv r (fun w => fullRootNumeratorF002 lam w (b w) x) z‖ ≤
      retainedSineBlock (fun i : Fin m => x (i.castLE hm)) * (r.factorial * H / R ^ r) := by
  have hq : ‖iteratedDeriv r (fun w => retainedNumeratorQuotientF002 m lam w (b w) x) z‖ ≤
      r.factorial * H / R ^ r := by
    apply Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le r hR _ hquot
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball _ hR.ne']
    intro w hw
    exact (retainedNumeratorQuotientF002_analyticAt m b x (hb w hw)
      (hgeom w hw).1 (hgeom w hw).2).differentiableAt.differentiableWithinAt
  rw [fullRootNumeratorF002_iteratedDeriv_retained m, norm_mul]
  have h := mul_le_mul_of_nonneg_left hq (norm_nonneg (embeddedSineBlock m x))
  simpa only [embeddedSineBlock_norm_eq hm] using h

theorem fullRootNumeratorF002_even_fixed_block_jet {m : ℕ} {lam : ℝ} {z : ℂ}
    {R q C M D B : ℝ} (hR : 0 < R) (hq : 0 ≤ q) (hC : 0 ≤ C)
    (hM : 0 ≤ M) (hD : 0 ≤ D) (b : ℂ → ℂ)
    (hb : AnalyticOnNhd ℂ b (Metric.closedBall z R))
    (hgeom : ∀ w ∈ Metric.closedBall z R, w ∉ spectralSetF002 lam ∧ spectralS w ≠ 0)
    (hroot : ∀ w ∈ Metric.closedBall z R, ∀ a c : ℝ,
      ‖schur (spectralSmallRootF002 lam w a) (spectralSmallRootF002 lam w c)‖ ≤ q)
    (hpair : ∀ w ∈ Metric.closedBall z R, ∀ a c : ℝ,
      ‖spectralCanceledPairF002 lam w a c‖ ≤ C)
    (hbody : ∀ w ∈ Metric.closedBall z R, ∀ a : ℝ, ‖spectralOneBodyF002 lam w a‖ ≤ M)
    (hcoeff : ∀ w ∈ Metric.closedBall z R, ∀ a c : ℝ,
      ‖spectralSinePairCoefficientF002 lam w a c‖ ≤ D)
    (hbnd : ∀ w ∈ Metric.closedBall z R, ‖b w‖ ≤ B)
    (r n : ℕ) (x : Fin (m + 2 * n) → ℝ) :
    ‖iteratedDeriv r (fun w => fullRootNumeratorF002 lam w (b w) x) z‖ ≤
      retainedSineBlock (fun i : Fin m => x (i.castLE (Nat.le_add_right m _))) *
        (r.factorial * ((B * M) ^ (m + 2 * n) * (D ^ m.choose 2 * C ^ (m * (2 * n)) *
          ((matchingNumber n : ℝ) * C ^ n * q ^ (2 * n * (n - 1))))) / R ^ r) := by
  apply fullRootNumeratorF002_fixed_block_jet_norm_le (Nat.le_add_right m _) hR b x hb hgeom
  intro w hw
  have hw' := Metric.sphere_subset_closedBall hw
  apply (retainedNumeratorQuotientF002_even_norm_le (hgeom w hw').1 (hgeom w hw').2
    hq hC hM hD (hroot w hw') (hpair w hw') (hbody w hw') (hcoeff w hw') n (b w) x).trans
  apply mul_le_mul_of_nonneg_right
  · exact pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) hM)
      (mul_le_mul_of_nonneg_right (hbnd w hw') hM) _
  · positivity

theorem fullRootNumeratorF002_odd_fixed_block_jet {m : ℕ} {lam : ℝ} {z : ℂ}
    {R q C M D B : ℝ} (hR : 0 < R) (hq : 0 < q) (hC : 0 < C)
    (hM : 0 ≤ M) (hD : 0 ≤ D) (b : ℂ → ℂ)
    (hb : AnalyticOnNhd ℂ b (Metric.closedBall z R))
    (hgeom : ∀ w ∈ Metric.closedBall z R, w ∉ spectralSetF002 lam ∧ spectralS w ≠ 0)
    (hroot : ∀ w ∈ Metric.closedBall z R, ∀ a c : ℝ,
      ‖schur (spectralSmallRootF002 lam w a) (spectralSmallRootF002 lam w c)‖ ≤ q)
    (hpair : ∀ w ∈ Metric.closedBall z R, ∀ a c : ℝ,
      ‖spectralCanceledPairF002 lam w a c‖ ≤ C)
    (hbody : ∀ w ∈ Metric.closedBall z R, ∀ a : ℝ, ‖spectralOneBodyF002 lam w a‖ ≤ M)
    (hcoeff : ∀ w ∈ Metric.closedBall z R, ∀ a c : ℝ,
      ‖spectralSinePairCoefficientF002 lam w a c‖ ≤ D)
    (hbnd : ∀ w ∈ Metric.closedBall z R, ‖b w‖ ≤ B)
    (r n : ℕ) (x : Fin (m + (2 * n + 1)) → ℝ) :
    ‖iteratedDeriv r (fun w => fullRootNumeratorF002 lam w (b w) x) z‖ ≤
      retainedSineBlock (fun i : Fin m => x (i.castLE (Nat.le_add_right m _))) *
        (r.factorial * ((B * M) ^ (m + (2 * n + 1)) *
          (D ^ m.choose 2 * C ^ (m * (2 * n + 1)) *
            ((matchingNumber (n + 1) : ℝ) * C ^ n * q ^ (2 * n * n)))) / R ^ r) := by
  apply fullRootNumeratorF002_fixed_block_jet_norm_le (Nat.le_add_right m _) hR b x hb hgeom
  intro w hw
  have hw' := Metric.sphere_subset_closedBall hw
  apply (retainedNumeratorQuotientF002_odd_norm_le (hgeom w hw').1 (hgeom w hw').2
    hq hC hM hD (hroot w hw') (hpair w hw') (hbody w hw') (hcoeff w hw') n (b w) x).trans
  apply mul_le_mul_of_nonneg_right
  · exact pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) hM)
      (mul_le_mul_of_nonneg_right (hbnd w hw') hM) _
  · positivity

end
end IsingBulk.AnisoF002.RegularTail.C03
