import IsingBulk.AnisoF002.C03.NegativeMomentumGap
import IsingBulk.AnisoF002.C03.RegularEdgeSiteKernel

/-!
# All-angle attenuation and the odd constrained phase gap

The cosine bound is periodic and holds on the entire real angular cycle.
Combining it with the exact odd momentum product protects the true site
denominator even at the boundary, uniformly over every winding sector.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set Filter IsingBulk.AnisoF002.RegularTail IsingBulk.AnisoF002.RegularTail.C03
open scoped Topology BigOperators

theorem exists_negative_cosine_attenuation {B : ℂ → ℂ} {φ : ℝ}
    (d : RegularEdgePhaseControl (negativeGlobalCenter B φ) (negativeGlobalCoefficient B))
    (hB : AnalyticAt ℂ B 0) (hφ : 0 < φ) (hπ : φ < Real.pi) (hBi : (B 0).im < 0) :
    ∃ eps0 kappa : ℝ, 0 < eps0 ∧ 0 < kappa ∧
      ∀ eps : ℝ, 0 ≤ eps → eps ≤ eps0 →
        (-(eps : ℂ) ∈ Metric.closedBall (0 : ℂ) (d.radius / 4) ∧
          ∀ q : ℝ, kappa * (eps + 1 - Real.cos q) ≤
            (negativeGlobalPhase B φ (-(eps : ℂ), (q : ℂ))).re) := by
  let a0 : ℝ := -(B 0).im
  have ha0 : 0 < a0 := neg_pos.mpr hBi
  have hcoeff : ∀ᶠ t : ℂ in 𝓝 0, a0 / 2 < -(B t).im :=
    ((Complex.continuous_im.continuousAt.comp hB.continuousAt).neg).eventually
      (Ioi_mem_nhds (half_lt_self ha0))
  obtain ⟨r, hr, hcoeffr⟩ := Metric.eventually_nhds_iff.mp hcoeff
  let eps0 : ℝ := min (r / 2) (d.radius / 4)
  let kappa : ℝ := (a0 / 2) / Real.exp d.phaseBound
  have heps0 : 0 < eps0 := lt_min (half_pos hr) (div_pos d.radius_pos (by norm_num))
  have hkappa : 0 < kappa := div_pos (half_pos ha0) (Real.exp_pos _)
  refine ⟨eps0, kappa, heps0, hkappa, ?_⟩
  intro eps he he0
  have hnorm : ‖-(eps : ℂ)‖ = eps := by
    rw [norm_neg, Complex.norm_real, Real.norm_of_nonneg he]
  have hte : -(eps : ℂ) ∈ Metric.closedBall (0 : ℂ) (d.radius / 4) := by
    rw [Metric.mem_closedBall, dist_zero_right, hnorm]
    exact he0.trans (min_le_right _ _)
  have htr : dist (-(eps : ℂ)) 0 < r := by
    rw [dist_zero_right, hnorm]
    exact (he0.trans (min_le_left _ _)).trans_lt (half_lt_self hr)
  have hamin : a0 / 2 ≤ -(B (-(eps : ℂ))).im := (hcoeffr htr).le
  have haeps : (B (-(eps : ℂ))).im < 0 := by linarith
  refine ⟨hte, ?_⟩
  intro q
  have hbound := d.phase_bound (-(eps : ℂ))
    (Metric.closedBall_subset_closedBall (by linarith [d.radius_pos]) hte) q
  rw [← negativeGlobalPhase_real] at hbound
  have hp := upper_phase_real_lower_of_region
    (negative_global_dispersion_region hφ hπ he haeps) hbound
  have hx : 0 ≤ eps + 1 - Real.cos q := by linarith [Real.cos_le_one q]
  calc
    kappa * (eps + 1 - Real.cos q) = (a0 / 2 * (eps + 1 - Real.cos q)) /
        Real.exp d.phaseBound := by dsimp [kappa]; ring
    _ ≤ (-(B (-(eps : ℂ))).im * (eps + 1 - Real.cos q)) / Real.exp d.phaseBound :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hamin hx) (Real.exp_pos _).le
    _ ≤ _ := by simpa only [negative_global_dispersion_im, negativeGlobalPhase] using hp

theorem negative_constrained_totalPhase_lower {B : ℂ → ℂ} {φ eps kappa : ℝ}
    {n : ℕ} (hn : Odd n) (hk : 0 ≤ kappa) (q : Fin n → ℝ)
    (hq : ∑ i, q i = 0)
    (hphase : ∀ x : ℝ, kappa * (eps + 1 - Real.cos x) ≤
      (negativeGlobalPhase B φ (-(eps : ℂ), (x : ℂ))).re) :
    kappa * ((n : ℝ) * eps + 2 / (n : ℝ)) ≤
      (edgeTotalPhase (negativeGlobalCenter B φ) (negativeGlobalCoefficient B)
        (-(eps : ℂ)) (fun i => q i - Real.pi)).re := by
  have hgap := odd_zero_sum_negative_momentum_gap hn q hq
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
    hphase (q i - Real.pi))
  simp only [negativeGlobalPhase_real, Real.cos_sub_pi, sub_neg_eq_add,
    ← Finset.mul_sum] at hsum
  have hid : (∑ i, (eps + 1 + Real.cos (q i))) =
      (n : ℝ) * eps + ∑ i, (1 + Real.cos (q i)) := by
    simp_rw [show ∀ i : Fin n, eps + 1 + Real.cos (q i) = eps + (1 + Real.cos (q i)) by intro i; ring]
    simp [Finset.sum_add_distrib]
  rw [hid] at hsum
  have hbound := mul_le_mul_of_nonneg_left
    (add_le_add (le_refl ((n : ℝ) * eps)) hgap) hk
  exact hbound.trans (by simpa only [edgeTotalPhase, Complex.re_sum] using hsum)

end
end IsingBulk.AnisoF002.NegativeHT
