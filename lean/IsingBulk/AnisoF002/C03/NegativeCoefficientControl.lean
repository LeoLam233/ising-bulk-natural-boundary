import IsingBulk.AnisoF002.C03.NegativeCosineAttenuation
import IsingBulk.AnisoF002.C03.RegularCoefficientNormal

/-!
# Constructed pole control for every complete odd coefficient

All constants are obtained from the actual analytic dispersion before N.
The coefficient disk has radius c/N² and remains valid at every inward
real center, including the boundary.  Every constrained angular tuple is
covered, with no omitted winding or partial-collision region.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set Filter IsingBulk.AnisoF002.RegularTail IsingBulk.AnisoF002.RegularTail.C03
open scoped Topology BigOperators

structure NegativeCoefficientControl (B : ℂ → ℂ) (φ : ℝ) where
  numerator : RegularEdgeControl (negativeGlobalCenter B φ) (negativeGlobalCoefficient B)
  phase : RegularEdgePhaseControl (negativeGlobalCenter B φ) (negativeGlobalCoefficient B)
  eps0 : ℝ
  attenuation : ℝ
  eps0_pos : 0 < eps0
  attenuation_pos : 0 < attenuation
  inward_numerator : ∀ eps : ℝ, 0 ≤ eps → eps ≤ eps0 →
    -(eps : ℂ) ∈ Metric.closedBall (0 : ℂ) (numerator.radius / 4)
  inward_phase : ∀ eps : ℝ, 0 ≤ eps → eps ≤ eps0 →
    -(eps : ℂ) ∈ Metric.closedBall (0 : ℂ) (phase.radius / 4)
  cosine_lower : ∀ eps : ℝ, 0 ≤ eps → eps ≤ eps0 → ∀ q : ℝ,
    attenuation * (eps + 1 - Real.cos q) ≤
      (negativeGlobalPhase B φ (-(eps : ℂ), (q : ℂ))).re

theorem exists_negative_coefficient_control {B : ℂ → ℂ} {φ : ℝ}
    (hB : AnalyticAt ℂ B 0) (hφ : 0 < φ) (hπ : φ < Real.pi) (hBi : (B 0).im < 0) :
    Nonempty (NegativeCoefficientControl B φ) := by
  obtain ⟨⟨dn⟩, ⟨dp⟩⟩ := exists_negative_global_controls hB hφ hπ hBi
  obtain ⟨e, k, he, hk, hbound⟩ := exists_negative_cosine_attenuation dp hB hφ hπ hBi
  refine ⟨{
    numerator := dn
    phase := dp
    eps0 := min e (dn.radius / 4)
    attenuation := k
    eps0_pos := lt_min he (div_pos dn.radius_pos (by norm_num))
    attenuation_pos := hk
    inward_numerator := ?_
    inward_phase := ?_
    cosine_lower := ?_ }⟩
  · intro eps heps he0
    rw [Metric.mem_closedBall, dist_zero_right, norm_neg, Complex.norm_real,
      Real.norm_of_nonneg heps]
    exact he0.trans (min_le_right _ _)
  · intro eps heps he0
    exact (hbound eps heps (he0.trans (min_le_left _ _))).1
  · intro eps heps he0
    exact (hbound eps heps (he0.trans (min_le_left _ _))).2

namespace NegativeCoefficientControl
variable {B : ℂ → ℂ} {φ : ℝ} (d : NegativeCoefficientControl B φ)

def phaseConstant : ℝ := min d.attenuation 1

theorem phaseConstant_pos : 0 < d.phaseConstant := lt_min d.attenuation_pos (by norm_num)

theorem phaseConstant_le_one : d.phaseConstant ≤ 1 := min_le_right _ _

def coefficientConstant : ℝ := min (d.numerator.radius / 4)
  (d.phaseConstant * d.phase.siteScale)

theorem coefficientConstant_pos : 0 < d.coefficientConstant :=
  lt_min (div_pos d.numerator.radius_pos (by norm_num))
    (mul_pos d.phaseConstant_pos d.phase.siteScale_pos)

def coefficientRadius (n : ℕ) : ℝ := d.coefficientConstant / (n : ℝ) ^ 2

theorem coefficientRadius_pos {n : ℕ} (hn : 0 < n) : 0 < d.coefficientRadius n :=
  div_pos d.coefficientConstant_pos (sq_pos_of_pos (Nat.cast_pos.mpr hn))

theorem coefficientRadius_le_quarter {n : ℕ} (hn : 0 < n) :
    d.coefficientRadius n ≤ d.numerator.radius / 4 := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  exact (div_le_self d.coefficientConstant_pos.le hn2).trans (min_le_left _ _)

theorem coefficientRadius_le_siteRadius {n : ℕ} (hn : 0 < n) :
    d.coefficientRadius n ≤ d.phase.siteRadius n (d.phaseConstant / (n : ℝ)) := by
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hn)
  have h := div_le_div_of_nonneg_right
    (show d.coefficientConstant ≤ d.phaseConstant * d.phase.siteScale from min_le_right _ _)
    (sq_nonneg (n : ℝ))
  change d.coefficientConstant / (n : ℝ) ^ 2 ≤ _
  calc
    _ ≤ (d.phaseConstant * d.phase.siteScale) / (n : ℝ) ^ 2 := h
    _ = d.phase.siteRadius n (d.phaseConstant / (n : ℝ)) := by
      unfold RegularEdgePhaseControl.siteRadius
      field_simp

theorem phase_eta_bounds {n : ℕ} (hn : 0 < n) :
    0 < d.phaseConstant / (n : ℝ) ∧ d.phaseConstant / (n : ℝ) ≤ 1 := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  exact ⟨div_pos d.phaseConstant_pos (Nat.cast_pos.mpr hn),
    (div_le_one (Nat.cast_pos.mpr hn)).mpr (d.phaseConstant_le_one.trans hn1)⟩

theorem constrained_phase_lower {n : ℕ} (hn : Odd n) {eps : ℝ}
    (he : 0 ≤ eps) (he0 : eps ≤ d.eps0) (q : Fin n → ℝ) (hq : ∑ i, q i = 0) :
    d.phaseConstant / (n : ℝ) ≤
      (edgeTotalPhase (negativeGlobalCenter B φ) (negativeGlobalCoefficient B)
        (-(eps : ℂ)) (fun i => q i - Real.pi)).re := by
  have h := negative_constrained_totalPhase_lower hn d.attenuation_pos.le q hq
    (d.cosine_lower eps he he0)
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn.pos
  have hk : d.phaseConstant ≤ d.attenuation := min_le_left _ _
  have hdiv := div_le_div_of_nonneg_right hk hn0.le
  have hprod := mul_nonneg d.attenuation_pos.le (mul_nonneg hn0.le he)
  have hpos := div_nonneg d.attenuation_pos.le hn0.le
  have hid : d.attenuation * ((n : ℝ) * eps + 2 / (n : ℝ)) =
      d.attenuation * ((n : ℝ) * eps) + 2 * (d.attenuation / (n : ℝ)) := by ring
  rw [hid] at h
  linarith

theorem coefficientDisk_numerator_subset {n : ℕ} (hn : 0 < n) {eps : ℝ}
    (he : 0 ≤ eps) (he0 : eps ≤ d.eps0) :
    Metric.closedBall (-(eps : ℂ)) (d.coefficientRadius n) ⊆
      Metric.closedBall (0 : ℂ) (d.numerator.radius / 2) := by
  apply Metric.closedBall_subset_closedBall'
  have ht := Metric.mem_closedBall.mp (d.inward_numerator eps he he0)
  have hr := d.coefficientRadius_le_quarter hn
  linarith

theorem coefficientDisk_phase_protected {n : ℕ} (hn : Odd n) {eps : ℝ}
    (he : 0 ≤ eps) (he0 : eps ≤ d.eps0) (q : Fin n → ℝ) (hq : ∑ i, q i = 0)
    {u : ℂ} (hu : u ∈ Metric.closedBall (-(eps : ℂ)) (d.coefficientRadius n)) :
    u ∈ Metric.closedBall (0 : ℂ) (d.phase.radius / 2) ∧
      (d.phaseConstant / (n : ℝ)) / 2 ≤
        (edgeTotalPhase (negativeGlobalCenter B φ) (negativeGlobalCoefficient B)
          u (fun i => q i - Real.pi)).re := by
  have heps := d.inward_phase eps he he0
  have heta := d.phase_eta_bounds hn.pos
  have hsite : u ∈ Metric.closedBall (-(eps : ℂ))
      (d.phase.siteRadius n (d.phaseConstant / (n : ℝ))) :=
    Metric.closedBall_subset_closedBall (d.coefficientRadius_le_siteRadius hn.pos) hu
  exact ⟨d.phase.siteDisk_subset_half hn.pos heta.2 heps hsite,
    d.phase.siteDisk_phase_protected (fun i => q i - Real.pi) hn.pos heta.1 heta.2 heps
      (d.constrained_phase_lower hn he he0 q hq) hsite⟩

end NegativeCoefficientControl
end
end IsingBulk.AnisoF002.NegativeHT
