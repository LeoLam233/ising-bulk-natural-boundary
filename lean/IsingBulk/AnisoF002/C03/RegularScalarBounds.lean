import IsingBulk.AnisoF002.RegularTail.FiniteNumerator
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Actual uniform scalar factors on compact spectral-complement charts

The bounds are derived from C02's canonical-root compact gap.  They keep
the anisotropy `T/S` explicit and bound the complete canceled pair by its
own constant.  This is not a claim that the complete pair contracts.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open IsingBulk.Anisotropic IsingBulk.AnisoF002.Geometry

theorem root_pair_gap {r s : ℂ} {rho : ℝ} (hrho : 0 ≤ rho)
    (hr : ‖r‖ ≤ rho) (hs : ‖s‖ ≤ rho) :
    1 - rho ^ 2 ≤ ‖1 - r * s‖ := by
  have hm : ‖r‖ * ‖s‖ ≤ rho ^ 2 := by
    simpa only [pow_two] using mul_le_mul hr hs (norm_nonneg s) hrho
  have hd := norm_sub_norm_le (1 : ℂ) (r * s)
  rw [norm_one, norm_mul] at hd
  linarith

theorem root_oneBody_norm_le {r : ℂ} {rho : ℝ} (hrho : 0 ≤ rho)
    (hrho1 : rho < 1) (hr : ‖r‖ ≤ rho) :
    ‖2 * r / (1 - r ^ 2)‖ ≤ 2 * rho / (1 - rho ^ 2) := by
  have hd : 0 < 1 - rho ^ 2 := by nlinarith
  have hb : 1 - rho ^ 2 ≤ ‖1 - r ^ 2‖ := by
    simpa only [pow_two] using root_pair_gap hrho hr hr
  rw [norm_div, norm_mul, show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num]
  exact div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hr (by norm_num)) hd hb

theorem canceledPair_norm_le {B r s y v : ℂ} {rho : ℝ}
    (hrho : 0 ≤ rho) (hrho1 : rho < 1) (hr : ‖r‖ ≤ rho) (hs : ‖s‖ ≤ rho)
    (hy : ‖y‖ = 1) (hv : ‖v‖ = 1) :
    ‖canceledPair B r s y v‖ ≤ 4 * ‖B‖ * rho ^ 2 / (1 - rho ^ 2) ^ 2 := by
  have hd : 0 < 1 - rho ^ 2 := by nlinarith
  have hgap := root_pair_gap hrho hr hs
  have hyv : ‖y - v‖ ≤ 2 := by
    calc
      ‖y - v‖ ≤ ‖y‖ + ‖v‖ := norm_sub_le y v
      _ = 2 := by rw [hy, hv]; norm_num
  have hn : ‖-B * (y - v) ^ 2 * r * s‖ ≤ 4 * ‖B‖ * rho ^ 2 := by
    simp only [norm_mul, norm_neg, norm_pow]
    calc
      ‖B‖ * ‖y - v‖ ^ 2 * ‖r‖ * ‖s‖ ≤ ‖B‖ * 2 ^ 2 * rho * rho := by gcongr
      _ = _ := by ring
  have hden : (1 - rho ^ 2) ^ 2 ≤ ‖y * v * (1 - r * s) ^ 2‖ := by
    rw [norm_mul, norm_mul, hy, hv, one_mul, one_mul, norm_pow]
    exact pow_le_pow_left₀ hd.le hgap 2
  unfold canceledPair
  rw [norm_div]
  exact div_le_div₀ (by positivity) hn (sq_pos_of_pos hd) hden

theorem spectralOneBodyF002_norm_le {lam : ℝ} {z : ℂ} {rho : ℝ}
    (hrho : 0 ≤ rho) (hrho1 : rho < 1)
    (hroot : ∀ a : ℝ, ‖spectralSmallRootF002 lam z a‖ ≤ rho) (a : ℝ) :
    ‖spectralOneBodyF002 lam z a‖ ≤ 2 * rho / (1 - rho ^ 2) :=
  root_oneBody_norm_le hrho hrho1 (hroot a)

theorem spectralCanceledPairF002_norm_le {lam : ℝ} {z : ℂ} {rho : ℝ}
    (hrho : 0 ≤ rho) (hrho1 : rho < 1)
    (hroot : ∀ a : ℝ, ‖spectralSmallRootF002 lam z a‖ ≤ rho) (a b : ℝ) :
    ‖spectralCanceledPairF002 lam z a b‖ ≤
      4 * ‖spectralT lam z / spectralS z‖ * rho ^ 2 / (1 - rho ^ 2) ^ 2 := by
  exact canceledPair_norm_le hrho hrho1 (hroot a) (hroot b)
    (Complex.norm_exp_ofReal_mul_I a) (Complex.norm_exp_ofReal_mul_I b)

/-- The complete one-body and canceled-pair bounds are constructed, uniformly
over all real angles and every point of the given compact chart. -/
theorem exists_compact_spectral_scalar_bounds {lam : ℝ} {K : Set ℂ}
    (hK : IsCompact K) (hgeom : K ⊆ (spectralSetF002 lam)ᶜ)
    (hS : ∀ z ∈ K, spectralS z ≠ 0) :
    ∃ M C : ℝ, 0 < M ∧ 0 < C ∧
      (∀ z ∈ K, ∀ a : ℝ, ‖spectralOneBodyF002 lam z a‖ ≤ M) ∧
      (∀ z ∈ K, ∀ a b : ℝ, ‖spectralCanceledPairF002 lam z a b‖ ≤ C) := by
  obtain ⟨rho, hrho, hrho1, hroot⟩ := spectralSmallRootF002_compact_gap hK hgeom
  have hT : Continuous (spectralT lam) := by
    change Continuous (fun z : ℂ => Complex.sinh ((lam : ℂ) * z))
    fun_prop
  have hSs : Continuous spectralS := by
    change Continuous Complex.sinh
    fun_prop
  have hc : ContinuousOn (fun z => spectralT lam z / spectralS z) K :=
    hT.continuousOn.div hSs.continuousOn hS
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hc
  let M : ℝ := 2 * rho / (1 - rho ^ 2) + 1
  let C : ℝ := 4 * max B 0 * rho ^ 2 / (1 - rho ^ 2) ^ 2 + 1
  have hd : 0 < 1 - rho ^ 2 := by nlinarith
  refine ⟨M, C, ?_, ?_, ?_, ?_⟩
  · dsimp [M]
    positivity
  · dsimp [C]
    positivity
  · intro z hz a
    exact (spectralOneBodyF002_norm_le hrho hrho1 (hroot z hz) a).trans
      (by dsimp [M]; linarith)
  · intro z hz a b
    apply (spectralCanceledPairF002_norm_le hrho hrho1 (hroot z hz) a b).trans
    have hBb : ‖spectralT lam z / spectralS z‖ ≤ max B 0 := (hB z hz).trans (le_max_left _ _)
    dsimp [C]
    have hh : 4 * ‖spectralT lam z / spectralS z‖ * rho ^ 2 / (1 - rho ^ 2) ^ 2 ≤
        4 * max B 0 * rho ^ 2 / (1 - rho ^ 2) ^ 2 := by gcongr
    linarith

end
end IsingBulk.AnisoF002.RegularTail.C03
