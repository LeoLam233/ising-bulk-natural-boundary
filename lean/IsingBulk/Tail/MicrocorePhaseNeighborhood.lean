import IsingBulk.Tail.MicrocorePhaseMagnitude
import IsingBulk.Tail.MicrocoreWindow

/-! A prescribed regular-coordinate neighborhood is reached uniformly
throughout every intermediate-window microcore. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Branch Filter

theorem original_phase_small_radius (d : LocalBranchData) (R : ℝ) (hR : 0 < R) :
    ∃ r C : ℝ, 0 < r ∧ 0 < C ∧ ∀ ε b u : ℝ,
      0 < ε → ε ≤ b → b < r → |u| ≤ b →
      ‖originalPhase d ε u‖ ≤ C*Real.sqrt b ∧ ‖originalPhase d ε u‖ < R := by
  obtain ⟨cl,C,rP,_,hC,hrP,hP⟩ := original_phase_magnitude d
  let r := min (rP/2) (R^2/(16*C^2))
  have hr : 0 < r := by dsimp [r]; positivity
  refine ⟨r,2*C,hr,by positivity,?_⟩
  intro ε b u hε hεb hbr hu
  have hb : 0 < b := hε.trans_le hεb
  have hbrP : b < rP := hbr.trans_le ((min_le_left _ _).trans (half_le_self hrP.le))
  have hh := (hP ε u hε (hεb.trans_lt hbrP) (hu.trans_lt hbrP)).2
  have hs : Real.sqrt (|u|+ε) ≤ 2*Real.sqrt b := by
    have hs1 := Real.sq_sqrt (show 0 ≤ |u|+ε by positivity)
    have hs2 := Real.sq_sqrt hb.le
    nlinarith [Real.sqrt_nonneg (|u|+ε),Real.sqrt_nonneg b]
  have hbound : ‖originalPhase d ε u‖ ≤ 2*C*Real.sqrt b := hh.trans (by nlinarith)
  refine ⟨hbound,hbound.trans_lt ?_⟩
  have hsmall : b < R^2/(16*C^2) := hbr.trans_le (min_le_right _ _)
  have hmul := (lt_div_iff₀ (show 0 < 16*C^2 by positivity)).mp hsmall
  have hs2 := Real.sq_sqrt hb.le
  have hp : 0 ≤ C*Real.sqrt b := by positivity
  nlinarith

theorem microcoreRadius_mono_prefactor (A c d : ℝ) (hcd : c ≤ d) (N : ℕ) :
    microcoreRadius A c N ≤ microcoreRadius A d N := by
  unfold microcoreRadius
  gcongr

theorem original_microcore_uniform_phase_neighborhood (d : LocalBranchData)
    (R : ℝ) (hR : 0 < R) :
    ∃ c : ℝ, 0 < c ∧ ∀ A D : ℝ, 0 ≤ A → 0 ≤ D →
      ∀ᶠ H : ℝ in atTop, ∀ N : ℕ, 1 ≤ N → (N:ℝ) ≤ D*Real.sqrt H →
      ∀ u : ℝ, |u| ≤ microcoreRadius A c N → ‖originalPhase d (Real.exp (-H)) u‖ < R := by
  obtain ⟨r,C,hr,_,hb⟩ := original_phase_small_radius d R hR
  refine ⟨r/2,by positivity,?_⟩
  intro A D hA hD
  filter_upwards [microcore_window_epsilon_le_radius D A (r/2) hD hA (by positivity)] with H hH
  intro N hN hwindow u hu
  have hrad : microcoreRadius A (r/2) N < r :=
    (microcoreRadius_le_prefactor A (r/2) hA (by positivity) N hN).trans_lt (half_lt_self hr)
  exact (hb _ _ u (Real.exp_pos _) (hH N hN hwindow) hrad hu).2

end
end IsingBulk.Tail
