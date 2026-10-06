import IsingBulk.First.CompatibleYLocalization
import IsingBulk.First.MeanSelectedData

/-! The mean rectangle is chosen first. This constructor uses that exact
prescribed sufficiently small delta, avoiding circular cutoff/contour choices. -/
namespace IsingBulk.First
noncomputable section
open Complex Set Metric Filter
open scoped Topology ContDiff

def compatibleCutoffDeltaBound (alpha beta : ℝ) : ℝ :=
  min (1/16) (‖exp (-(alpha:ℂ)*I)-exp (-(beta:ℂ)*I)‖/16)

theorem compatibleCutoffDeltaBound_pos {alpha beta : ℝ}
    (hne : exp (-(alpha:ℂ)*I) ≠ exp (-(beta:ℂ)*I)) :
    0 < compatibleCutoffDeltaBound alpha beta := by
  exact lt_min (by norm_num) (div_pos (norm_sub_pos_iff.mpr hne) (by norm_num))

theorem exists_compatibleYCutoffData_at_delta (n : ℕ) (alpha beta : ℝ)
    {U : Set (Fin n → ℝ)} (hU : U ∈ 𝓝 (0 : Fin n → ℝ))
    {Hmax delta : ℝ} (hH : 0 < Hmax) (hd : 0 < delta)
    (hsmall : delta ≤ compatibleCutoffDeltaBound alpha beta) :
    ∃ c : CompatibleYCutoffData n alpha beta U, c.delta = delta ∧ c.H ≤ Hmax := by
  let H := min Hmax delta
  have hp : 0 < H := lt_min hH hd
  have hHd : H ≤ delta := min_le_right _ _
  have hHmax : H ≤ Hmax := min_le_left _ _
  have hd1 : delta ≤ 1/16 := hsmall.trans (min_le_left _ _)
  have hds : delta ≤ ‖exp (-(alpha:ℂ)*I)-exp (-(beta:ℂ)*I)‖/16 :=
    hsmall.trans (min_le_right _ _)
  obtain ⟨chi,hχ,hχc,hχr,hχ1,hχU,hχs⟩ := exists_fixed_shape_cutoff n hp hU
  let b : ContDiffBump (0:ℝ) := ⟨delta,2*delta,hd,by linarith⟩
  let c : CompatibleYCutoffData n alpha beta U := {
    H := H, delta := delta, H_pos := hp, delta_pos := hd,
    chi := chi, eta := b, chi_smooth := hχ, eta_smooth := b.contDiff,
    chi_compact := hχc, eta_compact := b.hasCompactSupport,
    chi_range := hχr, eta_range := fun v => ⟨b.nonneg,b.le_one⟩,
    chi_one := hχ1, chi_support := hχU,
    shape_support := fun t ht => hχs t (subset_closure ht),
    eta_one := by
      intro v hv
      apply b.one_of_mem_closedBall
      simpa only [mem_closedBall,Real.dist_eq,sub_zero] using hv,
    eta_support := by
      intro v hv
      have hm : v ∈ Function.support b := hv
      rw [b.support_eq] at hm
      simpa only [mem_ball,Real.dist_eq,sub_zero] using hm,
    small := by linarith,
    separated := by linarith }
  exact ⟨c,rfl,hHmax⟩

theorem ordered_chart_centers_ne (a : OrderedChartData) (hab : a.alpha ≠ a.beta) :
    exp (-(a.alpha:ℂ)*I) ≠ exp (-(a.beta:ℂ)*I) := by
  intro he
  have hh := Complex.exp_inj_of_neg_pi_lt_of_le_pi
    (x := -(a.alpha:ℂ)*I) (y := -(a.beta:ℂ)*I)
    (by simpa using (show -Real.pi < -a.alpha by linarith [a.alpha_lt,Real.pi_pos]))
    (by simpa using (show -a.alpha ≤ Real.pi by linarith [a.alpha_pos,Real.pi_pos]))
    (by simpa using (show -Real.pi < -a.beta by linarith [a.beta_lt,Real.pi_pos]))
    (by simpa using (show -a.beta ≤ Real.pi by linarith [a.beta_pos,Real.pi_pos])) he
  have hi := congrArg Complex.im hh
  have hab' : a.alpha = a.beta := by simpa using hi
  exact hab hab'

end
end IsingBulk.First
