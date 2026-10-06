import IsingBulk.First.PeriodicYSupport

/-! Periodicization of an actual small compact chart bump about an arbitrary
lifted center. Vanishing near the principal-log seam gives global smoothness. -/
namespace IsingBulk.First
noncomputable section
open Set Filter Metric
open scoped Topology ContDiff

def centeredWrap {N : ℕ} (c x : Fin N → ℝ) : Fin N → ℝ :=
  fun i => c i+periodicAngle (x i-c i)

def periodicizeBump {N : ℕ} (c : Fin N → ℝ) (w : (Fin N → ℝ) → ℝ) : (Fin N → ℝ) → ℝ :=
  fun x => w (centeredWrap c x)

theorem periodicAngle_cos (u : ℝ) : Real.cos (periodicAngle u) = Real.cos u := by
  have he := congrArg Complex.re (periodicAngle_exp u)
  simpa only [Complex.exp_ofReal_mul_I_re] using he

theorem periodicAngle_neg_pi : periodicAngle (-Real.pi) = Real.pi := by
  have hp := periodicAngle_periodic (-Real.pi)
  rw [show -Real.pi+2*Real.pi=Real.pi by ring] at hp
  rw [← hp]
  exact periodicAngle_eq (by linarith [Real.pi_pos]) le_rfl

theorem centeredWrap_eq {N : ℕ} {c x : Fin N → ℝ}
    (hx : ∀ i, -Real.pi < x i-c i ∧ x i-c i ≤ Real.pi) : centeredWrap c x = x := by
  funext i
  rw [centeredWrap, periodicAngle_eq (hx i).1 (hx i).2]
  ring

theorem centeredWrap_update_period {N : ℕ} (c x : Fin N → ℝ) (i : Fin N) :
    centeredWrap c (Function.update x i (x i+2*Real.pi)) = centeredWrap c x := by
  funext j
  by_cases hj : j=i
  · subst j
    simp only [centeredWrap, Function.update_self]
    rw [show x i+2*Real.pi-c i=(x i-c i)+2*Real.pi by ring, periodicAngle_periodic]
  · simp only [centeredWrap, Function.update_of_ne hj]

theorem periodicizeBump_update_period {N : ℕ} (c x : Fin N → ℝ)
    (w : (Fin N → ℝ) → ℝ) (i : Fin N) :
    periodicizeBump c w (Function.update x i (x i+2*Real.pi)) = periodicizeBump c w x := by
  unfold periodicizeBump
  rw [centeredWrap_update_period]

theorem periodicizeBump_support_cos {N : ℕ} (c : Fin N → ℝ) (w : (Fin N → ℝ) → ℝ)
    (hw : ∀ x, w x ≠ 0 → ∀ i, |x i-c i| ≤ 1/2) {x : Fin N → ℝ}
    (hx : periodicizeBump c w x ≠ 0) (i : Fin N) : 3/4 ≤ Real.cos (x i-c i) := by
  have hh := hw (centeredWrap c x) hx i
  simp only [centeredWrap, add_sub_cancel_left] at hh
  have hb := Real.one_sub_sq_div_two_le_cos (x := periodicAngle (x i-c i))
  rw [periodicAngle_cos] at hb
  have hab := abs_le.mp hh
  nlinarith

theorem periodicizeBump_contDiff {N : ℕ} (c : Fin N → ℝ) (w : (Fin N → ℝ) → ℝ)
    (hw : ContDiff ℝ ∞ w) (hsmall : ∀ x, w x ≠ 0 → ∀ i, |x i-c i| ≤ 1/2) :
    ContDiff ℝ ∞ (periodicizeBump c w) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hall : ∀ i, 0 < Real.cos (x i-c i)
  · have hc : ContDiffAt ℝ ∞ (centeredWrap c) x := by
      apply contDiffAt_pi.mpr
      intro i
      have hi : ContDiffAt ℝ ∞ (fun y : Fin N → ℝ => y i-c i) x := by fun_prop
      exact contDiffAt_const.add ((periodicAngle_contDiffAt (hall i)).comp x
        (f := fun y : Fin N → ℝ => y i-c i) hi)
    exact hw.contDiffAt.comp x hc
  · push Not at hall
    obtain ⟨i,hi⟩ := hall
    have hcos : ContinuousAt (fun y : Fin N → ℝ => Real.cos (y i-c i)) x :=
      Real.continuous_cos.continuousAt.comp ((continuous_apply i).continuousAt.sub continuousAt_const)
    have hn : ∀ᶠ y : Fin N → ℝ in 𝓝 x, Real.cos (y i-c i) < 1/2 :=
      hcos.eventually (Iio_mem_nhds (by linarith))
    have hz : periodicizeBump c w =ᶠ[𝓝 x] (fun _ => 0) := by
      filter_upwards [hn] with y hy
      by_contra he
      linarith [periodicizeBump_support_cos c w hsmall he i]
    exact contDiffAt_const.congr_of_eventuallyEq hz

/-- On the centered closed fundamental box, the periodicized weight is exactly
the original compact lift. The seam endpoints are zero on both sides. -/
theorem periodicizeBump_eq_on_centeredBox {N : ℕ} (c : Fin N → ℝ) (w : (Fin N → ℝ) → ℝ)
    (hsmall : ∀ x, w x ≠ 0 → ∀ i, |x i-c i| ≤ 1/2) {x : Fin N → ℝ}
    (hx : ∀ i, -Real.pi ≤ x i-c i ∧ x i-c i ≤ Real.pi) : periodicizeBump c w x = w x := by
  by_cases hall : ∀ i, -Real.pi < x i-c i
  · unfold periodicizeBump
    rw [centeredWrap_eq (fun i => ⟨hall i,(hx i).2⟩)]
  · push Not at hall
    obtain ⟨i,hi⟩ := hall
    have he : x i-c i = -Real.pi := le_antisymm hi (hx i).1
    have hwx : w x = 0 := by
      by_contra hn
      have hh := hsmall x hn i
      rw [he, abs_neg, abs_of_pos Real.pi_pos] at hh
      linarith [Real.pi_gt_three]
    have hww : w (centeredWrap c x) = 0 := by
      by_contra hn
      have hh := hsmall (centeredWrap c x) hn i
      simp only [centeredWrap, he, periodicAngle_neg_pi, add_sub_cancel_left,
        abs_of_pos Real.pi_pos] at hh
      linarith [Real.pi_gt_three]
    exact hww.trans hwx.symm

end
end IsingBulk.First
