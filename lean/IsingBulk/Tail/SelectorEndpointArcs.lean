import IsingBulk.Tail.SelectorCutoffs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds

/-! The exact endpoint-width convention of manuscript Section 5 is met by
the constructed selector, taking α=sin δ and sufficiently small fixed δ. -/
namespace IsingBulk.Tail
noncomputable section
open Filter
open scoped Topology

theorem small_width_sine_pos (δ : ℝ) (hδ : 0 < δ) (hsmall : δ ≤ 1/4) :
    0 < Real.sin δ :=
  Real.sin_pos_of_pos_of_lt_pi hδ (by linarith [Real.pi_gt_three])

theorem endpoint_sine_le (δ θ : ℝ) (hδ : 0 < δ) (hsmall : δ ≤ 1/4)
    (hθlo : -Real.pi ≤ θ) (hθhi : θ ≤ Real.pi)
    (hθ : θ ≤ δ ∨ Real.pi-δ ≤ θ) : Real.sin θ ≤ Real.sin δ := by
  rcases hθ with hθ | hθ
  · by_cases hn : θ ≤ 0
    · exact (Real.sin_nonpos_of_nonpos_of_neg_pi_le hn hθlo).trans
        (small_width_sine_pos δ hδ hsmall).le
    · exact Real.sin_le_sin_of_le_of_le_pi_div_two
        (by linarith [Real.pi_pos]) (by linarith [Real.pi_gt_three]) hθ
  · rw [← Real.sin_pi_sub θ]
    exact Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [Real.pi_pos]) (by linarith [Real.pi_gt_three]) (by linarith)

theorem inner_upper_sine_ge (δ θ : ℝ) (hδ : 0 < δ) (hsmall : δ ≤ 1/4)
    (hθlo : 2*δ ≤ θ) (hθhi : θ ≤ Real.pi-2*δ) :
    3*Real.sin δ/2 ≤ Real.sin θ := by
  have hsin := small_width_sine_pos δ hδ hsmall
  have hcos : 3/4 ≤ Real.cos δ := by
    have ht := Real.one_sub_sq_div_two_le_cos (x := δ)
    nlinarith
  have hdouble : 3*Real.sin δ/2 ≤ Real.sin (2*δ) := by
    rw [Real.sin_two_mul]
    nlinarith
  apply hdouble.trans
  by_cases hh : θ ≤ Real.pi/2
  · exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) hh hθlo
  · rw [← Real.sin_pi_sub θ]
    exact Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [Real.pi_pos]) (by linarith) (by linarith)

theorem selectorA_zero_endpoint_arcs (δ θ : ℝ) (hδ : 0 < δ) (hsmall : δ ≤ 1/4)
    (hθlo : -Real.pi ≤ θ) (hθhi : θ ≤ Real.pi)
    (hθ : θ ≤ δ ∨ Real.pi-δ ≤ θ) :
    periodicUpperA (Real.sin δ) θ = 0 := by
  apply thresholdStep_zero
  · linarith [small_width_sine_pos δ hδ hsmall]
  · exact endpoint_sine_le δ θ hδ hsmall hθlo hθhi hθ

theorem selectorA_one_middle_arc (δ θ : ℝ) (hδ : 0 < δ) (hsmall : δ ≤ 1/4)
    (hθlo : 2*δ ≤ θ) (hθhi : θ ≤ Real.pi-2*δ) :
    periodicUpperA (Real.sin δ) θ = 1 := by
  apply thresholdStep_one
  · linarith [small_width_sine_pos δ hδ hsmall]
  · exact inner_upper_sine_ge δ θ hδ hsmall hθlo hθhi

theorem upper_interval_sine_min (δ θ : ℝ) (hδ : 0 < δ) (_hsmall : δ ≤ 1/4)
    (hθlo : δ ≤ θ) (hθhi : θ ≤ Real.pi-δ) : Real.sin δ ≤ Real.sin θ := by
  by_cases hh : θ ≤ Real.pi/2
  · exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) hh hθlo
  · rw [← Real.sin_pi_sub θ]
    exact Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [Real.pi_pos]) (by linarith) (by linarith)

/-- The p=1 region has positive slack around the source closed [δ,π−δ]
arc, which includes both the a support and every a derivative support. -/
theorem selectorP_one_near_closed_upper_arc (δ θ : ℝ) (hδ : 0 < δ)
    (hsmall : δ ≤ 1/4) (hθlo : δ ≤ θ) (hθhi : θ ≤ Real.pi-δ) :
    periodicUpperP (Real.sin δ) =ᶠ[nhds θ] (fun _ => 1) := by
  have hα := small_width_sine_pos δ hδ hsmall
  have hs := upper_interval_sine_min δ θ hδ hsmall hθlo hθhi
  have he : ∀ᶠ t in nhds θ, 3*Real.sin δ/4 < Real.sin t :=
    Real.continuous_sin.continuousAt.eventually (Ioi_mem_nhds (by linarith))
  filter_upwards [he] with t ht
  exact thresholdStep_one (by linarith) ht.le

end
end IsingBulk.Tail
