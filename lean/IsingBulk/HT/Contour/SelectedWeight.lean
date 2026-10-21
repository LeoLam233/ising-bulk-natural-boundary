import IsingBulk.Tail.SelectedFWeightedIntegral

/-! Quantitative mass of the actual discounted selected one-body weight.
This pays for the auxiliary dummy angle in the odd matching adapter.
The resulting loss is only one power of L, independent of particle number. -/
namespace IsingBulk.HT.Contour
noncomputable section
open IsingBulk.Tail Set MeasureTheory

/-- A pointwise lower bound on the existing weight, with no new cutoff. -/
theorem discountedSelectedWeight_lower {b η C eps L θ : ℝ}
    (hb : 0 ≤ b) (hbT : b ≤ 2*Real.pi) (hC : 0 ≤ C)
    (heps : 0 < eps) (heps1 : eps ≤ 1) (hL : 1 ≤ L)
    (hθ : θ ∈ Icc 0 (2*Real.pi)) :
    C / (L*(2*Real.pi+1)) ≤ discountedSelectedWeight b η C eps L θ := by
  have hT : 0 < 2*Real.pi := Real.two_pi_pos
  have hL0 : 0 < L := by linarith
  have hLT : 0 < L*(2*Real.pi+1) := by positivity
  unfold discountedSelectedWeight
  split_ifs with hcompact
  · exact div_le_div_of_nonneg_left hC hL0 (by nlinarith [mul_nonneg hL0.le hT.le])
  · have ha : |θ+b-2*Real.pi| ≤ 2*Real.pi := by
      apply abs_le.mpr
      constructor <;> linarith [hθ.1,hθ.2]
    have hs0 : 0 < Real.sqrt (|θ+b-2*Real.pi|+eps) := Real.sqrt_pos.mpr (by positivity)
    have hs : Real.sqrt (|θ+b-2*Real.pi|+eps) ≤ 2*Real.pi+1 := by
      apply Real.sqrt_le_iff.mpr
      constructor
      · positivity
      · nlinarith [sq_nonneg (2*Real.pi)]
    apply div_le_div_of_nonneg_left hC hs0
    nlinarith [mul_nonneg (sub_nonneg.mpr hL) (show 0 ≤ 2*Real.pi+1 by positivity)]

/-- The dummy one-body mass is at least a constant times L^{-1}; this
prevents an epsilon-dependent loss at each physical particle. -/
theorem discountedSelectedWeight_mass_lower {b η C eps L : ℝ}
    (hb : 0 ≤ b) (hbT : b ≤ 2*Real.pi) (hC : 0 ≤ C)
    (heps : 0 < eps) (heps1 : eps ≤ 1) (hL : 1 ≤ L) :
    (2*Real.pi)*C / (L*(2*Real.pi+1)) ≤
      ∫ θ in Icc 0 (2*Real.pi), discountedSelectedWeight b η C eps L θ := by
  have hi := (discountedSelectedWeight_integrable hb hbT hC heps hL (η := η)).1
  have hc : IntegrableOn (fun _ : ℝ => C/(L*(2*Real.pi+1))) (Icc 0 (2*Real.pi)) :=
    continuous_const.continuousOn.integrableOn_compact isCompact_Icc
  have hm := setIntegral_mono_on hc hi measurableSet_Icc
    (fun θ hθ => discountedSelectedWeight_lower hb hbT hC heps heps1 hL hθ (η := η))
  have he : (∫ _θ in Icc (0:ℝ) (2*Real.pi), C/(L*(2*Real.pi+1))) =
      (2*Real.pi)*C/(L*(2*Real.pi+1)) := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by positivity)]
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
    ring
  rwa [he] at hm

theorem discountedSelectedWeight_mass_pos {b η C eps L : ℝ}
    (hb : 0 ≤ b) (hbT : b ≤ 2*Real.pi) (hC : 0 < C)
    (heps : 0 < eps) (heps1 : eps ≤ 1) (hL : 1 ≤ L) :
    0 < ∫ θ in Icc 0 (2*Real.pi), discountedSelectedWeight b η C eps L θ := by
  have hL0 : 0 < L := by linarith
  apply lt_of_lt_of_le _ (discountedSelectedWeight_mass_lower hb hbT hC.le heps heps1 hL)
  positivity

end
end IsingBulk.HT.Contour
