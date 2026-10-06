import IsingBulk.Tail.OriginalResidueL2
import IsingBulk.Tail.UltraHighWeightedPairs

/-! The actual original weighted matched pair has the required logarithmic
square cost, uniformly on one fixed c epsilon complex disk. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch MeasureTheory Set
open scoped Topology

def originalWeightedPairIntegral (d : LocalBranchData) (e : ℝ) (s : ℂ) : ℝ :=
  ∫ p in Icc (0:ℝ) (2*Real.pi) ×ˢ Icc (0:ℝ) (2*Real.pi),
    ‖originalResidueAngle d e s p.1‖*‖originalResidueAngle d e s p.2‖*
      ‖pairKernel (anglePoint (Real.exp (-d.c₀*e)) p.1) (anglePoint (Real.exp (-d.c₀*e)) p.2)‖

theorem original_weighted_pair_logarithmic_square (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) :
    ∃ C delta e0 : ℝ, 0 < C ∧ 0 < delta ∧ 0 < e0 ∧ e0 ≤ 1 ∧
      ∀ e : ℝ, 0 < e → e < e0 → ∀ s : ℂ,
        ‖s-radialParameter d.theta e‖ ≤ delta*e →
        originalWeightedPairIntegral d e s ≤ C*(Real.log (1/e)+1)^2 := by
  obtain ⟨A,deltaL,eL,hA,hdL,heL,heL1,hL2⟩ := original_residue_l2_oneperiod d hcsmall
  obtain ⟨_,_,deltaR,eR,_,_,hdR,heR,_,hR⟩ := original_residue_square_pointwise d hcsmall
  let delta := min deltaL deltaR
  let e0 := min eL (min eR (1/(2*d.c₀)))
  let K := 2*simpleKernelConstant*(1+|Real.log (2*d.c₀)|)
  have hSK : 0 < simpleKernelConstant := by unfold simpleKernelConstant; positivity
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨A*K,delta,e0,mul_pos hA hK,lt_min hdL hdR,?_,?_,?_⟩
  · exact lt_min heL (lt_min heR (by have := d.c₀_pos; positivity))
  · exact (min_le_left _ _).trans heL1
  · intro e he heSmall s hs
    have heL' : e < eL := heSmall.trans_le (min_le_left _ _)
    have heR' : e < eR := heSmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have heSmall' : e ≤ 1/(2*d.c₀) := heSmall.le.trans ((min_le_right _ _).trans (min_le_right _ _))
    have he1 : e ≤ 1 := heL'.le.trans heL1
    have hsL := hs.trans (mul_le_mul_of_nonneg_right (min_le_left deltaL deltaR) he.le)
    have hsR := hs.trans (mul_le_mul_of_nonneg_right (min_le_right deltaL deltaR) he.le)
    have hcont := (hR e he heR' s hsR).1.norm
    have hr : 0 < Real.exp (-d.c₀*e) := Real.exp_pos _
    have hr1 : Real.exp (-d.c₀*e) < 1 := by
      rw [Real.exp_lt_one_iff]
      have := d.c₀_pos
      nlinarith
    have hp := original_weighted_y_pair_integral_le hr.le hr1 hcont (fun _ => norm_nonneg _)
    have hL := hL2 e he heL' s hsL
    have hL' : (∫ x in Icc (0:ℝ) (2*Real.pi), ‖originalResidueAngle d e s x‖^2) ≤
        A*(Real.log (1/e)+1) := by
      simpa only [originalResidueAngle,radialAnglePoint_eq_anglePoint_exp] using hL
    have hsmall : 2*d.c₀*e ≤ 1 := by
      have h := (le_div_iff₀ (show 0 < 2*d.c₀ by have := d.c₀_pos; positivity)).mp heSmall'
      nlinarith
    have hk := original_y_kernel_period_integral d.c₀_pos he hsmall 0
    simp only [zero_add] at hk
    rw [intervalIntegral.integral_of_le Real.two_pi_pos.le,← integral_Icc_eq_integral_Ioc] at hk
    have hloge : Real.log e ≤ 0 := Real.log_nonpos he.le he1
    have hlog : |Real.log (2*d.c₀*e)| ≤ |Real.log (2*d.c₀)|+Real.log (1/e) := by
      rw [Real.log_mul (by have := d.c₀_pos; positivity : 2*d.c₀ ≠ 0) he.ne']
      apply (abs_add_le _ _).trans_eq
      rw [abs_of_nonpos hloge,one_div,Real.log_inv]
    have hH : 0 ≤ Real.log (1/e) := by rw [one_div,Real.log_inv]; linarith
    have hkernel : (∫ y in Icc (0:ℝ) (2*Real.pi), originalYKernel (Real.exp (-d.c₀*e)) y) ≤
        K*(Real.log (1/e)+1) := by
      apply hk.trans
      dsimp only [K]
      have ha := abs_nonneg (Real.log (2*d.c₀))
      have hh : 1+|Real.log (2*d.c₀*e)| ≤
          (1+|Real.log (2*d.c₀)|)*(Real.log (1/e)+1) := by
        nlinarith [mul_nonneg ha hH]
      exact (mul_le_mul_of_nonneg_left hh (by positivity)).trans_eq (by ring)
    have hkpos : 0 ≤ ∫ y in Icc (0:ℝ) (2*Real.pi), originalYKernel (Real.exp (-d.c₀*e)) y :=
      setIntegral_nonneg measurableSet_Icc (fun y hy => originalYKernel_nonneg _ _)
    apply hp.trans
    have hm := mul_le_mul hL' hkernel hkpos (by positivity : 0 ≤ A*(Real.log (1/e)+1))
    convert hm using 1
    ring

end
end IsingBulk.Tail
