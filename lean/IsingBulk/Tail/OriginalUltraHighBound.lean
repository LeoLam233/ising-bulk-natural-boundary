import IsingBulk.Tail.OriginalFormFactorIntegral
import IsingBulk.Tail.OriginalDiskGlobalFactors

/-! Actual original-contour all-even-order bound, with uniform complex disk
and constants fixed before the order and radial limit. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set
open scoped Topology
set_option maxHeartbeats 800000

theorem original_ultrahigh_factorial_bound (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) :
    ∃ C₀ D delta e0 : ℝ, 0 < C₀ ∧ 0 < D ∧ 0 < delta ∧ 0 < e0 ∧ e0 ≤ 1 ∧
      ∀ n : ℕ, 0 < n → ∀ e : ℝ, 0 < e → e < e0 → ∀ s : ℂ,
        ‖s-radialParameter d.theta e‖ ≤ delta*e →
        ‖doubleFormFactor (2*n) (Real.exp (-d.c₀*e)) s‖ ≤
          C₀*(e⁻¹)^2*((D*(Real.log (1/e)+1)^2)^n/(n.factorial:ℝ)) := by
  have hsin : 0 < Real.sin d.theta :=
    Real.sin_pos_of_pos_of_lt_pi d.theta_pos (by linarith [d.theta_lt,Real.pi_pos])
  obtain ⟨C,deltaP,eP,hC,hdP,heP,heP1,hpf⟩ := original_weighted_pfaffian_bound d hcsmall
  obtain ⟨deltaG,eG,A,B,hdG,heG,hA,hB,hglob⟩ :=
    original_disk_global_factors d.theta d.c₀ hsin d.c₀_pos hcsmall
  let Q := max A (Real.exp 1)
  have hQ : 0 < Q := lt_of_lt_of_le hA (le_max_left _ _)
  refine ⟨2*B,Q^2*C/2,min deltaP deltaG,min eP eG,by positivity,by positivity,
    lt_min hdP hdG,lt_min heP heG,(min_le_left _ _).trans heP1,?_⟩
  intro n hn e he heSmall s hs
  have heP' := heSmall.trans_le (min_le_left eP eG)
  have heG' := heSmall.trans_le (min_le_right eP eG)
  have he1 := heP'.le.trans heP1
  have hsP := hs.trans (mul_le_mul_of_nonneg_right (min_le_left deltaP deltaG) he.le)
  have hsG := hs.trans (mul_le_mul_of_nonneg_right (min_le_right deltaP deltaG) he.le)
  obtain ⟨hmargin,hinv,hgap⟩ := hglob e he heG' s hsG
  let r := Real.exp (-d.c₀*e)
  have hr : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [d.c₀_pos])
  have hm : r⁻¹-r < (sourceS s).im := by
    simpa only [r,neg_mul,Real.exp_neg,inv_inv] using hmargin
  have hb := original_formFactor_weighted_integral d n hn he hm hA.le hinv
  have hpair := hpf n e he heP' s hsP
  have hgap' : (1-r^2)⁻¹^2 ≤ B*e⁻¹^2 := by
    have hh : r^2=Real.exp (-2*d.c₀*e) := by
      dsimp only [r]
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    simpa only [hh] using hgap
  have hmax : max A r⁻¹ ≤ Q := by
    apply max_le (le_max_left _ _)
    apply le_trans _ (le_max_right A (Real.exp 1))
    · change r⁻¹ ≤ Real.exp 1
      rw [show r⁻¹=Real.exp (d.c₀*e) by simp [r,neg_mul,Real.exp_neg]]
      apply Real.exp_le_exp.mpr
      have hc : d.c₀ ≤ 1/2 := by linarith [Real.sin_le_one d.theta]
      nlinarith [d.c₀_pos]
  have hj : 0 ≤ r/(2*Real.pi) := by positivity
  have hj1 : r/(2*Real.pi) ≤ 1 := by
    apply (div_le_one (by positivity : 0 < 2*Real.pi)).mpr
    linarith [Real.pi_gt_three]
  have hg : 0 < 1-r^2 := by nlinarith
  have hglobal : 2*(max A r⁻¹)^(2*n)/(1-r^2)^2 ≤ 2*Q^(2*n)*B*e⁻¹^2 := by
    rw [div_eq_mul_inv,inv_pow]
    calc
      _ ≤ 2*Q^(2*n)*(B*e⁻¹^2) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (le_trans hA.le (le_max_left _ _)) hmax _) (by norm_num)
        · simpa only [inv_pow] using hgap'
        · positivity
        · positivity
      _ = _ := by ring
  have hfac : 0 ≤ ((2*n).factorial:ℝ)⁻¹ := by positivity
  have hpn : 0 ≤ (matchingCount n:ℝ)*(C*(Real.log (1/e)+1)^2)^n := by positivity
  calc
    _ ≤ ((2*n).factorial:ℝ)⁻¹*(r/(2*Real.pi))^(2*n)*
        (2*(max A r⁻¹)^(2*n)/(1-r^2)^2)*
        ((matchingCount n:ℝ)*(C*(Real.log (1/e)+1)^2)^n) := by
      exact hb.trans (mul_le_mul_of_nonneg_left hpair (by positivity))
    _ ≤ ((2*n).factorial:ℝ)⁻¹*1*(2*Q^(2*n)*B*e⁻¹^2)*
        ((matchingCount n:ℝ)*(C*(Real.log (1/e)+1)^2)^n) := by
      gcongr
      exact pow_le_one₀ hj hj1
    _ = (2*B)*e⁻¹^2*((Q^2*C/2*(Real.log (1/e)+1)^2)^n/(n.factorial:ℝ)) := by
      have hf := matching_majorant_identity n 1 Q (C*(Real.log (1/e)+1)^2) 1 1
      norm_num only [one_pow,one_mul,mul_one,div_one] at hf
      have hh := congrArg (fun x : ℝ => B*e⁻¹^2*x) hf
      convert hh using 1 <;> ring

end
end IsingBulk.Tail
