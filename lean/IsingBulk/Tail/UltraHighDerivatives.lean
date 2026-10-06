import IsingBulk.Tail.OriginalUltraHighBound
import IsingBulk.First.FormFactorAnalytic
import IsingBulk.First.DominatedAnalyticIntegral

/-! Cauchy is applied on the actual original radial disk before any order
cutoff. The radius is fixed during every source derivative. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set Metric
open scoped Topology

theorem ultrahigh_derivative_factorial_bound (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) :
    ∃ C₀ D delta e0 : ℝ, 0 < C₀ ∧ 0 < D ∧ 0 < delta ∧ 0 < e0 ∧ e0 ≤ 1 ∧
      ∀ n : ℕ, 0 < n → ∀ j : ℕ, ∀ e : ℝ, 0 < e → e < e0 →
        ‖iteratedDeriv j (upperFormFactor (2*n)) (radialParameter d.theta e)‖ ≤
          (j.factorial:ℝ)*C₀*(e⁻¹)^2/(delta*e)^j *
            ((D*(Real.log (1/e)+1)^2)^n/(n.factorial:ℝ)) := by
  obtain ⟨C₀,D,deltaB,eB,hC,hD,hdB,heB,heB1,hbound⟩ :=
    original_ultrahigh_factorial_bound d hcsmall
  have hsin : 0 < Real.sin d.theta := Real.sin_pos_of_pos_of_lt_pi d.theta_pos
    (by linarith [d.theta_lt,Real.pi_pos])
  obtain ⟨deltaG,eG,A,B,hdG,heG,_,_,hglob⟩ :=
    original_disk_global_factors d.theta d.c₀ hsin d.c₀_pos hcsmall
  let delta := min deltaB deltaG
  refine ⟨C₀,D,delta,min eB eG,hC,hD,lt_min hdB hdG,lt_min heB heG,
    (min_le_left _ _).trans heB1,?_⟩
  intro n hn j e he heSmall
  have heB' := heSmall.trans_le (min_le_left eB eG)
  have heG' := heSmall.trans_le (min_le_right eB eG)
  let U := closedBall (radialParameter d.theta e) (delta*e)
  have hr : 0 < Real.exp (-d.c₀*e) := Real.exp_pos _
  have hr1 : Real.exp (-d.c₀*e) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [d.c₀_pos])
  have hmargin (s : ℂ) (hs : s ∈ U) :
      (Real.exp (-d.c₀*e))⁻¹-Real.exp (-d.c₀*e) < (sourceS s).im := by
    have hs' : ‖s-radialParameter d.theta e‖ ≤ deltaG*e :=
      (mem_closedBall_iff_norm.mp hs).trans
        (mul_le_mul_of_nonneg_right (min_le_right deltaB deltaG) he.le)
    have hm := (hglob e he heG' s hs').1
    simpa only [neg_mul,Real.exp_neg,inv_inv] using hm
  have ha (s : ℂ) (hs : s ∈ U) : AnalyticAt ℂ (upperFormFactor (2*n)) s := by
    apply upperFormFactor_analyticAt (2*n) (by omega)
    have hm := hmargin s hs
    have hi : 1 < (Real.exp (-d.c₀*e))⁻¹ := (one_lt_inv₀ hr).mpr hr1
    linarith
  have hb (s : ℂ) (hs : s ∈ U) : ‖upperFormFactor (2*n) s‖ ≤
      C₀*e⁻¹^2*((D*(Real.log (1/e)+1)^2)^n/(n.factorial:ℝ)) := by
    rw [upperFormFactor_eq_fixed_radius (2*n) (by omega) hr hr1 (hmargin s hs)]
    exact hbound n hn e he heB' s ((mem_closedBall_iff_norm.mp hs).trans
      (mul_le_mul_of_nonneg_right (min_le_left deltaB deltaG) he.le))
  have hd : 0 < delta*e := mul_pos (lt_min hdB hdG) he
  have ht := cauchy_bound_on_subdisk ha hb hd (by intro x hx; exact hx) j
  convert ht using 1
  ring

end
end IsingBulk.Tail
