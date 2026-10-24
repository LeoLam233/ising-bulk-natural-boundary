import IsingBulk.Anisotropic.NegativeNormalForm.ScalarPairSlope
import IsingBulk.Anisotropic.NegativeNormalForm.DensityAnalytic

/-! Dimension-free moving-center estimates for the actual scalar residue factors. -/
namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open Set Metric Filter
open scoped Topology
set_option maxHeartbeats 800000

/-- Evenness at zero drift removes the angular linear term, uniformly in the
pole parameter. Both scalar parameters may move in the same common ball. -/
theorem analytic_even_axis_moving_center_control (S : ScalarTriple → ℂ)
    (ha : AnalyticAt ℂ S 0) (heven : ∀ t v : ℂ, S (t,(0,-v))=S (t,(0,v))) :
    ∃ r L : ℝ, 0<r ∧ 0<L ∧ ∀ t t₀ d x : ℂ,
      ‖t‖<r → ‖t₀‖<r → ‖d‖<r → ‖x‖<r →
      ‖S (t,(d,x))-S (t₀,(d,0))‖ ≤
        L*(‖t-t₀‖+(‖d‖+‖x‖)*‖x‖) := by
  obtain ⟨r,L,hr,hL,hquad⟩ := analytic_even_axis_quadratic_control S ha heven
  obtain ⟨s,M,hs,hM,_ha,hLip⟩ := analytic_uniform_lipschitz ha
  refine ⟨min r s,L+M,lt_min hr hs,by positivity,?_⟩
  intro t t₀ d x ht ht₀ hd hx
  have hp : ‖(t,(d,x))‖<r :=
    (show max ‖t‖ (max ‖d‖ ‖x‖)<min r s from max_lt ht (max_lt hd hx)).trans_le (min_le_left _ _)
  have hbase : ‖(t,(d,(0:ℂ)))‖<s := by
    change max ‖t‖ (max ‖d‖ ‖(0:ℂ)‖)<s
    rw [norm_zero,max_eq_left (norm_nonneg _)]
    exact (max_lt ht hd).trans_le (min_le_right _ _)
  have hbase₀ : ‖(t₀,(d,(0:ℂ)))‖<s := by
    change max ‖t₀‖ (max ‖d‖ ‖(0:ℂ)‖)<s
    rw [norm_zero,max_eq_left (norm_nonneg _)]
    exact (max_lt ht₀ hd).trans_le (min_le_right _ _)
  have hparam := hLip (t,(d,0)) (t₀,(d,0)) hbase hbase₀
  have hdiff : ‖(t,(d,(0:ℂ)))-(t₀,(d,0))‖=‖t-t₀‖ := by
    simp [Prod.norm_def]
  rw [hdiff] at hparam
  calc
    _ ≤ ‖S (t,(d,x))-S (t,(d,0))‖+‖S (t,(d,0))-S (t₀,(d,0))‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ L*(‖d‖+‖x‖)*‖x‖+M*‖t-t₀‖ := add_le_add (hquad _ hp) hparam
    _ ≤ _ := by nlinarith [mul_nonneg hL.le (norm_nonneg (t-t₀)),
      mul_nonneg hM.le (mul_nonneg (add_nonneg (norm_nonneg d) (norm_nonneg x)) (norm_nonneg x))]

/-- The actual negative phase in moving angular coordinates. -/
theorem negativePhase_moving_analyticAt (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (hB : AnalyticAt ℂ B 0) :
    AnalyticAt ℂ (fun p : ScalarTriple => negativePhase B phi hphi p.1 (p.2.1+p.2.2)) 0 := by
  have hg : AnalyticAt ℂ (fun p : ℂ × ℂ => negativePhase B phi hphi p.1 p.2) (0,0) := by
    simpa only [Complex.cos_zero,sub_self] using negativePhase_analyticAt_center B phi hphi 0 (by simpa using hB)
  exact hg.fun_comp_of_eq (f := fun p : ScalarTriple => (p.1,p.2.1+p.2.2))
    (analyticAt_fst.prod ((analyticAt_fst.comp analyticAt_snd).add
      (analyticAt_snd.comp analyticAt_snd))) (by simp)

theorem negativePhase_moving_center_control (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (hB : AnalyticAt ℂ B 0) :
    ∃ r L : ℝ, 0<r ∧ 0<L ∧ ∀ t d x : ℂ,
      ‖t‖<r → ‖1-Complex.cos d‖<r → ‖d‖<r → ‖x‖<r →
      ‖negativePhase B phi hphi t (d+x)-(phi:ℂ)*Complex.I‖ ≤
        L*(‖t-(1-Complex.cos d)‖+(‖d‖+‖x‖)*‖x‖) := by
  obtain ⟨r,L,hr,hL,h⟩ := analytic_even_axis_moving_center_control _
    (negativePhase_moving_analyticAt B phi hphi hB)
    (fun t v => by simpa using negativePhase_even B phi hphi t v)
  refine ⟨r,L,hr,hL,?_⟩
  intro t d x ht ht₀ hd hx
  simpa only [add_zero,negativePhase_center] using h t (1-Complex.cos d) d x ht ht₀ hd hx

/-- Actual normalized one-body factor; its center is exactly one. -/
def residueOneBodyRatio (B : ℂ → ℂ) (phi : ℝ) (hphi : Real.sin phi≠0)
    (p : ScalarTriple) : ℂ :=
  ((Real.sin phi:ℂ)*Complex.I)/Complex.sinh (negativePhase B phi hphi p.1 (p.2.1+p.2.2))

theorem residueOneBodyRatio_center (B : ℂ → ℂ) (phi : ℝ) (hphi : Real.sin phi≠0) (d : ℂ) :
    residueOneBodyRatio B phi hphi (1-Complex.cos d,(d,0))=1 := by
  simp only [residueOneBodyRatio,add_zero,negativePhase_center,Complex.sinh_mul_I,←Complex.ofReal_sin]
  exact div_self (mul_ne_zero (by exact_mod_cast hphi) Complex.I_ne_zero)

theorem residueOneBodyRatio_control (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (hB : AnalyticAt ℂ B 0) :
    ∃ r L : ℝ, 0<r ∧ 0<L ∧ ∀ t d x : ℂ,
      ‖t‖<r → ‖1-Complex.cos d‖<r → ‖d‖<r → ‖x‖<r →
      ‖residueOneBodyRatio B phi hphi (t,(d,x))-1‖ ≤
        L*(‖t-(1-Complex.cos d)‖+(‖d‖+‖x‖)*‖x‖) := by
  have hs : Complex.sinh (negativePhase B phi hphi 0 0)≠0 := by
    simpa using phase_sinh_center_ne_zero B phi hphi 0
  have ha : AnalyticAt ℂ (residueOneBodyRatio B phi hphi) 0 :=
    analyticAt_const.div (Complex.analyticAt_sinh.comp (negativePhase_moving_analyticAt B phi hphi hB)) (by simpa using hs)
  obtain ⟨r,L,hr,hL,h⟩ := analytic_even_axis_moving_center_control _ ha
    (fun t v => by simp [residueOneBodyRatio,negativePhase_even])
  refine ⟨r,L,hr,hL,?_⟩
  intro t d x ht ht₀ hd hx
  simpa only [residueOneBodyRatio_center] using h t (1-Complex.cos d) d x ht ht₀ hd hx

end
end IsingBulk.Anisotropic.NegativeNormalForm
