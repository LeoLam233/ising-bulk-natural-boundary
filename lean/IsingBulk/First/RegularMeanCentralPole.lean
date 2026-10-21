import IsingBulk.First.RegularCentralPhase
import IsingBulk.First.MeanSideIsolation

/-! Sign-independent regular phase foundation for the actual source. -/
namespace IsingBulk.First.Regular
noncomputable section
open Complex Filter Set IsingBulk.Branch
open scoped Topology BigOperators

theorem chartW_selected_center (a : RegularChartData) (u : ℂ) :
    IsingBulk.Jets.chartW (exp ((a.theta:ℂ)*I)) 0 a.alpha u =
      ((Real.cos a.alpha+Real.cos a.beta:ℝ):ℂ)-Complex.cos (u-(a.alpha:ℂ)) := by
  have hS := IsingBulk.PrimeFamily.exp_angle_add_inv a.theta
  have hangle : ((Real.cos a.alpha+Real.cos a.beta:ℝ):ℂ)=2*(Real.cos a.theta:ℂ) := by
    exact_mod_cast a.angle_relation
  rw [IsingBulk.Jets.chartW_eq_plateauW]
  simp only [plateauW, Complex.ofReal_zero, zero_add, Complex.cosh_mul_I, hS, hangle]
  congr 1
  congr 1
  ring

def centralMeanZ (a : RegularChartData) (n : ℕ) (v : ℂ) : ℂ :=
  coordinateProduct (meanChartRoots (exp ((a.theta:ℂ)*I)) 0 a.alpha (0 : Fin n → ℝ) v)

theorem centralMeanZ_eq_exp (a : RegularChartData) (n : ℕ) (v : ℂ) :
    centralMeanZ a n v = exp ((-I*(n+1:ℂ))*centralChartPhase a (v/(n+1))) := by
  unfold centralMeanZ coordinateProduct meanChartRoots
  simp only [shapeExtend_zero, Pi.zero_apply, Complex.ofReal_zero, zero_add, chartW_selected_center,
    phaseRoot, centralChartPhase, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem centralMeanZ_zero (a : RegularChartData) (n : ℕ)
    (hbeta : exp (-(n+1:ℂ)*(a.beta:ℂ)*I)=1) : centralMeanZ a n 0 = 1 := by
  rw [centralMeanZ_eq_exp,zero_div,centralChartPhase_zero]
  convert hbeta using 1
  congr 1
  ring

theorem centralMeanZ_analytic (a : RegularChartData) (n : ℕ) : AnalyticAt ℂ (centralMeanZ a n) 0 := by
  have he : centralMeanZ a n = fun v => exp ((-I*(n+1:ℂ))*centralChartPhase a (v/(n+1))) :=
    funext (centralMeanZ_eq_exp a n)
  rw [he]
  have hi : AnalyticAt ℂ (fun v : ℂ => v/(n+1)) 0 := by fun_prop
  have ho : AnalyticAt ℂ (centralChartPhase a) ((0:ℂ)/(n+1)) := by
    simpa using centralChartPhase_analytic_zero a
  exact (analyticAt_const.mul (AnalyticAt.comp (f := fun v : ℂ => v/(n+1))
    (g := centralChartPhase a) ho hi)).cexp

theorem centralMeanZ_hasDerivAt_zero (a : RegularChartData) (n : ℕ)
    (hbeta : exp (-(n+1:ℂ)*(a.beta:ℂ)*I)=1) :
    HasDerivAt (centralMeanZ a n) (-I*(a.b:ℂ)) 0 := by
  have he : centralMeanZ a n = fun v => exp ((-I*(n+1:ℂ))*centralChartPhase a (v/(n+1))) :=
    funext (centralMeanZ_eq_exp a n)
  rw [he]
  have hp := (centralChartPhase_hasDerivAt_zero a).comp_of_eq 0
    ((hasDerivAt_id (0:ℂ)).div_const (n+1:ℂ)) (by simp)
  have hh := (hp.const_mul (-I*(n+1:ℂ))).cexp
  change HasDerivAt (fun v : ℂ => exp ((-I*(n+1:ℂ))*centralChartPhase a (v/(n+1)))) _ 0 at hh
  have hb : exp ((-I*(n+1:ℂ))*(a.beta:ℂ))=1 := by
    convert hbeta using 1
    congr 1
    ring
  convert! hh using 1
  simp only [Function.comp_def,id_eq,zero_div,centralChartPhase_zero,hb,one_mul]
  have hN : (n+1:ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  field_simp

/-- The actual source Z mean pole at zero shape is simple, with slope -ib. -/
theorem centralMeanZ_linear_gap (a : RegularChartData) (n : ℕ)
    (hbeta : exp (-(n+1:ℂ)*(a.beta:ℂ)*I)=1) :
    ∃ r : ℝ, 0 < r ∧ ∀ v : ℂ, ‖v‖ < r → (a.b/2)*‖v‖ ≤ ‖1-centralMeanZ a n v‖ := by
  have hq : -I*(a.b:ℂ) ≠ 0 := mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero)
    (Complex.ofReal_ne_zero.mpr (ne_of_gt a.b_pos))
  obtain ⟨r,hr,hb⟩ := analytic_simple_zero_lower (centralMeanZ_analytic a n)
    (centralMeanZ_zero a n hbeta) (centralMeanZ_hasDerivAt_zero a n hbeta) hq
  refine ⟨r,hr,?_⟩
  intro v hv
  simpa [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos a.b_pos] using hb v hv

end
end IsingBulk.First.Regular
