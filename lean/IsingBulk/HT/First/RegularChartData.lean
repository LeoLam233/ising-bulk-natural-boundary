import IsingBulk.First.RegularChartData
import IsingBulk.HT.First.NegativePrimeFamily

/-! Actual quadrant-II selected data for the shared regular chart. -/
namespace IsingBulk.HT.First
noncomputable section
open IsingBulk.First

abbrev RegularChartData := IsingBulk.First.RegularChartData
abbrev regularChartOfAcute (a : OrderedChartData) : RegularChartData := a.toRegular

@[simp] theorem regularChartOfAcute_b (a : OrderedChartData) : (regularChartOfAcute a).b=a.b := rfl
@[simp] theorem regularChartOfAcute_d (a : OrderedChartData) : (regularChartOfAcute a).d=a.d := rfl
@[simp] theorem regularChartOfAcute_Q (a : OrderedChartData) (N : ℕ) : (regularChartOfAcute a).Q N=a.Q N := rfl
@[simp] theorem regularChartOfAcute_K (a : OrderedChartData) (N : ℕ) : (regularChartOfAcute a).K N=a.K N := rfl
@[simp] theorem regularChartOfAcute_Ds (a : OrderedChartData) (N : ℕ) : (regularChartOfAcute a).Ds N=a.Ds N := rfl

def negativeSelectedRegularChart {p : ℕ} {a b : ℤ}
    (ha : NegativeAdmissible p a) (hb : NegativeAdmissible p b) : RegularChartData where
  alpha := PrimeFamily.angle p a
  beta := PrimeFamily.angle p b
  theta := Real.arccos (PrimeFamily.cosineAverage p a b)
  alpha_pos := by linarith [Real.pi_pos,ha.1]
  alpha_lt_pi := ha.2
  beta_pos := by linarith [Real.pi_pos,hb.1]
  beta_lt_pi := hb.2
  theta_pos := Real.arccos_pos.mpr (by linarith [(negative_cosineAverage_bounds ha hb).2])
  theta_lt_pi := Real.arccos_lt_pi.mpr (negative_cosineAverage_bounds ha hb).1
  angle_relation := by
    have hc := negative_cosineAverage_bounds ha hb
    rw [Real.cos_arccos hc.1.le (by linarith : PrimeFamily.cosineAverage p a b≤1)]
    unfold PrimeFamily.cosineAverage
    ring
  level_ne_zero := by
    have hc := (negative_cosineAverage_bounds ha hb).2
    unfold PrimeFamily.cosineAverage at hc
    linarith

theorem negativeSelectedRegularChart_d_neg {p : ℕ} {a b : ℤ}
    (ha : NegativeAdmissible p a) (hb : NegativeAdmissible p b) :
    (negativeSelectedRegularChart ha hb).d<0 := by
  let A := negativeSelectedRegularChart ha hb
  have hlevel : Real.cos A.alpha+Real.cos A.beta<0 := by
    have hc := (negative_cosineAverage_bounds ha hb).2
    change (Real.cos A.alpha+Real.cos A.beta)/2<0 at hc
    linarith
  exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hlevel (sub_pos.mpr A.cosine_product_lt_one))
    (mul_pos (by norm_num) (pow_pos A.sin_beta_pos 3))

end
end IsingBulk.HT.First
