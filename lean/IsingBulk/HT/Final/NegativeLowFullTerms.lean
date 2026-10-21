import IsingBulk.HT.Final.UpperFullDerivatives
import IsingBulk.HT.Final.RadialObstruction
import IsingBulk.HT.First.NegativeFullLowerOrderBounds
import IsingBulk.HT.First.RegularChartData
import IsingBulk.HT.First.OddLimitTransfer

/-! Actual lower-particle full-site bounds at the original negative integer-angle
family. The negative non-Nickel geometry is proved in NegativeLowerOrderBounds;
no reflected-positive arithmetic family is substituted. -/
namespace IsingBulk.HT.Final
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.HT.First Filter
open scoped Topology BigOperators

theorem negative_lower_full_coefficient_bounded {p : ℕ} (hp : p.Prime)
    (hp11 : 11 ≤ p) {a b : ℤ} (ha : NegativeAdmissible p a)
    (hb : NegativeAdmissible p b) {N : ℕ} (hN : 0 < N) (hNp : N < p) (j : ℕ) :
    ∃ e C : ℝ, 0 < e ∧ ∀ eps : ℝ, 0 < eps → eps ≤ e →
      ‖iteratedDeriv j (upperFullCoefficient N)
        (radialParameter (negativeSelectedRegularChart ha hb).theta eps)‖ ≤ C := by
  let A := negativeSelectedRegularChart ha hb
  obtain ⟨e,he,hB⟩ :=
    negative_selected_lower_full_orders_fixed_radius_bounded hp hp11 ha hb N hN hNp
  obtain ⟨C,_hC,hC⟩ := hB j
  obtain ⟨d,hd,hRep⟩ := radial_upper_full_derivatives N hN A.sin_theta_pos
  refine ⟨min e (d/2),C,lt_min he (by positivity),?_⟩
  intro eps heps heCap
  rw [hRep eps heps
    ((heCap.trans (min_le_right _ _)).trans_lt (by linarith)) j]
  exact hC eps heps (heCap.trans (min_le_left _ _))

theorem negative_lower_full_sum_littleO {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p)
    {a b : ℤ} (ha : NegativeAdmissible p a) (hb : NegativeAdmissible p b) (j : ℕ) :
    Asymptotics.IsLittleO (𝓝[>] (0:ℝ))
      (fun eps => ∑ n ∈ Finset.range (p/2), iteratedDeriv j (upperFullCoefficient (2*n+1))
        (radialParameter (negativeSelectedRegularChart ha hb).theta eps))
      (fun eps : ℝ => (eps:ℂ)⁻¹) := by
  apply Asymptotics.IsLittleO.fun_sum
  intro n hn
  have hnp : 2*n+1 < p := by have := Finset.mem_range.mp hn; omega
  obtain ⟨e,C,he,hbnd⟩ := negative_lower_full_coefficient_bounded hp hp11 ha hb
    (by omega : 0 < 2*n+1) hnp j
  exact bounded_radial_term_epsilon_isLittleO he hbnd

end
end IsingBulk.HT.Final
