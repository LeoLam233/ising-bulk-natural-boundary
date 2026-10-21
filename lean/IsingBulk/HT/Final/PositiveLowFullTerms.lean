import IsingBulk.HT.Final.UpperFullDerivatives
import IsingBulk.HT.Final.RadialObstruction
import IsingBulk.HT.First.PrimeOrder
import IsingBulk.HT.First.OddLimitTransfer
import IsingBulk.First.OnsiteGlobalBound

/-! Genuine fixed-particle lower-order estimates for the full HT coefficients.
Only finitely many particle numbers occur here; the infinite tail is separate. -/
namespace IsingBulk.HT.Final
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.HT.First Filter
open scoped Topology BigOperators

theorem selected_lower_full_coefficient_bounded {p : ℕ} (hp : p.Prime)
    (hp11 : 11 ≤ p) {a b : ℤ} (ha : PrimeFamily.Admissible p a)
    (hb : PrimeFamily.Admissible p b) {N : ℕ} (hN : 0 < N) (hOdd : Odd N)
    (hNp : N < p) (j : ℕ) :
    ∃ e C : ℝ, 0 < e ∧ ∀ eps : ℝ, 0 < eps → eps ≤ e →
      ‖iteratedDeriv j (upperFullCoefficient N)
        (radialParameter (selectedOrderedChart ha hb).theta eps)‖ ≤ C := by
  let A := selectedOrderedChart ha hb
  have hlevel := PrimeFamily.cosineAverage_bounds ha hb
  have hS : sourceS (Complex.exp ((A.theta:ℂ)*Complex.I)) =
      ((2*PrimeFamily.cosineAverage p a b:ℝ):ℂ) := by
    simpa only [sourceS,PrimeFamily.selectedPoint,selectedOrderedChart,A,
      Complex.ofReal_mul,Complex.ofReal_ofNat] using PrimeFamily.selectedPoint_relation ha hb
  obtain ⟨eO,heO,hO⟩ := onsite_global_radial_bound hN
    (2*PrimeFamily.cosineAverage p a b) (by constructor <;> linarith)
    A.theta A.sin_theta_pos hS
  obtain ⟨CO,_hCO,hO⟩ := hO j
  obtain ⟨eD,CD,heD,_hCD,hD⟩ :=
    selected_lower_odd_orders_fixed_radius_bounded hp hp11 ha hb N hN hOdd hNp j
  obtain ⟨d,hd,_,hMargin⟩ := radial_disk_source_trace_margin A.sin_theta_pos
  refine ⟨min eO (min (eD/2) (d/2)),CO+2*CD,
    lt_min heO (lt_min (by positivity) (by positivity)),?_⟩
  intro eps he heCap
  have heO' : eps ≤ eO := heCap.trans (min_le_left _ _)
  have heD' : eps < eD :=
    (heCap.trans ((min_le_right _ _).trans (min_le_left _ _))).trans_lt (by linarith)
  have hed : eps < d :=
    (heCap.trans ((min_le_right _ _).trans (min_le_right _ _))).trans_lt (by linarith)
  have hr : 0 < (sourceRadialPair A.theta eps).1 := Real.exp_pos _
  have hr1 : (sourceRadialPair A.theta eps).1 < 1 := by
    change Real.exp (-(Real.sin A.theta/4)*eps) < 1
    rw [Real.exp_lt_one_iff]
    nlinarith [mul_pos A.sin_theta_pos he]
  have hwidth : 0 < Real.sin A.theta / 16 * eps :=
    mul_pos (div_pos A.sin_theta_pos (by norm_num)) he
  have hm := (hMargin eps he hed (radialParameter A.theta eps)
    (by simpa using hwidth)).2
  rw [upperFullCoefficient_iteratedDeriv_fixed_radius N hN j hr hr1 hm,
    standardFormFactor_iteratedDeriv_eq N hN j hr hr1 hm]
  have hOn := hO eps he heO'
  have hDn := hD eps he heD'
  have hbnd := norm_add_le
    (iteratedDeriv j (onsiteFormFactor N (sourceRadialPair A.theta eps).1)
      (radialParameter A.theta eps))
    (2*iteratedDeriv j (doubleFormFactor N (sourceRadialPair A.theta eps).1)
      (radialParameter A.theta eps))
  simp only [norm_mul,Complex.norm_ofNat,iteratedDeriv_eq_iterate,sourceRadialPair] at hbnd hOn hDn ⊢
  linarith

theorem selected_lower_full_coefficient_epsilon_zero {p : ℕ} (hp : p.Prime)
    (hp11 : 11 ≤ p) {a b : ℤ} (ha : PrimeFamily.Admissible p a)
    (hb : PrimeFamily.Admissible p b) {N : ℕ} (hN : 0 < N) (hOdd : Odd N)
    (hNp : N < p) (j : ℕ) :
    Tendsto (fun eps : ℝ => eps • iteratedDeriv j (upperFullCoefficient N)
      (radialParameter (selectedOrderedChart ha hb).theta eps)) (𝓝[>] 0) (𝓝 (0:ℂ)) := by
  obtain ⟨e,C,he,hbnd⟩ := selected_lower_full_coefficient_bounded hp hp11 ha hb hN hOdd hNp j
  apply epsilon_limit_of_isLittleO (L := 0)
  simpa only [mul_zero,sub_zero] using bounded_radial_term_epsilon_isLittleO he hbnd

end
end IsingBulk.HT.Final
