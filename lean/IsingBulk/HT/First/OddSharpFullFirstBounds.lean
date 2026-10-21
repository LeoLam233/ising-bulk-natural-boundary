import IsingBulk.HT.First.OddSharpFirstBounds

/-! Sharp lower derivatives of the literal full-site source C = f + 2T.
The onsite term is bounded by the proved source theorem, while the offsite
term is controlled by analytic radial descent from its first singularity. -/
namespace IsingBulk.HT.First
noncomputable section
open Complex Filter Set IsingBulk.First IsingBulk.Branch
open scoped Topology

/-- The fixed-radius normalization identity holds on one common radial interval
for every derivative order. -/
theorem radial_standard_jet_eq (N : ℕ) (hN : 0 < N) {theta : ℝ}
    (htheta : 0 < Real.sin theta) :
    ∃ d : ℝ, 0 < d ∧ ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ d → ∀ j : ℕ,
      (deriv^[j] (standardFormFactor N (sourceRadialPair theta epsilon).1))
          (sourceRadialPair theta epsilon).2 =
        (deriv^[j] (onsiteFormFactor N (sourceRadialPair theta epsilon).1))
          (sourceRadialPair theta epsilon).2 +
        2*(deriv^[j] (doubleFormFactor N (sourceRadialPair theta epsilon).1))
          (sourceRadialPair theta epsilon).2 := by
  obtain ⟨d,hd,_,hMargin⟩ := radial_disk_source_trace_margin htheta
  refine ⟨d/2,by positivity,?_⟩
  intro epsilon heps heD j
  have heD' : epsilon < d := heD.trans_lt (by linarith)
  have hr : 0 < (sourceRadialPair theta epsilon).1 := Real.exp_pos _
  have hr1 : (sourceRadialPair theta epsilon).1 < 1 := by
    change Real.exp (-(Real.sin theta/4)*epsilon) < 1
    rw [Real.exp_lt_one_iff]
    nlinarith [mul_pos htheta heps]
  have hm := (hMargin epsilon heps heD' (radialParameter theta epsilon)
    (by simpa using mul_pos (div_pos htheta (by norm_num) : 0 < Real.sin theta/16) heps)).2
  simpa only [iteratedDeriv_eq_iterate,sourceRadialPair] using
    standardFormFactor_iteratedDeriv_eq N hN j hr hr1 hm

/-- Source-preserving assembly of sharp lower estimates. The two premises
are independently proved for both selected-point families below. -/
theorem standard_sharp_lower_bounds_of_onsite_bound (N : ℕ) (hN : 0 < N)
    {theta : ℝ} (htheta : 0 < Real.sin theta) (k : ℕ)
    (hOff : ∃ e : ℝ, 0 < e ∧
      (∃ C : ℝ, 0 < C ∧ ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ e →
        ‖(deriv^[k-1] (doubleFormFactor N (sourceRadialPair theta epsilon).1))
          (sourceRadialPair theta epsilon).2‖ ≤ C*(1+|Real.log epsilon|)) ∧
      (∀ j : ℕ, j+1 < k → ∃ C : ℝ, 0 < C ∧ ∀ epsilon : ℝ,
        0 < epsilon → epsilon ≤ e →
        ‖(deriv^[j] (doubleFormFactor N (sourceRadialPair theta epsilon).1))
          (sourceRadialPair theta epsilon).2‖ ≤ C))
    (hOn : ∃ e : ℝ, 0 < e ∧ ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ e →
        ‖(deriv^[j] (onsiteFormFactor N (sourceRadialPair theta epsilon).1))
          (sourceRadialPair theta epsilon).2‖ ≤ C) :
    ∃ e : ℝ, 0 < e ∧
      (∃ C : ℝ, 0 < C ∧ ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ e →
        ‖(deriv^[k-1] (standardFormFactor N (sourceRadialPair theta epsilon).1))
          (sourceRadialPair theta epsilon).2‖ ≤ C*(1+|Real.log epsilon|)) ∧
      (∀ j : ℕ, j+1 < k → ∃ C : ℝ, 0 < C ∧ ∀ epsilon : ℝ,
        0 < epsilon → epsilon ≤ e →
        ‖(deriv^[j] (standardFormFactor N (sourceRadialPair theta epsilon).1))
          (sourceRadialPair theta epsilon).2‖ ≤ C) := by
  obtain ⟨e₁,he₁,hLog,hLow⟩ := hOff
  obtain ⟨e₂,he₂,hOn⟩ := hOn
  obtain ⟨d,hd,hEq⟩ := radial_standard_jet_eq N hN htheta
  let e := min e₁ (min e₂ d)
  have he : 0 < e := lt_min he₁ (lt_min he₂ hd)
  have hle₁ {epsilon : ℝ} (h : epsilon ≤ e) : epsilon ≤ e₁ :=
    h.trans (min_le_left _ _)
  have hle₂ {epsilon : ℝ} (h : epsilon ≤ e) : epsilon ≤ e₂ :=
    h.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hleD {epsilon : ℝ} (h : epsilon ≤ e) : epsilon ≤ d :=
    h.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hnorm (j : ℕ) {epsilon : ℝ} (hpos : 0 < epsilon) (h : epsilon ≤ e) :
      ‖(deriv^[j] (standardFormFactor N (sourceRadialPair theta epsilon).1))
          (sourceRadialPair theta epsilon).2‖ ≤
        ‖(deriv^[j] (onsiteFormFactor N (sourceRadialPair theta epsilon).1))
          (sourceRadialPair theta epsilon).2‖ +
        2*‖(deriv^[j] (doubleFormFactor N (sourceRadialPair theta epsilon).1))
          (sourceRadialPair theta epsilon).2‖ := by
    rw [hEq epsilon hpos (hleD h) j]
    calc
      _ ≤ _ := norm_add_le _ _
      _ = _ := by rw [norm_mul]; norm_num
  refine ⟨e,he,?_,?_⟩
  · obtain ⟨C,hC,hBound⟩ := hLog
    obtain ⟨D,hD,hOnBound⟩ := hOn (k-1)
    refine ⟨D+2*C,by positivity,?_⟩
    intro epsilon hpos h
    have hb := (hnorm (k-1) hpos h).trans
      (add_le_add (hOnBound epsilon hpos (hle₂ h))
        (mul_le_mul_of_nonneg_left (hBound epsilon hpos (hle₁ h)) (by norm_num)))
    nlinarith [mul_nonneg hD (abs_nonneg (Real.log epsilon))]
  · intro j hj
    obtain ⟨C,hC,hBound⟩ := hLow j hj
    obtain ⟨D,hD,hOnBound⟩ := hOn j
    refine ⟨D+2*C,by positivity,?_⟩
    intro epsilon hpos h
    exact (hnorm j hpos h).trans
      (add_le_add (hOnBound epsilon hpos (hle₂ h))
        (mul_le_mul_of_nonneg_left (hBound epsilon hpos (hle₁ h)) (by norm_num)))

/-- Sharp manuscript lower estimates for the positive-family full-site source.
In particular, the critical lower derivative is logarithmic, not merely
little-o of the inverse radial distance. -/
theorem first_standard_odd_source_sharp_lower_bounds {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p)
    {a b : ℤ} (ha : PrimeFamily.Admissible p a) (hb : PrimeFamily.Admissible p b)
    (hab : a ≠ b) :
    let k := derivativeOrder p
    let A := selectedOrderedChart ha hb
    ∃ e : ℝ, 0 < e ∧
      (∃ C : ℝ, 0 < C ∧ ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ e →
        ‖(deriv^[k-1] (standardFormFactor p (sourceRadialPair A.theta epsilon).1))
          (sourceRadialPair A.theta epsilon).2‖ ≤ C*(1+|Real.log epsilon|)) ∧
      (∀ j : ℕ, j+1 < k → ∃ C : ℝ, 0 < C ∧ ∀ epsilon : ℝ,
        0 < epsilon → epsilon ≤ e →
        ‖(deriv^[j] (standardFormFactor p (sourceRadialPair A.theta epsilon).1))
          (sourceRadialPair A.theta epsilon).2‖ ≤ C) := by
  dsimp only
  let A := selectedOrderedChart ha hb
  have hlevel := PrimeFamily.cosineAverage_bounds ha hb
  have hS : sourceS (exp ((A.theta:ℂ)*I)) = ((2*PrimeFamily.cosineAverage p a b:ℝ):ℂ) := by
    simpa only [sourceS,PrimeFamily.selectedPoint,selectedOrderedChart,A,Complex.ofReal_mul,
      Complex.ofReal_ofNat] using PrimeFamily.selectedPoint_relation ha hb
  exact standard_sharp_lower_bounds_of_onsite_bound p hp.pos A.sin_theta_pos (derivativeOrder p)
    (first_fixed_odd_source_sharp_lower_bounds hp hp11 ha hb hab)
    (onsite_global_radial_bound hp.pos (2*PrimeFamily.cosineAverage p a b)
      (by constructor <;> linarith) A.theta A.sin_theta_pos hS)

namespace Regular

/-- Sharp full-site lower estimates at the literal negative selected point.
The original angle and fixed-radius source are retained throughout. -/
theorem negative_first_standard_odd_source_sharp_lower_bounds {p : ℕ} (hp : p.Prime)
    (hp11 : 11 ≤ p) {a b : ℤ}
    (ha : NegativeAdmissible p a) (hb : NegativeAdmissible p b) (hab : a ≠ b) :
    let k := derivativeOrder p
    let A := negativeSelectedRegularChart ha hb
    ∃ e : ℝ, 0 < e ∧
      (∃ C : ℝ, 0 < C ∧ ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ e →
        ‖(deriv^[k-1] (standardFormFactor p (sourceRadialPair A.theta epsilon).1))
          (sourceRadialPair A.theta epsilon).2‖ ≤ C*(1+|Real.log epsilon|)) ∧
      (∀ j : ℕ, j+1 < k → ∃ C : ℝ, 0 < C ∧ ∀ epsilon : ℝ,
        0 < epsilon → epsilon ≤ e →
        ‖(deriv^[j] (standardFormFactor p (sourceRadialPair A.theta epsilon).1))
          (sourceRadialPair A.theta epsilon).2‖ ≤ C) := by
  dsimp only
  let A := negativeSelectedRegularChart ha hb
  have hlevel := negative_cosineAverage_bounds ha hb
  have hS : sourceS (exp ((A.theta:ℂ)*I)) = ((2*PrimeFamily.cosineAverage p a b:ℝ):ℂ) := by
    simpa only [sourceS,PrimeFamily.selectedPoint,negativeSelectedRegularChart,A,Complex.ofReal_mul,
      Complex.ofReal_ofNat] using negative_selectedPoint_relation ha hb
  exact standard_sharp_lower_bounds_of_onsite_bound p hp.pos A.sin_theta_pos (derivativeOrder p)
    (negative_first_fixed_odd_source_sharp_lower_bounds hp hp11 ha hb hab)
    (negative_onsite_global_radial_bound hp.pos (2*PrimeFamily.cosineAverage p a b)
      (by constructor <;> linarith) A.theta A.sin_theta_pos hS)

end Regular
end
end IsingBulk.HT.First
