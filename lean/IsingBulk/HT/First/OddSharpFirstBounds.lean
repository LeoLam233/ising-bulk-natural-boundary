import IsingBulk.HT.First.RadialJetDescent
import IsingBulk.HT.First.OddFirstTheorem
import IsingBulk.HT.First.NegativeFirstTheorem
import IsingBulk.First.FormFactorAnalytic
import IsingBulk.First.CompactJetIntegral

/-! Sharp lower derivatives of the actual first-particle source. The proved
simple-pole asymptotic is integrated along the analytic radial source; no
logarithmic or bounded lower-jet estimate is added as an assumption. -/
namespace IsingBulk.HT.First
noncomputable section
open Complex Filter Set IsingBulk.First IsingBulk.Branch
open scoped Topology

 theorem sourceS_radial_im_pos {theta epsilon : ℝ}
    (htheta : 0 < Real.sin theta) (he : 0 < epsilon) :
    0 < (sourceS (radialParameter theta epsilon)).im := by
  have hden : 0 < 1+epsilon := by linarith
  have hsmall : epsilon^2/(1+epsilon)<epsilon := by
    apply (div_lt_iff₀ hden).2
    nlinarith
  have ht := (radial_trace_components theta epsilon hden.ne').2
  change (sourceS (radialParameter theta epsilon)).im =
    (2*epsilon-epsilon^2/(1+epsilon))*Real.sin theta at ht
  rw [ht]
  exact mul_pos (by linarith) htheta

 theorem upper_radial_jet_hasDerivAt (N j : ℕ) (hN : 0<N) {theta epsilon : ℝ}
    (htheta : 0<Real.sin theta) (he : 0<epsilon) :
    HasDerivAt (fun x : ℝ => (deriv^[j] (upperFormFactor N)) (radialParameter theta x))
      (exp ((theta:ℂ)*I)*(deriv^[j+1] (upperFormFactor N))
        (radialParameter theta epsilon)) epsilon := by
  have hAnalytic := upperFormFactor_analyticAt N hN (sourceS_radial_im_pos htheta he)
  have hf := (analytic_iterate_deriv_at hAnalytic j).differentiableAt.hasDerivAt
  simp only [radialParameter, ofReal_add, ofReal_one] at hf
  have hg : HasDerivAt (fun z : ℂ => (1+z)*exp ((theta:ℂ)*I))
      (exp ((theta:ℂ)*I)) (epsilon:ℂ) := by
    convert ((hasDerivAt_id (epsilon:ℂ)).const_add 1).mul_const (exp ((theta:ℂ)*I)) using 1 <;> simp
  have hh := (hf.comp (epsilon:ℂ) hg).comp_ofReal
  convert hh using 1
  · funext x
    simp only [radialParameter, ofReal_add, ofReal_one, Function.comp_def]
  · simp only [Function.iterate_succ', Function.comp_def, radialParameter, ofReal_add, ofReal_one]
    ring

/-- The upper source is analytic on the entire positive radial path. Its
proved top asymptotic therefore controls every lower jet sharply. -/
theorem upper_sharp_lower_jets_of_simple_pole (N : ℕ) (hN : 0<N)
    {theta : ℝ} (htheta : 0<Real.sin theta) {k : ℕ} (hk : 2≤k) {L : ℂ}
    (hTop : Asymptotics.IsLittleO (𝓝[>] (0:ℝ))
      (fun epsilon => (deriv^[k] (upperFormFactor N)) (radialParameter theta epsilon)-
        (epsilon:ℂ)⁻¹*L) (fun epsilon => (epsilon:ℂ)⁻¹)) :
    ∃ e : ℝ, 0<e ∧
      (∃ C : ℝ, 0<C ∧ ∀ epsilon : ℝ, 0<epsilon → epsilon≤e →
        ‖(deriv^[k-1] (upperFormFactor N)) (radialParameter theta epsilon)‖ ≤
          C*(1+|Real.log epsilon|)) ∧
      (∀ j : ℕ, j+1<k → ∃ C : ℝ, 0<C ∧ ∀ epsilon : ℝ,
        0<epsilon → epsilon≤e →
        ‖(deriv^[j] (upperFormFactor N)) (radialParameter theta epsilon)‖ ≤ C) := by
  obtain ⟨a,C,ha,hC,hb⟩ := inv_bound_of_simple_pole_asymptotic hTop
  have hv : ‖exp ((theta:ℂ)*I)‖=1 := by simp [Complex.norm_exp]
  have hh := sharp_lower_jets_of_top_inv_bound ha hC hk hv
    (fun j x hx => upper_radial_jet_hasDerivAt N j hN htheta hx.1) hb
  refine ⟨a,ha,?_,?_⟩
  · obtain ⟨B,hB,hBound⟩ := hh.1
    exact ⟨B,hB,fun epsilon he hea => hBound epsilon ⟨he,hea⟩⟩
  · intro j hj
    obtain ⟨B,hB,hBound⟩ := hh.2 j hj
    exact ⟨B,hB,fun epsilon he hea => hBound epsilon ⟨he,hea⟩⟩

/-- Transfer to the actual fixed-radius offsite source, with the radius
held fixed during every s derivative as in the manuscript. -/
theorem fixed_sharp_lower_jets_of_simple_pole (N : ℕ) (hN : 0<N)
    {theta : ℝ} (htheta : 0<Real.sin theta) {k : ℕ} (hk : 2≤k) {L : ℂ}
    (hTop : Asymptotics.IsLittleO (𝓝[>] (0:ℝ))
      (fun epsilon => (deriv^[k] (upperFormFactor N)) (radialParameter theta epsilon)-
        (epsilon:ℂ)⁻¹*L) (fun epsilon => (epsilon:ℂ)⁻¹)) :
    ∃ e : ℝ, 0<e ∧
      (∃ C : ℝ, 0<C ∧ ∀ epsilon : ℝ, 0<epsilon → epsilon≤e →
        ‖(deriv^[k-1] (doubleFormFactor N (sourceRadialPair theta epsilon).1))
          (sourceRadialPair theta epsilon).2‖ ≤ C*(1+|Real.log epsilon|)) ∧
      (∀ j : ℕ, j+1<k → ∃ C : ℝ, 0<C ∧ ∀ epsilon : ℝ,
        0<epsilon → epsilon≤e →
        ‖(deriv^[j] (doubleFormFactor N (sourceRadialPair theta epsilon).1))
          (sourceRadialPair theta epsilon).2‖ ≤ C) := by
  obtain ⟨e,he,hlog,hLow⟩ := upper_sharp_lower_jets_of_simple_pole N hN htheta hk hTop
  obtain ⟨d,hd,hRep⟩ := radial_upper_double_derivatives N hN htheta
  let a := min e (d/2)
  have ha : 0<a := lt_min he (by positivity)
  have hd' (epsilon : ℝ) (hea : epsilon≤a) : epsilon<d :=
    hea.trans_lt ((min_le_right _ _).trans_lt (by linarith))
  refine ⟨a,ha,?_,?_⟩
  · obtain ⟨C,hC,hBound⟩ := hlog
    refine ⟨C,hC,?_⟩
    intro epsilon heps hepa
    have hh := hBound epsilon heps (hepa.trans (min_le_left _ _))
    have hr := hRep epsilon heps (hd' epsilon hepa) (k-1)
    simp only [iteratedDeriv_eq_iterate] at hr
    rw [hr] at hh
    exact hh
  · intro j hj
    obtain ⟨C,hC,hBound⟩ := hLow j hj
    refine ⟨C,hC,?_⟩
    intro epsilon heps hepa
    have hh := hBound epsilon heps (hepa.trans (min_le_left _ _))
    have hr := hRep epsilon heps (hd' epsilon hepa) j
    simp only [iteratedDeriv_eq_iterate] at hr
    rw [hr] at hh
    exact hh

/-- The manuscript's sharp lower offsite derivatives, positive prime family. -/
theorem first_fixed_odd_source_sharp_lower_bounds {p : ℕ} (hp : p.Prime) (hp11 : 11≤p)
    {a b : ℤ} (ha : PrimeFamily.Admissible p a) (hb : PrimeFamily.Admissible p b)
    (hab : a≠b) :
    let k := derivativeOrder p
    let A := selectedOrderedChart ha hb
    ∃ e : ℝ, 0<e ∧
      (∃ C : ℝ, 0<C ∧ ∀ epsilon : ℝ, 0<epsilon → epsilon≤e →
        ‖(deriv^[k-1] (doubleFormFactor p (sourceRadialPair A.theta epsilon).1))
          (sourceRadialPair A.theta epsilon).2‖ ≤ C*(1+|Real.log epsilon|)) ∧
      (∀ j : ℕ, j+1<k → ∃ C : ℝ, 0<C ∧ ∀ epsilon : ℝ,
        0<epsilon → epsilon≤e →
        ‖(deriv^[j] (doubleFormFactor p (sourceRadialPair A.theta epsilon).1))
          (sourceRadialPair A.theta epsilon).2‖ ≤ C) := by
  dsimp only
  have hN : p-1+1=p := by omega
  have hTop := (first_upper_odd_asymptotic hp hp11 ha hb hab).2
  simp only [hN, iteratedDeriv_eq_iterate] at hTop
  have hk : 2≤derivativeOrder p := by
    have h := odd_square_order (hp.odd_of_ne_two (by omega))
    nlinarith
  exact fixed_sharp_lower_jets_of_simple_pole p hp.pos
    (selectedOrderedChart ha hb).sin_theta_pos hk hTop

namespace Regular

/-- The same sharp bounds at the original negative selected point. -/
theorem negative_first_fixed_odd_source_sharp_lower_bounds {p : ℕ} (hp : p.Prime) (hp11 : 11≤p)
    {a b : ℤ} (ha : NegativeAdmissible p a) (hb : NegativeAdmissible p b) (hab : a≠b) :
    let k := derivativeOrder p
    let A := negativeSelectedRegularChart ha hb
    ∃ e : ℝ, 0<e ∧
      (∃ C : ℝ, 0<C ∧ ∀ epsilon : ℝ, 0<epsilon → epsilon≤e →
        ‖(deriv^[k-1] (doubleFormFactor p (sourceRadialPair A.theta epsilon).1))
          (sourceRadialPair A.theta epsilon).2‖ ≤ C*(1+|Real.log epsilon|)) ∧
      (∀ j : ℕ, j+1<k → ∃ C : ℝ, 0<C ∧ ∀ epsilon : ℝ,
        0<epsilon → epsilon≤e →
        ‖(deriv^[j] (doubleFormFactor p (sourceRadialPair A.theta epsilon).1))
          (sourceRadialPair A.theta epsilon).2‖ ≤ C) := by
  dsimp only
  have hN : p-1+1=p := by omega
  have hTop := (negative_first_upper_odd_asymptotic hp hp11 ha hb hab).2
  simp only [hN, iteratedDeriv_eq_iterate] at hTop
  have hk : 2≤derivativeOrder p := by
    have h := odd_square_order (hp.odd_of_ne_two (by omega))
    nlinarith
  exact fixed_sharp_lower_jets_of_simple_pole p hp.pos
    (negativeSelectedRegularChart ha hb).sin_theta_pos hk hTop

end Regular
end
end IsingBulk.HT.First
