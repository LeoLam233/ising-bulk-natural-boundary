import IsingBulk.HT.First.NegativeLowerOrderBounds
import IsingBulk.HT.First.NegativeOnsiteBounds
import IsingBulk.First.NormalizationDerivatives

/-! Actual lower-particle full-site regularity at a negative selected prime
point. This combines proved onsite and offsite estimates at one permitted
radius, held fixed under each source derivative. -/
namespace IsingBulk.HT.First
noncomputable section
open Complex Filter IsingBulk.First
open scoped Topology

theorem negative_selected_lower_full_orders_fixed_radius_bounded {p : ℕ} {a b : ℤ}
    (hp : p.Prime) (hp11 : 11 ≤ p)
    (ha : NegativeAdmissible p a) (hb : NegativeAdmissible p b) :
    let theta := Real.arccos (PrimeFamily.cosineAverage p a b)
    ∀ N : ℕ, 0 < N → N < p →
      ∃ e : ℝ, 0 < e ∧ ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ epsilon : ℝ,
        0 < epsilon → epsilon ≤ e →
        ‖(deriv^[j] (standardFormFactor N (sourceRadialPair theta epsilon).1))
          (sourceRadialPair theta epsilon).2‖ ≤ C := by
  dsimp only
  let theta := Real.arccos (PrimeFamily.cosineAverage p a b)
  have hc := negative_cosineAverage_bounds ha hb
  have ht0 : 0 < theta := Real.arccos_pos.mpr (by linarith)
  have htpi : theta < Real.pi := Real.arccos_lt_pi.mpr hc.1
  have htheta := Real.sin_pos_of_pos_of_lt_pi ht0 htpi
  have hS : sourceS (exp ((theta:ℂ)*I)) = ((2*PrimeFamily.cosineAverage p a b:ℝ):ℂ) := by
    simpa only [sourceS,PrimeFamily.selectedPoint,theta,Complex.ofReal_mul,Complex.ofReal_ofNat]
      using negative_selectedPoint_relation ha hb
  intro N hN hNp
  obtain ⟨eT,heT,hT⟩ := negative_selected_lower_orders_fixed_radius_bounded hp hp11 ha hb N hN hNp
  obtain ⟨eO,heO,hO⟩ := negative_onsite_global_radial_bound hN
    (2*PrimeFamily.cosineAverage p a b) (by constructor <;> linarith) theta htheta hS
  obtain ⟨d,hd,_,hm⟩ := radial_disk_source_trace_margin htheta
  let e := min eT (min eO (d/2))
  have he : 0 < e := lt_min heT (lt_min heO (by positivity))
  refine ⟨e,he,?_⟩
  intro j
  obtain ⟨CT,hCT,hbT⟩ := hT j
  obtain ⟨CO,hCO,hbO⟩ := hO j
  refine ⟨CO+2*CT,by positivity,?_⟩
  intro epsilon heps hepsE
  have heT' := hepsE.trans (min_le_left _ _)
  have heO' := hepsE.trans ((min_le_right _ _).trans (min_le_left _ _))
  have heD : epsilon < d := hepsE.trans_lt
    (((min_le_right _ _).trans (min_le_right _ _)).trans_lt (by linarith))
  have hmargin := (hm epsilon heps heD (IsingBulk.Branch.radialParameter theta epsilon)
    (by simpa using mul_pos (show 0 < Real.sin theta/16 by positivity) heps)).2
  have hr : 0 < (sourceRadialPair theta epsilon).1 := Real.exp_pos _
  have hr1 : (sourceRadialPair theta epsilon).1 < 1 := by
    change Real.exp (-(Real.sin theta/4)*epsilon) < 1
    rw [Real.exp_lt_one_iff]
    exact mul_neg_of_neg_of_pos (by linarith) heps
  have hEq := standardFormFactor_iteratedDeriv_eq N hN j hr hr1 hmargin
  simp only [iteratedDeriv_eq_iterate] at hEq
  change ‖(deriv^[j] (standardFormFactor N (sourceRadialPair theta epsilon).1))
    (IsingBulk.Branch.radialParameter theta epsilon)‖ ≤ CO + 2 * CT
  rw [hEq]
  calc
    _ ≤ ‖(deriv^[j] (onsiteFormFactor N (sourceRadialPair theta epsilon).1))
          (sourceRadialPair theta epsilon).2‖+
        2*‖(deriv^[j] (doubleFormFactor N (sourceRadialPair theta epsilon).1))
          (sourceRadialPair theta epsilon).2‖ := by
      simpa only [norm_mul,norm_ofNat,sourceRadialPair] using norm_add_le
        ((deriv^[j] (onsiteFormFactor N (sourceRadialPair theta epsilon).1))
          (sourceRadialPair theta epsilon).2)
        (2*(deriv^[j] (doubleFormFactor N (sourceRadialPair theta epsilon).1))
          (sourceRadialPair theta epsilon).2)
    _ ≤ CO+2*CT := add_le_add (hbO epsilon heps heO')
      (mul_le_mul_of_nonneg_left (hbT epsilon heps heT') (by norm_num))

end
end IsingBulk.HT.First
