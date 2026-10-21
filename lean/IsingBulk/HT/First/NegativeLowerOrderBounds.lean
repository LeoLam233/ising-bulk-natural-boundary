import IsingBulk.HT.First.NegativeNonNickelGeometry
import IsingBulk.First.NonNickelRadialBounds

/-! Actual fixed-radius offsite lower-order bounds on the negative-cosine
prime family, obtained from its proved negative active-vector classification
and the unchanged LT finite-cover, nonstationary and IBP infrastructure. -/
namespace IsingBulk.HT.First
noncomputable section
open Complex Set Filter IsingBulk.First
open scoped Topology ContDiff

theorem negative_selected_lower_orders_fixed_radius_bounded {p : ℕ} {a b : ℤ}
    (hp : p.Prime) (hp11 : 11 ≤ p)
    (ha : NegativeAdmissible p a) (hb : NegativeAdmissible p b) :
    let theta := Real.arccos (PrimeFamily.cosineAverage p a b)
    ∀ N : ℕ, 0 < N → N < p →
      ∃ e : ℝ, 0 < e ∧ ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ epsilon : ℝ,
        0 < epsilon → epsilon ≤ e →
        ‖(deriv^[j] (doubleFormFactor N (sourceRadialPair theta epsilon).1))
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
  have hn := (negative_first_prime_Nickel_order hp hp11 ha hb).2.2 N hN hNp
  have hsep (u : DoubleAngularVector N)
      (_hu : u ∈ tsupport (fun _ : DoubleAngularVector N => (1:ℝ))) :
      ActiveSourceSeparated (angleTuple 1 u.1) (angleTuple 1 u.2)
        (2*PrimeFamily.cosineAverage p a b) :=
    negative_nonNickel_active_separated hN hp hp11 ha hb
      (fun _ => anglePoint_norm (by norm_num) _)
      (fun _ => anglePoint_norm (by norm_num) _) hn
  have hper : DoubleCoordinatePeriodic (fun _ : DoubleAngularVector N => (1:ℝ)) := by
    intro u i
    exact ⟨rfl,rfl⟩
  obtain ⟨e,he,hB⟩ := source_complement_global_bound hN
    (2*PrimeFamily.cosineAverage p a b) theta htheta hS (fun _ => 1) contDiff_const hper hsep
  obtain ⟨d,hd,_,hm⟩ := radial_disk_source_trace_margin htheta
  refine ⟨min e (d/2),lt_min he (by positivity),?_⟩
  intro j
  obtain ⟨C,hC,hbnd⟩ := hB j
  refine ⟨C,hC,?_⟩
  intro epsilon heps hepsSmall
  have hepsE := hepsSmall.trans (min_le_left e (d/2))
  have hepsD : epsilon < d := hepsSmall.trans_lt ((min_le_right e (d/2)).trans_lt (by linarith))
  have hmargin := (hm epsilon heps hepsD (IsingBulk.Branch.radialParameter theta epsilon)
    (by simpa using mul_pos (show 0 < Real.sin theta/16 by positivity) heps)).2
  have hr : 0 < (sourceRadialPair theta epsilon).1 := Real.exp_pos _
  have hr1 : (sourceRadialPair theta epsilon).1 < 1 := by
    change Real.exp (-(Real.sin theta/4)*epsilon) < 1
    rw [Real.exp_lt_one_iff]
    exact mul_neg_of_neg_of_pos (by linarith) heps
  rw [← iteratedDeriv_eq_iterate,
    doubleFormFactor_iteratedDeriv_localized_one N hN j hr hr1
      (s := (sourceRadialPair theta epsilon).2) hmargin,
    iteratedDeriv_eq_iterate]
  exact hbnd epsilon heps hepsE

end
end IsingBulk.HT.First
