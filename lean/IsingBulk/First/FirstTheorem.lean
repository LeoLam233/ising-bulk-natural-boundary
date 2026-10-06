import IsingBulk.First.FirstUpperAsymptotic
import IsingBulk.First.LowerOrderFixedRadius
import IsingBulk.First.LowerOrderFiniteWindow

/-! FIRST, in the literal source fixed-radius T_N representation. The only
external premise is the named published full-site fixed-order theorem, used
solely for lower even N via the proved onsite subtraction and radius transfer. -/
namespace IsingBulk.First
noncomputable section
open Complex Filter IsingBulk.Branch
open scoped Topology

theorem radial_upper_double_derivatives (N : ℕ) (hN : 0 < N) {theta : ℝ}
    (htheta : 0 < Real.sin theta) :
    ∃ e : ℝ, 0 < e ∧ ∀ epsilon : ℝ, 0 < epsilon → epsilon < e → ∀ j : ℕ,
      iteratedDeriv j (upperFormFactor N) (radialParameter theta epsilon) =
        (deriv^[j] (doubleFormFactor N (sourceRadialPair theta epsilon).1))
          (sourceRadialPair theta epsilon).2 := by
  obtain ⟨e,he,_,hMargin⟩ := radial_disk_source_trace_margin htheta
  refine ⟨e,he,?_⟩
  intro epsilon hp hsmall j
  have hr : 0 < (sourceRadialPair theta epsilon).1 := Real.exp_pos _
  have hr1 : (sourceRadialPair theta epsilon).1 < 1 := by
    change Real.exp (-(Real.sin theta/4)*epsilon) < 1
    rw [Real.exp_lt_one_iff]
    nlinarith [mul_pos htheta hp]
  have hm := (hMargin epsilon hp hsmall (radialParameter theta epsilon)
    (by simpa using mul_pos (div_pos htheta (by norm_num) : 0 < Real.sin theta/16) hp)).2
  simpa only [iteratedDeriv_eq_iterate,sourceRadialPair] using
    upperFormFactor_iteratedDeriv_fixed_radius N hN j hr hr1 hm

/-- The complete first-particle-order asymptotic and every lower derivative
bound use the actual fixed-radius offsite contour, not the full-site coefficient. -/
theorem first_fixed_source_asymptotic {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p) {a b : ℤ}
    (ha : PrimeFamily.Admissible p a) (hb : PrimeFamily.Admissible p b) (hab : a ≠ b) :
    let k := (2*p)^2/2-1
    let A := selectedOrderedChart ha hb
    let L := localLeadingCoefficient A (2*p-1) k
    L ≠ 0 ∧
      Asymptotics.IsLittleO (𝓝[>] (0:ℝ))
        (fun epsilon => (deriv^[k] (doubleFormFactor (2*p) (sourceRadialPair A.theta epsilon).1))
          (sourceRadialPair A.theta epsilon).2 - (Real.sqrt epsilon:ℂ)⁻¹*(2*L))
        (fun epsilon => (Real.sqrt epsilon:ℂ)⁻¹) ∧
      ∃ e : ℝ, 0 < e ∧ ∀ j : ℕ, j < k → ∃ C : ℝ, 0 ≤ C ∧ ∀ epsilon : ℝ,
        0 < epsilon → epsilon < e →
        ‖(deriv^[j] (doubleFormFactor (2*p) (sourceRadialPair A.theta epsilon).1))
          (sourceRadialPair A.theta epsilon).2‖ ≤ C := by
  dsimp only
  have hN : 2*p-1+1=2*p := by have := hp.pos; omega
  obtain ⟨hL,hTop,e,he,hLow⟩ := first_upper_asymptotic hp hp11 ha hb hab
  simp only [hN] at hL hTop hLow
  obtain ⟨d,hd,hRep⟩ := radial_upper_double_derivatives (2*p)
    (Nat.mul_pos (by omega) hp.pos) (selectedOrderedChart ha hb).sin_theta_pos
  refine ⟨hL,?_,min e d,lt_min he hd,?_⟩
  · apply hTop.congr' ?_ (Filter.Eventually.of_forall (fun _ => rfl))
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hd).filter_mono nhdsWithin_le_nhds] with epsilon hp heps
    rw [hRep epsilon hp heps]
  · intro j hj
    obtain ⟨C,hC,hB⟩ := hLow j hj
    refine ⟨C,hC,?_⟩
    intro epsilon hp heps
    have h := hB epsilon hp (heps.trans_le (min_le_left _ _))
    rw [hRep epsilon hp (heps.trans_le (min_le_right _ _))] at h
    exact h

/-- Source theorem thm:first. The lower-even-order clause retains the correct
published quantifier order: each fixed N and each fixed j has its own approach
threshold and bound. No uniformity over infinitely many j or any tail is asserted. -/
theorem theorem_first {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p) {a b : ℤ}
    (ha : PrimeFamily.Admissible p a) (hb : PrimeFamily.Admissible p b) (hab : a ≠ b)
    (hTW : PublishedTWFixedOrderInput (PrimeFamily.selectedPoint p a b)) :
    let k := (2*p)^2/2-1
    let A := selectedOrderedChart ha hb
    let L := localLeadingCoefficient A (2*p-1) k
    L ≠ 0 ∧
      Asymptotics.IsLittleO (𝓝[>] (0:ℝ))
        (fun epsilon => (deriv^[k] (doubleFormFactor (2*p) (sourceRadialPair A.theta epsilon).1))
          (sourceRadialPair A.theta epsilon).2 - (Real.sqrt epsilon:ℂ)⁻¹*(2*L))
        (fun epsilon => (Real.sqrt epsilon:ℂ)⁻¹) ∧
      (∃ e : ℝ, 0 < e ∧ ∀ j : ℕ, j < k → ∃ C : ℝ, 0 ≤ C ∧ ∀ epsilon : ℝ,
        0 < epsilon → epsilon < e →
        ‖(deriv^[j] (doubleFormFactor (2*p) (sourceRadialPair A.theta epsilon).1))
          (sourceRadialPair A.theta epsilon).2‖ ≤ C) ∧
      (∀ N : ℕ, 0 < N → Even N → N < 2*p → ∀ j : ℕ,
        ∃ e C : ℝ, 0 < e ∧ 0 ≤ C ∧ ∀ epsilon : ℝ, 0 < epsilon → epsilon < e →
          ‖(deriv^[j] (doubleFormFactor N (sourceRadialPair A.theta epsilon).1))
            (sourceRadialPair A.theta epsilon).2‖ ≤ C) := by
  dsimp only
  have h := first_fixed_source_asymptotic hp hp11 ha hb hab
  exact ⟨h.1,h.2.1,h.2.2,selected_lower_orders_fixed_radius_bounded hp hp11 ha hb hTW⟩

end
end IsingBulk.First
