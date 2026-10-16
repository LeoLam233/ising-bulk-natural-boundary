import IsingBulk.First.LowerOrderTransfer
import IsingBulk.First.NonNickelRadialBounds

/-! The lower-order conclusion for the literal manuscript contour coefficient,
with the chosen source radius held fixed under every s derivative. -/
namespace IsingBulk.First
noncomputable section
open Set

theorem lowerOrder_fixed_radius_bound_of_published (N : ℕ) (hN : 0 < N)
    (level : ℝ) (hlevel : 0 < level ∧ level < 2) (θ : ℝ) (hθ : 0 < Real.sin θ)
    (hS : sourceS (Complex.exp ((θ:ℂ)*Complex.I)) = (level:ℂ))
    (hTW : PublishedFullSiteBounded N (Complex.exp ((θ:ℂ)*Complex.I))) :
    ∀ j : ℕ, ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        ‖(deriv^[j] (doubleFormFactor N (sourceRadialPair θ ε).1))
          (sourceRadialPair θ ε).2‖ ≤ C := by
  obtain ⟨d,hd,_,hm⟩ := radial_disk_source_trace_margin hθ
  intro j
  obtain ⟨e,C,he,hC,hb⟩ := lowerOrder_radial_bound_of_published N hN level hlevel θ hθ hS hTW j
  refine ⟨min e d,C,lt_min he hd,hC,?_⟩
  intro ε hε hεsmall
  have hεe := hεsmall.trans_le (min_le_left e d)
  have hεd := hεsmall.trans_le (min_le_right e d)
  have hmargin := (hm ε hε hεd (IsingBulk.Branch.radialParameter θ ε)
    (by simpa using mul_pos (show 0 < Real.sin θ/16 by positivity) hε)).2
  have hr : 0 < (sourceRadialPair θ ε).1 := Real.exp_pos _
  have hr1 : (sourceRadialPair θ ε).1 < 1 := by
    change Real.exp (-(Real.sin θ/4)*ε) < 1
    rw [Real.exp_lt_one_iff]
    exact mul_neg_of_neg_of_pos (by linarith) hε
  rw [← iteratedDeriv_eq_iterate,
    ← upperFormFactor_iteratedDeriv_fixed_radius N hN j hr hr1
      (s := (sourceRadialPair θ ε).2) hmargin,
    iteratedDeriv_eq_iterate]
  exact hb ε hε hεe

/-- This endpoint uses the actual offsite double contour, not an abstract
bounded function or the published full-site observable. -/
theorem selected_lower_orders_fixed_radius_bounded {p : ℕ} {a b : ℤ}
    (hp : p.Prime) (hp11 : 11 ≤ p)
    (ha : PrimeFamily.Admissible p a) (hb : PrimeFamily.Admissible p b) :
    ∀ N : ℕ, 0 < N → Even N → N < 2*p → ∀ j : ℕ,
      ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        ‖(deriv^[j] (doubleFormFactor N (sourceRadialPair (selectedOrderedChart ha hb).theta ε).1))
          (sourceRadialPair (selectedOrderedChart ha hb).theta ε).2‖ ≤ C := by
  intro N hN he hlt j
  have hlevel := PrimeFamily.cosineAverage_bounds ha hb
  have hS : sourceS (Complex.exp (((selectedOrderedChart ha hb).theta:ℂ)*Complex.I)) =
      ((2*PrimeFamily.cosineAverage p a b:ℝ):ℂ) := by
    simpa only [sourceS,PrimeFamily.selectedPoint,selectedOrderedChart,
      Complex.ofReal_mul,Complex.ofReal_ofNat] using PrimeFamily.selectedPoint_relation ha hb
  have hn := (PrimeFamily.first_even_Nickel_order hp (by omega) ha hb).2 N hN he hlt
  obtain ⟨e,he0,hbnd⟩ := nonNickel_fixed_radius_radial_bound hN
    (2*PrimeFamily.cosineAverage p a b) (selectedOrderedChart ha hb).theta
    (by constructor <;> linarith) (selectedOrderedChart ha hb).sin_theta_pos hS hn
  obtain ⟨C,hC,hB⟩ := hbnd j
  exact ⟨e,C,he0,hC,fun ε hε hεe => hB ε hε hεe.le⟩


end
end IsingBulk.First
