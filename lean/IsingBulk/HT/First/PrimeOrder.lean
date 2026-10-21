import IsingBulk.Algebra.PrimeTheorem
import IsingBulk.First.NonNickelRadialBounds
import IsingBulk.First.MeanSelectedData

/-!
HT prime-order adapters for the positive selected family. The cyclotomic,
density, and nonstationary analytic proofs are inherited from LT. Doubling the
integer angle labels embeds an n-Nickel representation at 2n, allowing the
existing first-even-order theorem to exclude every n<p without pretending that
p is even. The quadrant-II family is a separate outstanding obligation.
-/
namespace IsingBulk.HT.First
noncomputable section
open IsingBulk.PrimeFamily

/-- Doubling the denominator and integer label leaves the angle unchanged. -/
theorem angle_double_order (n : ℕ) (l : ℤ) : angle (2*n) (2*l) = angle n l := by
  unfold angle
  push_cast
  ring

/-- Every n-Nickel equation is also a 2n-Nickel equation. -/
theorem nickel_double_order {s : ℂ} {n : ℕ} (h : NickelAt s n) :
    NickelAt s (2*n) := by
  obtain ⟨hs,l,m,he⟩ := h
  exact ⟨hs,2*l,2*m,by simpa only [angle_double_order] using he⟩

/-- First HT odd order for the positive prime family; in fact no positive
particle order below p is Nickel. -/
theorem first_prime_Nickel_order {p : ℕ} (hp : p.Prime) (hp3 : 2 < p)
    {a b : ℤ} (ha : Admissible p a) (hb : Admissible p b) :
    Odd p ∧ NickelAt (selectedPoint p a b) p ∧
      ∀ n : ℕ, 0 < n → n < p → ¬ NickelAt (selectedPoint p a b) n := by
  refine ⟨hp.odd_of_ne_two (by omega), ?_, ?_⟩
  · refine ⟨Complex.norm_exp_ofReal_mul_I _,a,b,?_⟩
    rw [selectedPoint_relation ha hb]
    unfold cosineAverage
    push_cast
    ring
  · intro n hn hnp hNickel
    apply (first_even_Nickel_order hp hp3 ha hb).2 (2*n)
      (by omega) ⟨n,by omega⟩ (by omega)
    exact nickel_double_order hNickel

/-- The established unique pair result specializes from 2p to p by label
inclusion, without changing its cyclotomic proof. -/
theorem unique_prime_cosine_pair {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p)
    {a b : ℤ} (ha : Admissible p a) (hb : Admissible p b) (l m : ℤ)
    (hrep : selectedPoint p a b+(selectedPoint p a b)⁻¹ =
      (Real.cos (angle p l) : ℂ)+(Real.cos (angle p m) : ℂ)) :
    (Real.cos (angle p l) = Real.cos (angle p a) ∧
      Real.cos (angle p m) = Real.cos (angle p b)) ∨
    (Real.cos (angle p l) = Real.cos (angle p b) ∧
      Real.cos (angle p m) = Real.cos (angle p a)) := by
  have h := unique_cosine_pair hp hp11 ha hb (2*l) (2*m)
    (by simpa only [angle_double_order] using hrep)
  simpa only [angle_double_order] using h

/-- Actual fixed-radius lower-order offsite bounds for HT. There is no
published smoothness input and no new analytic assumption in this adapter. -/
theorem selected_lower_odd_orders_fixed_radius_bounded {p : ℕ} {a b : ℤ}
    (hp : p.Prime) (hp11 : 11 ≤ p)
    (ha : Admissible p a) (hb : Admissible p b) :
    ∀ N : ℕ, 0 < N → Odd N → N < p → ∀ j : ℕ,
      ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        ‖(deriv^[j] (IsingBulk.First.doubleFormFactor N
          (IsingBulk.First.sourceRadialPair
            (IsingBulk.First.selectedOrderedChart ha hb).theta ε).1))
          (IsingBulk.First.sourceRadialPair
            (IsingBulk.First.selectedOrderedChart ha hb).theta ε).2‖ ≤ C := by
  intro N hN _hOdd hNp j
  have hlevel := cosineAverage_bounds ha hb
  have hS : IsingBulk.First.sourceS
      (Complex.exp (((IsingBulk.First.selectedOrderedChart ha hb).theta:ℂ)*Complex.I)) =
      ((2*cosineAverage p a b:ℝ):ℂ) := by
    simpa only [IsingBulk.First.sourceS,selectedPoint,IsingBulk.First.selectedOrderedChart,
      Complex.ofReal_mul,Complex.ofReal_ofNat] using selectedPoint_relation ha hb
  have hn := (first_prime_Nickel_order hp (by omega) ha hb).2.2 N hN hNp
  obtain ⟨e,he,hbnd⟩ := IsingBulk.First.nonNickel_fixed_radius_radial_bound hN
    (2*cosineAverage p a b) (IsingBulk.First.selectedOrderedChart ha hb).theta
    (by constructor <;> linarith) (IsingBulk.First.selectedOrderedChart ha hb).sin_theta_pos hS hn
  obtain ⟨C,hC,hB⟩ := hbnd j
  exact ⟨e,C,he,hC,fun ε hε hεe => hB ε hε hεe.le⟩

end
end IsingBulk.HT.First
