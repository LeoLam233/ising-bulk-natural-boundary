import IsingBulk.First.CompatibleComplement
import IsingBulk.First.ComplementGlobalBound
import IsingBulk.First.AngularReindex
import IsingBulk.HT.First.OddComplementGeometry

/-! Actual odd-order selected complement. The entire LT nonstationary finite
cover, partition, integration-by-parts, derivative and radial-bound stack is
reused through `source_complement_global_bound`; only the p-indexed selected
geometry and reindexing wrappers are new. -/
namespace IsingBulk.HT.First
noncomputable section
open Complex Set Filter IsingBulk.First
open scoped Topology ContDiff

/-- No selected bad configuration lies in the actual complementary support;
all x angular variables remain unrestricted and unweighted. -/
theorem odd_selected_compatible_complement_good {p : ℕ} (hp : p.Prime) {a b : ℤ}
    {U : Set (Fin (p-1) → ℝ)}
    (c : CompatibleYCutoffData (p-1) (PrimeFamily.angle p a) (PrimeFamily.angle p b) U) :
    let hN : p-1+1=p := by have := hp.pos; omega
    ContDiff ℝ ∞ (compatibleDoubleComplement hN c) ∧
      DoubleCoordinatePeriodic (compatibleDoubleComplement hN c) ∧
      (∀ u ∈ tsupport (compatibleDoubleComplement hN c),
        ¬ oddSelectedBadConfiguration a b (angleTuple 1 u.1) (angleTuple 1 u.2)) := by
  dsimp only
  refine ⟨compatibleDoubleComplement_contDiff _ c,compatibleDoubleComplement_periodic _ c,?_⟩
  intro u hu hbad
  apply compatibleDoubleComplement_not_support (by have := hp.pos; omega) c (u := u) _ hu
  rcases hbad with h | h
  · right
    intro j
    have hh := h.2 j
    simpa [angleTuple,anglePoint,circleMap,selectedLowerRoot,mul_comm] using hh
  · left
    intro j
    have hh := h.2 j
    simpa [angleTuple,anglePoint,circleMap,selectedLowerRoot,mul_comm] using hh

/-- Compatibility with the selected first-order complement. -/
theorem odd_selected_complement_global_bound {p : ℕ} {a b : ℤ}
    (hp : p.Prime) (hp11 : 11 ≤ p)
    (ha : PrimeFamily.Admissible p a) (hb : PrimeFamily.Admissible p b)
    (θ : ℝ) (hθ : 0 < Real.sin θ)
    (hS : sourceS (Complex.exp ((θ:ℂ)*Complex.I)) =
      ((2*PrimeFamily.cosineAverage p a b:ℝ):ℂ))
    (W : DoubleAngularVector p → ℝ) (hW : ContDiff ℝ ∞ W)
    (hWp : DoubleCoordinatePeriodic W)
    (hgood : ∀ u ∈ tsupport W,
      ¬ oddSelectedBadConfiguration a b (angleTuple 1 u.1) (angleTuple 1 u.2)) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
        ‖(deriv^[j] (fun s => localizedDoubleFormFactor p (sourceRadialPair θ ε).1 s W))
          (sourceRadialPair θ ε).2‖ ≤ C := by
  apply source_complement_global_bound hp.pos
    (2*PrimeFamily.cosineAverage p a b) θ hθ hS W hW hWp
  intro u hu
  exact odd_selected_active_separating_functional hp hp11 ha hb
    (fun _ => anglePoint_norm (by norm_num) _)
    (fun _ => anglePoint_norm (by norm_num) _) (hgood u hu)

theorem odd_selected_compatible_complement_bounded {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p)
    {a b : ℤ} (ha : PrimeFamily.Admissible p a) (hb : PrimeFamily.Admissible p b)
    {U : Set (Fin (p-1) → ℝ)}
    (c : CompatibleYCutoffData (p-1) (PrimeFamily.angle p a) (PrimeFamily.angle p b) U) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ epsilon₀ →
        ‖(deriv^[j] (fun s => localizedDoubleFormFactor (p-1+1)
          (sourceRadialPair (selectedOrderedChart ha hb).theta epsilon).1 s
          (fun u => c.remainder u.2)))
          (sourceRadialPair (selectedOrderedChart ha hb).theta epsilon).2‖ ≤ C := by
  have hN : p-1+1=p := by have := hp.pos; omega
  have hW := odd_selected_compatible_complement_good hp c
  dsimp only at hW
  have hS : sourceS (exp (((selectedOrderedChart ha hb).theta:ℂ)*I)) =
      ((2*PrimeFamily.cosineAverage p a b:ℝ):ℂ) := by
    simpa only [sourceS,PrimeFamily.selectedPoint,selectedOrderedChart,Complex.ofReal_mul,Complex.ofReal_ofNat] using
      PrimeFamily.selectedPoint_relation ha hb
  obtain ⟨e,he,hbound⟩ := odd_selected_complement_global_bound hp hp11 ha hb
    (selectedOrderedChart ha hb).theta (selectedOrderedChart ha hb).sin_theta_pos hS
    (compatibleDoubleComplement hN c) hW.1 hW.2.1 hW.2.2
  refine ⟨e,he,?_⟩
  intro j
  obtain ⟨C,hC,hB⟩ := hbound j
  refine ⟨C,hC,?_⟩
  intro epsilon heps hee
  have h := hB epsilon heps hee
  rw [← iteratedDeriv_eq_iterate] at h ⊢
  change ‖iteratedDeriv j (fun s => localizedDoubleFormFactor p
    (sourceRadialPair (selectedOrderedChart ha hb).theta epsilon).1 s
    (fun u => reindexYWeight hN c.remainder u.2))
    (sourceRadialPair (selectedOrderedChart ha hb).theta epsilon).2‖ ≤ C at h
  rw [localizedDoubleFormFactor_iteratedDeriv_y_reindex] at h
  exact h

end
end IsingBulk.HT.First
