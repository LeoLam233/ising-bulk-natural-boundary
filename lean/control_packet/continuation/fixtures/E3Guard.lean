import IsingBulk
import Lean.Util.CollectAxioms

/- Targeted E3 regression adapted from the Opus control. Production imports
neither this fixture nor its guard-less comparison premise. -/
open IsingBulk.First IsingBulk.Final IsingBulk.Branch Filter Asymptotics
open scoped Topology

namespace IsingBulkControls

-- This definitional check fails if the audited non-Nickel guard is removed.
theorem E3_retains_Nickel_guard (s₀ : ℂ) :
    PublishedTWFixedOrderInput s₀ ↔
      (‖s₀‖ = 1 → ∀ N : ℕ, 0 < N → Even N →
        ¬ IsingBulk.PrimeFamily.NickelAt s₀ N → PublishedFullSiteBounded N s₀) := Iff.rfl

theorem selected_first_order_is_Nickel {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p)
    {a b : ℤ} (ha : IsingBulk.PrimeFamily.Admissible p a)
    (hb : IsingBulk.PrimeFamily.Admissible p b) :
    IsingBulk.PrimeFamily.NickelAt (IsingBulk.PrimeFamily.selectedPoint p a b) (2*p) :=
  (IsingBulk.PrimeFamily.first_even_Nickel_order hp (by omega) ha hb).1

def E3NoGuard (s₀ : ℂ) : Prop :=
  ‖s₀‖ = 1 → ∀ N : ℕ, 0 < N → Even N → PublishedFullSiteBounded N s₀

-- FIRST's internal singular carrier refutes the guard-less comparison premise.
theorem E3NoGuard_refuted {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p) {a b : ℤ}
    (ha : IsingBulk.PrimeFamily.Admissible p a) (hb : IsingBulk.PrimeFamily.Admissible p b)
    (hab : a ≠ b) : ¬ E3NoGuard (IsingBulk.PrimeFamily.selectedPoint p a b) := by
  intro h
  have hnorm : ‖IsingBulk.PrimeFamily.selectedPoint p a b‖ = 1 := by
    unfold IsingBulk.PrimeFamily.selectedPoint; exact Complex.norm_exp_ofReal_mul_I _
  have hpos : 0 < 2*p := by have := hp.pos; omega
  have hpub := h hnorm (2*p) hpos (even_two_mul p)
  have hlevel := IsingBulk.PrimeFamily.cosineAverage_bounds ha hb
  have hbound := lowerOrder_radial_bound_of_published (2*p) hpos
    (2*IsingBulk.PrimeFamily.cosineAverage p a b) (by constructor <;> linarith)
    (selectedOrderedChart ha hb).theta (selectedOrderedChart ha hb).sin_theta_pos
    (by simpa only [sourceS,IsingBulk.PrimeFamily.selectedPoint,selectedOrderedChart,
          Complex.ofReal_mul,Complex.ofReal_ofNat] using
        IsingBulk.PrimeFamily.selectedPoint_relation ha hb) hpub
  obtain ⟨hL, hTop, -⟩ := first_upper_asymptotic hp hp11 ha hb hab
  have hn : 2*p-1+1 = 2*p := by have := hp.pos; omega
  simp only [hn] at hL hTop
  obtain ⟨e0, C, he0, -, hB⟩ := hbound ((2*p)^2/2-1)
  have hF : (fun ε : ℝ => iteratedDeriv ((2*p)^2/2-1) (upperFormFactor (2*p))
        (radialParameter (selectedOrderedChart ha hb).theta ε))
      =o[𝓝[>] 0] (fun ε : ℝ => (Real.sqrt ε : ℂ)⁻¹) :=
    IsingBulk.First.bounded_radial_term_isLittleO (show 0 < e0/2 by positivity)
      (fun e he hee => by rw [iteratedDeriv_eq_iterate]; exact hB e he (by linarith))
  have h2 : (fun ε : ℝ => (Real.sqrt ε : ℂ)⁻¹ *
        (2 * localLeadingCoefficient (selectedOrderedChart ha hb) (2*p-1) ((2*p)^2/2-1)))
      =o[𝓝[>] 0] (fun ε : ℝ => (Real.sqrt ε : ℂ)⁻¹) :=
    (hF.sub hTop).congr_left (fun ε => by ring)
  have h2L : (2 * localLeadingCoefficient (selectedOrderedChart ha hb) (2*p-1) ((2*p)^2/2-1)) ≠ 0 :=
    mul_ne_zero two_ne_zero hL
  have h3 : (fun ε : ℝ => (Real.sqrt ε : ℂ)⁻¹) =o[𝓝[>] 0] (fun ε : ℝ => (Real.sqrt ε : ℂ)⁻¹) :=
    (h2.const_mul_left
      ((2 * localLeadingCoefficient (selectedOrderedChart ha hb) (2*p-1) ((2*p)^2/2-1))⁻¹)).congr_left
    (fun ε => by rw [mul_comm ((Real.sqrt ε:ℂ)⁻¹), ← mul_assoc, inv_mul_cancel₀ h2L, one_mul])
  refine Asymptotics.isLittleO_irrefl ?_ h3
  refine Filter.Eventually.frequently ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hs : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  simp [hs.ne']

end IsingBulkControls

open Lean Elab Command in
run_cmd do
  for name in #[`IsingBulkControls.E3_retains_Nickel_guard,
      `IsingBulkControls.selected_first_order_is_Nickel, `IsingBulkControls.E3NoGuard_refuted] do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == `propext || ax == `Classical.choice || ax == `Quot.sound do
        throwError "Unapproved E3 control axiom: {name}; {ax}"
    logInfo m!"E3_CONTROL_AXIOMS: {name}; AXIOMS: {axioms}"
  logInfo "E3_GUARD_CONTROL_PASSED"
