import IsingBulk.Analysis.JetsTheorem
import IsingBulk.Tail.AllBranchExteriorPoleAbsorption
import IsingBulk.Tail.BoundedMultiplierContinuity
import IsingBulk.Tail.AllBranchExteriorSelectedRemovable

/-!
HT-1.0 Appendix A and the near-collision sectors: conversion of the HT
order k = (p²-1)/2 into the strict powers used in puncture removal and
coarea. The rational weights, actual semantic jet list and coefficient
neighborhoods are inherited from LT without a particle-parity premise.
-/
namespace IsingBulk.HT.Lie
noncomputable section
open IsingBulk.Jets IsingBulk.Tail Filter
open scoped Topology

/-- The exact HT derivative order gives a uniform two-power budget. -/
theorem twice_order_le {p j : ℕ} (hj : j ≤ (p^2-1)/2) :
    2*j ≤ p^2-1 := by omega

/-- The source's conservative coarea exponent has margin at least 4p+1.
Oddness is used upstream to obtain N ≥ p+2, not in this polynomial fact. -/
theorem coarea_power_lower {p N j : ℕ} (hp : 1 ≤ p)
    (hN : p+2 ≤ N) (hj : j ≤ (p^2-1)/2) :
    4*p+1 ≤ N^2-2*j-4 := by
  have hp2 : 1 ≤ p^2 := by nlinarith
  have hj2 := twice_order_le hj
  have hsub : p^2-1+1 = p^2 := by omega
  have hsq : (p+2)^2 ≤ N^2 := Nat.pow_le_pow_left hN 2
  have htotal : 4*p+1+2*j+4 ≤ N^2 := by nlinarith
  omega

theorem coarea_power_pos {p N j : ℕ} (hp : 1 ≤ p)
    (hN : p+2 ≤ N) (hj : j ≤ (p^2-1)/2) :
    0 < N^2-2*j-4 := by
  have h := coarea_power_lower hp hN hj
  omega

/-- One less inverse radius is lost before coarea, at the actual flux. -/
theorem full_collision_flux_power_lower {p N j : ℕ} (hp : 1 ≤ p)
    (hN : p+2 ≤ N) (hj : j ≤ (p^2-1)/2) :
    4*p+2 ≤ N^2-2*j-3 := by
  have h := coarea_power_lower hp hN hj
  omega

theorem full_collision_flux_power_pos {p N j : ℕ} (hp : 1 ≤ p)
    (hN : p+2 ≤ N) (hj : j ≤ (p^2-1)/2) :
    0 < N^2-2*j-3 := by
  have h := full_collision_flux_power_lower hp hN hj
  omega

/-- The selected-tube exponent stays positive at every earlier stage. -/
theorem selected_flux_power_pos {M k j : ℕ} (hM : 2*k+2 < M)
    (hj : j ≤ k) : 0 < 2*M+1-2*j := by omega

/-- No change is made to the LT term list. Its filtration controls the
actual coefficient, cutoff and numerator words at the HT derivative order. -/
theorem source_terms_ht_filtration {p N j : ℕ} (a b : Fin N)
    (hj : j ≤ (p^2-1)/2) (T : SourceJetTerm N)
    (hT : T ∈ sourceJetTerms a b j) :
    T.pole+T.cutoff.length+(spatialWord T.numerator).length ≤ p^2-1 ∧
      parameterOrder T.numerator+T.cutoff.length+
        (spatialWord T.numerator).length ≤ (p^2-1)/2 := by
  have h := sourceJetTerms_valid a b j T hT
  exact ⟨h.1.trans (twice_order_le hj), h.2.trans hj⟩

/-- Every term fits the rational selected weight chosen once for all j≤k.
This is the order premise of the actual LT pole-absorption theorem. -/
theorem source_term_weight_budget {N M k j : ℕ} (a b : Fin N)
    (hM : 2*k+2 < M) (hj : j ≤ k) (T : SourceJetTerm N)
    (hT : T ∈ sourceJetTerms a b j) :
    T.cutoff.length ≤ k ∧ T.pole+T.cutoff.length ≤ 2*M := by
  have h := sourceJetTerms_valid a b j T hT
  constructor <;> omega

/-- The source weight estimate with its stated M>2k+2 quantifier order.
The constant is selected before dimension, selected indices and coordinates. -/
theorem rational_weight_jets (M k : ℕ) (hM : 2*k+2 < M) :
    ∃ C : ℕ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N → ∀ a b : Fin N,
      ∀ u : Fin N → ℝ, 0 < allBranchExteriorDiameter u →
      ∀ l : List (Fin N), l.length ≤ k →
      ‖cutoffJet l (allBranchExteriorPairWeight M a b) u‖ ≤
        (C:ℝ)*(N:ℝ)^C*|u a-u b|^(2*M-l.length)/
          (allBranchExteriorDiameter u)^(2*M) :=
  allBranchExterior_weight_jets_uniform M k (by omega) (by omega)

/-- A literal rational weight absorbs every selected pole of the actual
semantic recurrence. The branch estimate is reused, not postulated. -/
theorem rational_weight_absorbs_source_terms (d₀ : IsingBulk.Branch.LocalBranchData)
    (M k : ℕ) (hM : 2*k+2 < M) :
    ∃ C : ℕ, 0 < C ∧ ∃ c r : ℝ, 0 < c ∧ 0 < r ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ r → ∀ N : ℕ, 1 ≤ N →
      ∀ a b : Fin N, ∀ u : Fin N → ℝ, (∀ i, |u i| ≤ r) → u a ≠ u b →
      ∀ j : ℕ, j ≤ k → ∀ T ∈ sourceJetTerms a b j,
      ‖cutoffJet T.cutoff (allBranchExteriorPairWeight M a b) u‖ /
        ‖IsingBulk.Branch.originalPhase d₀ ε (u a)-
          IsingBulk.Branch.originalPhase d₀ ε (u b)‖^T.pole ≤
      ((C:ℝ)*(N:ℝ)^C)*(c⁻¹)^T.pole/
        (allBranchExteriorDiameter u)^(T.cutoff.length+T.pole) := by
  obtain ⟨C,hC,c,r,hc,hr,h⟩ :=
    allBranchExterior_actual_pole_absorption d₀ M k (by omega) (by omega)
  refine ⟨C,hC,c,r,hc,hr,?_⟩
  intro ε hε hεr N hN a b u hu hab j hj T hT
  have hbudget := source_term_weight_budget a b hM hj T hT
  exact h ε hε hεr N hN a b u hu hab T.cutoff hbudget.1 T.pole hbudget.2

/-- The weight zero cancels the pole of an additional field in a selected
flux. In fact the resulting real germ has zero first derivative on the
selected diagonal. No analyticity of the real cutoff is required. -/
theorem selected_flux_ratio_flat {N M k j : ℕ} (a b : Fin N)
    (hM : 2*k+2 < M) (hj : j ≤ k) (T : SourceJetTerm N)
    (hT : T ∈ sourceJetTerms a b j) (v θ u : ℝ) (s : ℂ)
    (hs : s ≠ 0) (hr : 0 < (chartW s v θ (u:ℂ)).re)
    (hi : 0 < (chartW s v θ (u:ℂ)).im)
    (hg : angularG v θ (u:ℂ) ≠ 0)
    (hsi : Complex.sin (chartPhase s v θ (u:ℂ)) ≠ 0) :
    HasFDerivAt
      (allBranchSelectedPowerRatio v θ (2*M-T.cutoff.length) (T.pole+1))
      (0 : ((ℝ × ℝ) × ℂ) →L[ℝ] ℂ) ((u,u),s) := by
  have hfiltration := sourceJetTerms_valid a b j T hT
  exact allBranchExterior_selected_power_flat v θ u s
    (2*M-T.cutoff.length) (T.pole+1) (by omega) hs hr hi hg hsi

/-- A quantitative flux bound with a positive collision power implies an
actual zero-flux limit. This conclusion still requires the geometric flux
bound as input; an exponent alone is not a Stokes theorem. -/
theorem flux_tendsto_zero_of_power_bound {ι : Type*} {l : Filter ι}
    (F : ι → ℂ) (r : ι → ℝ) (C : ℝ) (e : ℕ) (he : 0 < e)
    (hr : Tendsto r l (𝓝 0))
    (hF : ∀ᶠ i in l, ‖F i‖ ≤ C*(r i)^e) :
    Tendsto F l (𝓝 0) := by
  have hlim : Tendsto (fun i => C*(r i)^e) l (𝓝 0) := by
    simpa only [zero_pow (Nat.ne_of_gt he), mul_zero] using
      tendsto_const_nhds.mul (hr.pow e)
  exact squeeze_zero_norm' hF hlim

/-- Both puncture limits are taken for fixed ε,N. No boundary-uniform
estimate or interchange of these limits is inferred here. -/
theorem full_collision_flux_tendsto_zero {ι : Type*} {l : Filter ι}
    {p N j : ℕ} (hp : 1 ≤ p) (hN : p+2 ≤ N)
    (hj : j ≤ (p^2-1)/2) (F : ι → ℂ) (r : ι → ℝ) (C : ℝ)
    (hr : Tendsto r l (𝓝 0))
    (hF : ∀ᶠ i in l, ‖F i‖ ≤ C*(r i)^(N^2-2*j-3)) :
    Tendsto F l (𝓝 0) :=
  flux_tendsto_zero_of_power_bound F r C _
    (full_collision_flux_power_pos hp hN hj) hr hF

end
end IsingBulk.HT.Lie
