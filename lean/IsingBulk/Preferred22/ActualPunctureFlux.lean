import IsingBulk.Preferred22.ActualShellTheorem
import IsingBulk.Preferred22.PunctureFlux

/-! Actual quantitative equality-puncture flux with the scalar-word, shell
and physical-field estimates all discharged. This is the vanishing current
input to the separate genuine integrated transport theorem. -/
namespace IsingBulk.Preferred22
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology ENNReal ContDiff

/-- Every actual large-order puncture current has uniform dyadic decay.
The cutoffs are genuine real smooth functions, and constants precede epsilon
and the exhaustion index. No q28, field or transport premise survives. -/
theorem preferred_actual_puncture_flux_uniform (d : PreferredBranchData) :
    ∃ cap : ℝ,0<cap ∧ cap<d.alpha ∧ ∀ B : PreferredCoareaBump d,B.delta<cap →
      ∃ δ₀ τ₀ ε₀ : ℝ,0<δ₀ ∧ δ₀<B.delta ∧ 0<τ₀ ∧ 0<ε₀ ∧
      ∀ δB : ℝ,0<δB → δB≤δ₀ → ∀ rcut : ℝ → ℝ,
      PreferredRightCutoffData d B δB rcut → ∀ τ : ℝ,0≤τ → τ<τ₀ →
      ∀ k j n : ℕ,j≤k → 2*k+4<n+1 → Even (n+1) →
      ∃ L : ℝ,0<L ∧ ∀ ε : ℝ,0<ε → ε<ε₀ → ∀ m : ℕ,
      (∫⁻ θ : Fin n → ℝ in angularBox n,
        ENNReal.ofReal ‖preferredRightPunctureFlux d B τ rcut j ε (preferredDyadicRadius m)
          (preferredLiftedAngles B.delta (constrainedAngles θ))‖)≤
        ENNReal.ofReal (L*(1+|Real.log ε|)*(1/2:ℝ)^m) := by
  obtain ⟨cs,hcs,hcsa,hshell⟩ := preferred_actual_all_diameter_shell_bound d
  obtain ⟨cv,hcv,_hcva,hfield⟩ := preferred_actual_angular_field_bound d
  refine ⟨min cs cv,lt_min hcs hcv,(min_le_left _ _).trans_lt hcsa,?_⟩
  intro B hBcap
  obtain ⟨δs,τs,εs,hδs,hδsδ,hτs,hεs,hs⟩ :=
    hshell B (hBcap.trans_le (min_le_left _ _))
  obtain ⟨C,εv,τv,δv,hC,hεv,hτv,hδv,_hδvδ,hv⟩ :=
    hfield B (hBcap.trans_le (min_le_right _ _))
  let δ₀ := min δs δv
  let τ₀ := min τs τv
  let ε₀ := min εs εv
  refine ⟨δ₀,τ₀,ε₀,lt_min hδs hδv,(min_le_left _ _).trans_lt hδsδ,
    lt_min hτs hτv,lt_min hεs hεv,?_⟩
  intro δB hδB hδB₀ rcut hcut τ hτ hτr k j n hj hN hEven
  have hq : PreferredAllDiameterShellBound d B δB τ ε₀ preferredPopulationCutoff rcut k :=
    (hs δB hδB (hδB₀.trans (min_le_left _ _)) rcut hcut.2.2.1 hcut.2.2.2.1 τ hτ
      (hτr.trans_le (min_le_left _ _)) k).mono_epsilon (min_le_left _ _)
  apply preferred_right_puncture_flux_uniform_bound_of_q28 d B rcut hcut hq hj hN hEven hC
  intro ε hε hεr θ hθ hd i
  apply hv (n+1) (by omega) ε τ hε (hεr.trans_le (min_le_right _ _))
    hτ (hτr.trans_le (min_le_right _ _)) θ _ hd i
  intro a
  have hm : δB≤δv := hδB₀.trans (min_le_right _ _)
  exact ⟨by linarith [(hθ a).1],(hθ a).2⟩

end
end IsingBulk.Preferred22
