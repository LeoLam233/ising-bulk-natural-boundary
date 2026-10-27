import IsingBulk.Preferred22.ActualCompleteRightDerivativeTail
import IsingBulk.Preferred22.ActualAnchorBound
import IsingBulk.Preferred22.SelectedKernelDisk

/-! The complete differentiated absolute positive-even coefficient tail.
The selected, entire named-anchor and full right estimates are instantiated
on one actual contour with the required order of parameter choices. -/
namespace IsingBulk.Preferred22
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

theorem preferred_actual_absolute_tail (d : PreferredBranchData)
    {p : ℕ} (hp : p.Prime) {a : ℤ} (ha : IsingBulk.PrimeFamily.Admissible p a)
    (hα : d.alpha=IsingBulk.PrimeFamily.angle p a)
    (Nstar k : ℕ) (hNstar : 2≤Nstar) (hEven : Even Nstar) (hk : 2*k+2=Nstar^2) :
    PreferredAbsoluteTailStatement (Complex.exp ((d.alpha:ℂ)*Complex.I)) Nstar k := by
  obtain ⟨cR,hcR,_hcRa,hright⟩ := preferred_actual_complete_right_derivative_tail d hp ha hα
  obtain ⟨cA,hcA,_hcAa,hanchor⟩ := preferred_actual_anchor_absolute_bound d
  let cap := min cR cA
  have hcap : 0<cap := lt_min hcR hcA
  let B := cappedCanonicalPreferredBump d cap hcap
  have hB : B.delta<cap := cappedCanonicalPreferredBump_delta_lt d hcap
  obtain ⟨δR,τR,εR,hδR,hδRB,hτR,hεR,hright'⟩ :=
    hright B (hB.trans_le (min_le_left _ _))
  let δB := min δR (preferredRightMargin d B)/2
  have hmargin := preferredRightMargin_bounds d B
  have hδB : 0<δB := half_pos (lt_min hδR hmargin.1)
  have hδBR : δB≤δR := by dsimp only [δB]; linarith [min_le_left δR (preferredRightMargin d B)]
  have hδBm : δB≤preferredRightMargin d B := by
    dsimp only [δB]
    linarith [min_le_right δR (preferredRightMargin d B)]
  let rcut := preferredRightCutoff d δB
  have hcut : PreferredRightCutoffData d B δB rcut := preferred_right_cutoff_data_of_le d B hδB hδBm
  obtain ⟨εA,τA,hεA,_hεA1,hτA,hanchor'⟩ :=
    hanchor B (hB.trans_le (min_le_right _ _)) δB hδB (hδBR.trans_lt hδRB)
  obtain ⟨ρ,hρ,_hρ1,hselected⟩ := preferred_actual_selected_population_bound d hcap
  let τ := min τR (min τA ρ)/2
  have hτ : 0<τ := half_pos (lt_min hτR (lt_min hτA hρ))
  have hτR' : τ<τR := by
    dsimp only [τ]
    linarith [min_le_left τR (min τA ρ)]
  have hτA' : τ<τA := by
    have hh := (min_le_right τR (min τA ρ)).trans (min_le_left τA ρ)
    dsimp only [τ]
    linarith
  have hτρ : τ<ρ := by
    have hh := (min_le_right τR (min τA ρ)).trans (min_le_right τA ρ)
    dsimp only [τ]
    linarith
  let ε₀ := min εR (min εA ρ)
  have hε₀ : 0<ε₀ := lt_min hεR (lt_min hεA hρ)
  have hεR' : ε₀≤εR := min_le_left _ _
  have hεA' : ε₀≤εA := (min_le_right _ _).trans (min_le_left _ _)
  have hερ : ε₀≤ρ := (min_le_right _ _).trans (min_le_right _ _)
  have hF : PreferredSelectedPopulationBound d B τ ε₀ := by
    intro j
    obtain ⟨C,hC,hb⟩ := hselected τ hτ hτρ j
    exact ⟨C,hC,fun n hn he ε hε hεr => hb n hn he ε hε (hεr.trans_le hερ)⟩
  have hA : PreferredAnchorAbsoluteBound d B τ ε₀ rcut k := by
    intro j hj
    obtain ⟨C,J,hC,hb⟩ := hanchor' τ hτ.le hτA' rcut hcut k j hj
    exact ⟨C,J,hC,fun n hn he ε hε hεr => hb n hn he ε hε (hεr.trans_le hεA')⟩
  have hR := hright' δB τ ε₀ hδB hδBR hτ.le hτR' hε₀ hεR' rcut hcut Nstar k hNstar hEven hk
  exact preferred_coefficient_tail_of_component_bounds d B hτ.le hε₀ rcut
    hcut.2.2.1 hcut.2.2.2.1 Nstar k hNstar hF hA hR

end
end IsingBulk.Preferred22
