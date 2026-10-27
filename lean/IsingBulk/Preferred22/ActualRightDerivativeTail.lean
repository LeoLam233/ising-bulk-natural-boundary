import IsingBulk.Preferred22.RightRadialTransport
import IsingBulk.Preferred22.ActualShellTheorem
import IsingBulk.Preferred22.CompleteRightDerivativeTail

/-! Actual complex derivatives of the complete large-order right integral:
source scalar bounds, coarea, full absolute mass and the global punctured
Stokes identity are all discharged on one common physical regime. -/
namespace IsingBulk.Preferred22
noncomputable section

theorem PreferredLargeRightIntegralIdentity.mono_epsilon
    {d : PreferredBranchData} {B : PreferredCoareaBump d} {τ ε₀ ε₁ : ℝ}
    {r : ℝ → ℝ} {k : ℕ}
    (h : PreferredLargeRightIntegralIdentity d B τ ε₀ r k) (he : ε₁≤ε₀) :
    PreferredLargeRightIntegralIdentity d B τ ε₁ r k := by
  intro n hN hEven j hj ε hε hεr
  exact h n hN hEven j hj ε hε (hεr.trans_le he)

/-- No scalar, shell, mass, flux, or integrated-transport premise remains.
This endpoint concerns the genuine complete right-cell derivatives for
N>2k+4; the finite intermediate block is a separate source obligation. -/
theorem preferred_actual_large_right_derivative_tail (d : PreferredBranchData) :
    ∃ cap : ℝ,0<cap ∧ cap<d.alpha ∧ ∀ B : PreferredCoareaBump d,B.delta<cap →
      ∃ δ₀ τ₀ ε₀ : ℝ,0<δ₀ ∧ δ₀<B.delta ∧ 0<τ₀ ∧ 0<ε₀ ∧
      ∀ δB : ℝ,0<δB → δB≤δ₀ → ∀ rcut : ℝ → ℝ,
      PreferredRightCutoffData d B δB rcut → ∀ τ : ℝ,0≤τ → τ<τ₀ →
      ∀ k : ℕ,PreferredRightDerivativeTailStatement d B τ ε₀ rcut (2*k+4) k := by
  obtain ⟨cs,hcs,hcsa,hs⟩ := preferred_actual_all_diameter_shell_bound d
  obtain ⟨ci,hci,_hcia,hi⟩ := preferred_actual_large_right_integral_identity d
  let cap := min cs ci
  refine ⟨cap,lt_min hcs hci,(min_le_left _ _).trans_lt hcsa,?_⟩
  intro B hBcap
  obtain ⟨δs,τs,εs,hδs,hδsB,hτs,hεs,hs'⟩ := hs B (hBcap.trans_le (min_le_left _ _))
  obtain ⟨δi,τi,εi,hδi,_hδiB,hτi,hεi,hi'⟩ := hi B (hBcap.trans_le (min_le_right _ _))
  let δ₀ := min δs δi
  let τ₀ := min τs τi
  let ε₀ := min εs εi
  refine ⟨δ₀,τ₀,ε₀,lt_min hδs hδi,(min_le_left _ _).trans_lt hδsB,
    lt_min hτs hτi,lt_min hεs hεi,?_⟩
  intro δB hδB hδB₀ rcut hcut τ hτ hτr k
  have hshell := hs' δB hδB (hδB₀.trans (min_le_left _ _)) rcut
    hcut.2.2.1 hcut.2.2.2.1 τ hτ (hτr.trans_le (min_le_left _ _)) k
  have hid := hi' δB hδB (hδB₀.trans (min_le_right _ _)) rcut hcut
    τ hτ (hτr.trans_le (min_le_right _ _)) k
  exact preferred_large_right_derivative_tail_of_identity d B rcut hcut k
    (hshell.mono_epsilon (min_le_left _ _)) (hid.mono_epsilon (min_le_right _ _))

end
end IsingBulk.Preferred22
