import IsingBulk.Preferred22.WordShellBound
import IsingBulk.Preferred22.ActualWordBounds

/-! The complete actual all-order q28 theorem. The normalized scalar word
bound is proved by the source chain and is discharged here, not assumed. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set
open scoped BigOperators ContDiff

theorem PreferredAllDiameterShellBound.mono_epsilon
    {d : PreferredBranchData} {B : PreferredCoareaBump d} {δB τ ε₀ ε₁ : ℝ}
    {η rcut : ℝ → ℝ} {k : ℕ}
    (h : PreferredAllDiameterShellBound d B δB τ ε₀ η rcut k) (he : ε₁≤ε₀) :
    PreferredAllDiameterShellBound d B δB τ ε₁ η rcut k := by
  intro j hj
  obtain ⟨C,J,hC,hbound⟩ := h j hj
  refine ⟨C,J,hC,?_⟩
  intro n hN hEven ε r hε hεr hr l i a
  exact hbound n hN hEven ε r hε (hεr.trans_le he) hr l i a

/-- Full actual all-diameter shell bounds, for every fixed transport order.
One physical regime precedes all N and j; cutoff smoothness is genuinely real.
The right margin may still be shrunk for the finite-mean construction. -/
theorem preferred_actual_all_diameter_shell_bound (d : PreferredBranchData) :
    ∃ cap : ℝ,0<cap ∧ cap<d.alpha ∧ ∀ B : PreferredCoareaBump d,B.delta<cap →
      ∃ δ₀ τ₀ ε₀ : ℝ,0<δ₀ ∧ δ₀<B.delta ∧ 0<τ₀ ∧ 0<ε₀ ∧
      ∀ δB : ℝ,0<δB → δB≤δ₀ → ∀ rcut : ℝ → ℝ,
      ContDiff ℝ ∞ rcut → Function.Periodic rcut (2*Real.pi) →
      ∀ τ : ℝ,0≤τ → τ<τ₀ → ∀ k : ℕ,
      PreferredAllDiameterShellBound d B δB τ ε₀ preferredPopulationCutoff rcut k := by
  obtain ⟨cs,hcs,hcsa,hshell⟩ := preferred_all_diameter_shell_bound_of_normalized_words d
  obtain ⟨cw,hcw,_hcwa,hword⟩ := preferred_actual_normalized_word_bounds d
  let cap := min cs cw
  refine ⟨cap,lt_min hcs hcw,(min_le_left _ _).trans_lt hcsa,?_⟩
  intro B hBcap
  obtain ⟨δs,τs,εs,hδs,hδsδ,hτs,hεs,hs⟩ := hshell B (hBcap.trans_le (min_le_left _ _))
  obtain ⟨εw,τw,δw,hεw,hτw,hδw,_hδwδ,hw⟩ := hword B (hBcap.trans_le (min_le_right _ _))
  let δ₀ := min δs δw
  let τ₀ := min τs τw
  let ε₀ := min εs εw
  refine ⟨δ₀,τ₀,ε₀,lt_min hδs hδw,(min_le_left _ _).trans_lt hδsδ,
    lt_min hτs hτw,lt_min hεs hεw,?_⟩
  intro δB hδB hδB₀ rcut hrcut hrper τ hτ hτr k
  apply hs δB τ ε₀ hδB (hδB₀.trans (min_le_left _ _)) hτ
    (hτr.trans_le (min_le_left _ _)) (lt_min hεs hεw) (min_le_left _ _)
    preferredPopulationCutoff rcut preferredPopulationCutoff_smooth hrcut k
  intro j _hj
  obtain ⟨C,hC,hcoeff⟩ := hw rcut hrcut hrper j
  refine ⟨C,5*j*j+12*j+2,hC,?_⟩
  intro N hN ε hε hεr θ hθ hdiam w
  apply hcoeff N (by omega) ε τ hε (hεr.trans_le (min_le_right _ _))
    hτ (hτr.trans_le (min_le_right _ _)) θ _ hdiam w
  intro i
  have hδBw : δB≤δw := hδB₀.trans (min_le_right _ _)
  constructor <;> linarith [(hθ i).1,(hθ i).2]

end
end IsingBulk.Preferred22
