import IsingBulk.Preferred22.ShellGeometry
import IsingBulk.Preferred22.CoordinateDiameter

/-! Upper-scale and diameter control from the literal constrained shell,
with no change of variables or auxiliary occupancy assumption. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set
open scoped BigOperators

theorem preferredRightShell_mono_margin {n : ℕ} (d : PreferredBranchData)
    (B : PreferredCoareaBump d) {δ₁ δ₂ r : ℝ} (hδ : δ₁≤δ₂) (l : ℤ) (i a : Fin (n+1)) :
    preferredRightShell d B δ₁ r l i a⊆preferredRightShell d B δ₂ r l i a := by
  rintro x ⟨hx,hbox,hsum,hext,hr,hR⟩
  refine ⟨hx,?_,hsum,hext,hr,hR⟩
  intro v
  exact ⟨by linarith [(hbox v).1],(hbox v).2⟩

theorem preferredRightShell_diameter_lower {n : ℕ} (d : PreferredBranchData)
    (B : PreferredCoareaBump d) {δB r : ℝ} (hr : 0<r) {l : ℤ}
    {i a : Fin (n+1)} {x : Fin n → ℝ} (hx : x∈preferredRightShell d B δB r l i a) :
    r≤preferredAngularDiameter (preferredLiftedAngles B.delta (constrainedAngles x)) := by
  have hh := preferredAngularDiameter_pair_le (preferredLiftedAngles B.delta (constrainedAngles x)) a i
  have hp := hr.trans_le hx.2.2.2.2.1
  rw [abs_of_pos hp] at hh
  exact hx.2.2.2.2.1.trans hh

/-- Every nonempty actual shell has a fixed bounded T. This is used only
after transport and does not differentiate a diameter or an extremum. -/
theorem preferredRightShell_scale_upper {n : ℕ} (d : PreferredBranchData)
    (B : PreferredCoareaBump d) {δB r ε : ℝ} (hδB : δB<B.delta) (hε : ε≤1)
    {l : ℤ} {i a : Fin (n+1)} {x : Fin n → ℝ}
    (hx : x∈preferredRightShell d B δB r l i a) :
    preferredShellScale d (n+1) l r ε≤5*Real.pi+1 := by
  have hl := Finset.mem_Icc.mp (preferredRightShell_mean_mem d B hδB hx)
  have hN : (0:ℝ)<(n+1:ℕ) := by positivity
  have hlabs : |(l:ℝ)|≤((n+1:ℕ):ℝ) := by
    apply abs_le.mpr
    constructor
    · exact_mod_cast hl.1
    · exact_mod_cast hl.2
  have hquot : |2*Real.pi*(l:ℝ)/((n+1:ℕ):ℝ)|≤2*Real.pi := by
    rw [abs_div,abs_mul,abs_of_pos (by positivity : 0<2*Real.pi),abs_of_pos hN]
    apply (div_le_iff₀ hN).mpr
    exact mul_le_mul_of_nonneg_left hlabs (by positivity)
  have hmean : |preferredShellMean d (n+1) l|≤3*Real.pi := by
    calc
      _ ≤ |d.b|+|2*Real.pi*(l:ℝ)/((n+1:ℕ):ℝ)| := abs_add_le _ _
      _ ≤ d.b+2*Real.pi := by rw [abs_of_pos d.b_pos]; linarith
      _ ≤ 3*Real.pi := by linarith [d.b_lt]
  have hbox := hx.2.1
  have hr : r≤2*Real.pi := by
    have hlower := (hbox i).1
    have hupper := (hbox a).2
    have hdiam := hx.2.2.2.2.1
    linarith [B.branch_plateau,B.delta_b,d.b_lt]
  unfold preferredShellScale
  linarith

/-- One order-independent square-root cap follows from the exact shell. -/
theorem preferredRightShell_sqrt_scale_upper {n : ℕ} (d : PreferredBranchData)
    (B : PreferredCoareaBump d) {δB r ε : ℝ} (hδB : δB<B.delta) (hε : ε≤1)
    {l : ℤ} {i a : Fin (n+1)} {x : Fin n → ℝ}
    (hx : x∈preferredRightShell d B δB r l i a) :
    Real.sqrt (preferredShellScale d (n+1) l r ε)≤max 1 (Real.sqrt (5*Real.pi+1)) :=
  (Real.sqrt_le_sqrt (preferredRightShell_scale_upper d B hδB hε hx)).trans (le_max_right _ _)

end
end IsingBulk.Preferred22
