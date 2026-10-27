import IsingBulk.Preferred22.ShellObligations
import IsingBulk.Preferred22.CoordinateShell
import IsingBulk.Preferred22.RightCoarea

/-! Exact constrained-mean and diameter geometry of the actual lifted
right shells. -/
namespace IsingBulk.Preferred22
noncomputable section
open scoped BigOperators Topology
open Set

/-- A single explicit finite set contains every constrained mean of a
nonempty actual right shell. -/
def preferredMeanIndices (N : ℕ) : Finset ℤ := Finset.Icc (-(N:ℤ)) (N:ℤ)

theorem preferredMeanIndices_card (N : ℕ) :
    (preferredMeanIndices N).card = 2*N+1 := by
  simp only [preferredMeanIndices,Int.card_Icc]
  omega

theorem preferredMeanIndices_card_le {N : ℕ} (hN : 0 < N) :
    (preferredMeanIndices N).card ≤ 3*N := by
  rw [preferredMeanIndices_card]
  omega

/-- The mean bound follows from the literal constrained sum and the actual
right-rectangle angular support. It is uniform before the diameter. -/
theorem preferredRightShell_mean_mem {n : ℕ} (d : PreferredBranchData)
    (B : PreferredCoareaBump d) {δB r : ℝ} (hδB : δB < B.delta)
    {l : ℤ} {i j : Fin (n+1)} {θ : Fin n → ℝ}
    (hθ : θ ∈ preferredRightShell d B δB r l i j) :
    l ∈ preferredMeanIndices (n+1) := by
  obtain ⟨_,hbox,hsum,_,_,_⟩ := hθ
  let w := preferredLiftedAngles B.delta (constrainedAngles θ)
  have hw (v : Fin (n+1)) : -Real.pi ≤ w v ∧ w v ≤ Real.pi := by
    have hv := hbox v
    constructor <;> linarith [hv.1,hv.2,B.branch_plateau,B.delta_b,d.b_lt]
  have hlow : -(n+1:ℝ)*Real.pi ≤ 2*Real.pi*(l:ℝ) := by
    have hh := Finset.sum_le_sum (fun v (_ : v ∈ Finset.univ) => (hw v).1)
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hh
    change ((n+1:ℕ):ℝ)*(-Real.pi) ≤ ∑ v, w v at hh
    change (∑ v, w v)=2*Real.pi*(l:ℝ) at hsum
    rw [hsum] at hh
    push_cast at hh
    nlinarith only [hh]
  have hupp : 2*Real.pi*(l:ℝ) ≤ (n+1:ℝ)*Real.pi := by
    have hh := Finset.sum_le_sum (fun v (_ : v ∈ Finset.univ) => (hw v).2)
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hh
    change (∑ v, w v) ≤ ((n+1:ℕ):ℝ)*Real.pi at hh
    change (∑ v, w v)=2*Real.pi*(l:ℝ) at hsum
    rw [hsum] at hh
    push_cast at hh
    exact hh
  have hNπ : 0 ≤ (n+1:ℝ)*Real.pi := by positivity
  have hlo : -(n+1:ℝ) ≤ (l:ℝ) := by
    apply le_of_mul_le_mul_left (a := 2*Real.pi) _ (by positivity)
    nlinarith only [hlow,hNπ]
  have hhi : (l:ℝ) ≤ (n+1:ℝ) := by
    apply le_of_mul_le_mul_left (a := 2*Real.pi) _ (by positivity)
    nlinarith only [hupp,hNπ]
  apply Finset.mem_Icc.mpr
  constructor
  · exact_mod_cast hlo
  · exact_mod_cast hhi

/-- Every actual coordinate in a shell lies in the fixed-mean window used
for q22 and q23. The extrema are selected only after all transport. -/
theorem preferredRightShell_window {n : ℕ} (d : PreferredBranchData)
    (B : PreferredCoareaBump d) {δB r : ℝ} {l : ℤ} {i j : Fin (n+1)}
    {θ : Fin n → ℝ} (hθ : θ ∈ preferredRightShell d B δB r l i j) :
    ∀ v : Fin (n+1),
      preferredShellMean d (n+1) l-2*r ≤ preferredLiftedAngles B.delta (constrainedAngles θ) v+d.b ∧
      preferredLiftedAngles B.delta (constrainedAngles θ) v+d.b ≤ preferredShellMean d (n+1) l+2*r := by
  obtain ⟨_,_,hsum,hext,_,hd⟩ := hθ
  let w := preferredLiftedAngles B.delta (constrainedAngles θ)
  have hmean : (∑ v, (w v+d.b)) = ((n+1:ℕ):ℝ)*preferredShellMean d (n+1) l := by
    rw [Finset.sum_add_distrib]
    change (∑ v, w v)=2*Real.pi*(l:ℝ) at hsum
    rw [hsum]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,preferredShellMean]
    have hN : ((n+1:ℕ):ℝ) ≠ 0 := by positivity
    field_simp
    ring
  apply constrained_shell_coordinate_window (i := i) (j := j) (Nat.succ_pos n) hmean
  · intro v
    have hv := hext v
    constructor <;> linarith [hv.1,hv.2]
  · linarith

/-- The phase-scale upper endpoint is controlled by twice the literal
fixed mean scale, uniformly even when the mean crosses the branch. -/
theorem preferredRightShell_max_scale {n : ℕ} (d : PreferredBranchData)
    (B : PreferredCoareaBump d) {δB r ε : ℝ} (hε : 0 ≤ ε) {l : ℤ}
    {i j : Fin (n+1)} {θ : Fin n → ℝ}
    (hθ : θ ∈ preferredRightShell d B δB r l i j) :
    preferredLiftedAngles B.delta (constrainedAngles θ) j+d.b+ε ≤
      2*preferredShellScale d (n+1) l r ε := by
  have hw := (preferredRightShell_window d B hθ j).2
  unfold preferredShellScale
  linarith [le_abs_self (preferredShellMean d (n+1) l),
    abs_nonneg (preferredShellMean d (n+1) l)]


/-- Both q23 estimates, now attached to the literal constrained angular
shell used in the actual transported-density obligation. -/
theorem preferredRightShell_coordinate_scales (d : PreferredBranchData)
    (B : PreferredCoareaBump d) :
    ∃ C ε₀ τ₀ δB : ℝ, 0 < C ∧ 0 < ε₀ ∧ 0 < τ₀ ∧ 0 < δB ∧ δB < B.delta ∧
      ∀ n : ℕ, ∀ ε τ r : ℝ, 0 < ε → ε < ε₀ → 0 ≤ τ → τ < τ₀ → 0 < r →
      ∀ l : ℤ, ∀ i j : Fin (n+1), ∀ θ : Fin n → ℝ,
      θ ∈ preferredRightShell d B δB r l i j →
      let w := preferredLiftedAngles B.delta (constrainedAngles θ)
      let q := preferredSourceCoordinate τ B.p B.m (IsingBulk.Branch.radialParameter d.alpha ε) w
      ∀ a : Fin (n+1),
        ‖q a‖ ≤ C*Real.sqrt (preferredShellScale d (n+1) l r ε) ∧
        ∀ v : Fin (n+1), ‖q a-q v‖ ≤ C*r/Real.sqrt (preferredShellScale d (n+1) l r ε) := by
  obtain ⟨Ca,εa,τa,δa,hCa,hεa,hτa,hδa,hδaδ,ha⟩ := preferred_actual_coordinate_absolute_scale d B
  obtain ⟨Cd,εd,τd,δd,hCd,hεd,hτd,hδd,_,hd⟩ := preferred_actual_coordinate_difference d B
  let δB := min δa δd
  refine ⟨Ca+Cd,min εa εd,min τa τd,δB,by positivity,lt_min hεa hεd,
    lt_min hτa hτd,lt_min hδa hδd,(min_le_left _ _).trans_lt hδaδ,?_⟩
  intro n ε τ r hε hεr hτ hτr hr l i j θ hθ
  let w := preferredLiftedAngles B.delta (constrainedAngles θ)
  let q := preferredSourceCoordinate τ B.p B.m (IsingBulk.Branch.radialParameter d.alpha ε) w
  change ∀ a : Fin (n+1), ‖q a‖ ≤ _ ∧ ∀ v : Fin (n+1), ‖q a-q v‖ ≤ _
  have hbox := hθ.2.1
  have hδBa : δB ≤ δa := min_le_left _ _
  have hδBd : δB ≤ δd := min_le_right _ _
  have hboxa (v : Fin (n+1)) : -δa ≤ w v+d.b ∧ w v+d.b ≤ d.b+B.delta := by
    have hv := hbox v
    constructor <;> linarith [hv.1,hv.2,hδBa]
  have hboxd (v : Fin (n+1)) : -δd ≤ w v+d.b ∧ w v+d.b ≤ d.b+B.delta := by
    have hv := hbox v
    constructor <;> linarith [hv.1,hv.2,hδBd]
  have hwindow := preferredRightShell_window d B hθ
  have hqa := ha (n+1) (Nat.succ_pos n) ε τ (preferredShellMean d (n+1) l) r hε
    (hεr.trans_le (min_le_left _ _)) hτ (hτr.trans_le (min_le_left _ _)) hr w hboxa hwindow
  have hqd := hd (n+1) (Nat.succ_pos n) ε τ (preferredShellMean d (n+1) l) r hε
    (hεr.trans_le (min_le_right _ _)) hτ (hτr.trans_le (min_le_right _ _)) hr w hboxd hwindow
  intro a
  constructor
  · exact (hqa a).trans (mul_le_mul_of_nonneg_right (by linarith : Ca ≤ Ca+Cd) (Real.sqrt_nonneg _))
  · intro v
    exact (hqd a v).trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith : Cd ≤ Ca+Cd) hr.le) (Real.sqrt_nonneg _))

end
end IsingBulk.Preferred22
