import IsingBulk.HT22.Tail.PunctureMass
import IsingBulk.HT22.Near.ActualDyadicSum
namespace IsingBulk.HT22.SmallTube
noncomputable section
open Set MeasureTheory IsingBulk.Preferred22 IsingBulk.HT22.Tail IsingBulk.HT22.Geometry IsingBulk.HT22.Near
open scoped Topology ENNReal BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The actual regular scale is at most sqrt of the angular shell radius,
uniformly in the signed mean and positive physical epsilon. -/
theorem coordinateScale_le_sqrt_radius (μ : ℝ) {r ε : ℝ} (hr : 0<r) (hε : 0≤ε) :
    shellCoordinateScale μ r ε≤Real.sqrt r := by
  unfold shellCoordinateScale
  have hT : 0 < |μ| + r + ε := by positivity
  rw [div_le_iff₀ (Real.sqrt_pos.mpr hT)]
  calc
    r = Real.sqrt r*Real.sqrt r := (Real.mul_self_sqrt hr.le).symm
    _ ≤ Real.sqrt r*Real.sqrt (|μ|+r+ε) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith [abs_nonneg μ])) (Real.sqrt_nonneg r)

theorem signedRightShell_radius_le_diameter {n : ℕ} (a : ℝ) (d : PreferredBranchData)
    (B : PreferredCoareaBump d) (δ r : ℝ) (l : ℤ) (i k : Fin (n+1))
    {θ : Fin n → ℝ} (hθ : θ∈signedRightShell a d B δ r l i k) :
    r≤preferredAngularDiameter (preferredLiftedAngles B.delta (constrainedAtTotal a θ)) := by
  have hpair := preferredAngularDiameter_pair_le
    (preferredLiftedAngles B.delta (constrainedAtTotal a θ)) k i
  exact hθ.2.1.2.2.1.trans ((le_abs_self _).trans hpair)

/-- The original full small-tube mask is subordinate to the actual near
scale mask on every shell. This uses the shell's real extreme particles. -/
theorem smallMass_shell_le_near_mask (b : PreferredBranchData) (B : PreferredCoareaBump b)
    (δ : ℝ) (rcut : ℝ → ℝ) (j : ℕ) (a η : ℝ) (n : ℕ) (ε τ R : ℝ)
    (hε : 0≤ε) (hδ : δ < B.delta) (m : ℕ) (l : ℤ) (i k : Fin (2*n+3)) :
    (∫⁻ x in signedRightShell a b B δ (preferredDyadicRadius m) l i k,
      smallMassIntegrand a (Complex.exp (-Complex.I*(η:ℂ))) b B τ rcut j
        (IsingBulk.Branch.radialParameter b.alpha ε) R x)≤
      if dyadicScale (b.b+(a+2*Real.pi*(l:ℝ))/((2*n+3:ℕ):ℝ)) ε m≤Real.sqrt R
      then physicalShellMass b B δ rcut j a η n ε τ m l i k else 0 := by
  by_cases hscale : dyadicScale (b.b+(a+2*Real.pi*(l:ℝ))/((2*n+3:ℕ):ℝ)) ε m≤Real.sqrt R
  · rw [ite_eq_left hscale]
    apply lintegral_mono
    intro x
    unfold smallMassIntegrand
    dsimp only
    split_ifs
    · exact le_rfl
    · exact bot_le
  · rw [ite_eq_right hscale]
    apply le_of_eq
    apply lintegral_eq_zero_of_ae_eq_zero
    apply ae_restrict_of_forall_mem (signedRightShell_isClosed a b B hδ _ l i k).measurableSet
    intro x hx
    unfold smallMassIntegrand
    have hrad := signedRightShell_radius_le_diameter a b B δ (preferredDyadicRadius m) l i k hx
    have hnot : ¬preferredAngularDiameter (preferredLiftedAngles B.delta (constrainedAtTotal a x))≤R := by
      intro hh
      apply hscale
      exact (coordinateScale_le_sqrt_radius _ (preferredDyadicRadius_pos m) hε).trans
        (Real.sqrt_le_sqrt (hrad.trans hh))
    dsimp only
    simp only [ite_eq_right hnot, Pi.zero_apply]
end
end IsingBulk.HT22.SmallTube
