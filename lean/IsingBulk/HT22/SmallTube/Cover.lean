import IsingBulk.HT22.SmallTube.Mask
import IsingBulk.HT22.Geometry.SignedShellCover
namespace IsingBulk.HT22.SmallTube
noncomputable section
open Set MeasureTheory IsingBulk.Preferred22 IsingBulk.HT22.Tail IsingBulk.HT22.Geometry IsingBulk.HT22.Near
open scoped Topology ENNReal BigOperators
set_option backward.isDefEq.respectTransparency false

theorem smallMass_le_near_sum (b : PreferredBranchData) (B : PreferredCoareaBump b)
    (δ : ℝ) (hδ : δ < B.delta) (rcut : ℝ → ℝ)
    (hcut : PreferredRightCutoffData b B δ rcut) (j : ℕ) (a η : ℝ)
    (ha : |a| ≤ Real.pi) (n : ℕ) (ε τ R : ℝ) (hε : 0 ≤ ε) :
    (∫⁻ x : Fin (2*n+2) → ℝ in angularBox (2*n+2),
      smallMassIntegrand a (Complex.exp (-Complex.I*(η:ℂ))) b B τ rcut j
        (IsingBulk.Branch.radialParameter b.alpha ε) R x) ≤
      ∑ l : {l : ℤ // l∈preferredMeanIndices (2*n+3)}, ∑ i : Fin (2*n+3), ∑ k : Fin (2*n+3),
        nearPhysicalShellSum b B δ (Real.sqrt R) rcut j a η n ε τ l.1 i k := by
  rw [smallMass_lintegral_eq_signedRightRegion a _ b B rcut hcut]
  apply (signedRightRegion_lintegral_le_shells (by omega) a b B hδ ha _).trans
  calc
    _ ≤ ∑' m : ℕ, ∑ l : {l : ℤ // l∈preferredMeanIndices (2*n+3)},
        ∑ i : Fin (2*n+3), ∑ k : Fin (2*n+3),
        if dyadicScale (b.b+(a+2*Real.pi*(l.1:ℝ))/((2*n+3:ℕ):ℝ)) ε m≤Real.sqrt R
        then physicalShellMass b B δ rcut j a η n ε τ m l.1 i k else 0 := by
      apply ENNReal.tsum_le_tsum
      intro m
      apply Finset.sum_le_sum
      intro l _
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro k _
      exact smallMass_shell_le_near_mask b B δ rcut j a η n ε τ R hε hδ m l.1 i k
    _ = _ := by
      simp only [nearPhysicalShellSum, ← tsum_fintype (L := SummationFilter.unconditional _)]
      rw [ENNReal.tsum_comm]
      congr 1
      ext l
      rw [ENNReal.tsum_comm]
      congr 1
      ext i
      rw [ENNReal.tsum_comm]
end
end IsingBulk.HT22.SmallTube
