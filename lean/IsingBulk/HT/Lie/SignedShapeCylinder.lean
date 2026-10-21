import IsingBulk.HT.Lie.SignedShapeFlux
import Mathlib.Data.Finset.Lattice.Fold

/-! The center coordinate is integrated last. A uniform bound derived from
the full physical chart controls the literal center-cylinder side flux,
including the branch center c=0; no dominated-convergence premise is needed. -/
namespace IsingBulk.HT.Lie
noncomputable section
open IsingBulk.Branch IsingBulk.Lie IsingBulk.Tail Filter Set MeasureTheory
open scoped Topology

def shapeCylinderFlux {n : ℕ} (center : Fin (n+2)) (r ρ : ℝ)
    (F : (Fin (n+2) → ℝ) → Fin (n+2) → ℂ) : ℂ :=
  ∫ c in Icc (-r/2) (r/2), shapeCubeFlux center c ρ F

/-- Actual signed surface integral, including its retained center measure. -/
theorem signed_shape_cylinder_flux_vanishes {d : LocalBranchData} (B : BranchEstimates d)
    (hcsmall : d.c₀ < Real.sin d.theta/2) (M j : ℕ) (hM : 2*j+2 < M) :
    ∃ r : ℝ, 0 < r ∧ ∀ ε : ℝ, 0 < ε → ε ≤ r → ∀ α : ℝ,
      ∀ n : ℕ, 2*j+1 ≤ (n+2)*(n+1) →
      0 < ((n+2)*(n+1)-(2*j+1))+n → ∀ p q : Fin (n+2), p ≠ q →
      ∀ center : Fin (n+2),
      Tendsto (fun ρ => shapeCylinderFlux center r ρ
        (signedOriginalFlux (Complex.exp (Complex.I*(α:ℂ))) d ε M j p q))
        (𝓝[>] (0:ℝ)) (𝓝 0) := by
  obtain ⟨r,hr,hbound⟩ := signed_shape_flux_power_bound B hcsmall M j hM
  refine ⟨r,hr,?_⟩
  intro ε hε hεr α n horder hpower p q hpq center
  obtain ⟨C,hC,hflux⟩ := hbound ε hε hεr α n horder p q hpq center
  let S := Icc (-r/2) (r/2)
  apply flux_tendsto_zero_of_power_bound _ (fun ρ => ρ) (C*volume.real S)
    (((n+2)*(n+1)-(2*j+1))+n) hpower continuousWithinAt_id
  filter_upwards [hflux] with ρ hρ
  have hh : ‖shapeCylinderFlux center r ρ
      (signedOriginalFlux (Complex.exp (Complex.I*(α:ℂ))) d ε M j p q)‖ ≤
      (C*ρ^(((n+2)*(n+1)-(2*j+1))+n))*volume.real S := by
    apply norm_setIntegral_le_of_norm_le_const (μ := volume) isCompact_Icc.measure_lt_top
    intro c hc
    exact hρ c (abs_le.mpr ⟨by linarith [hc.1],hc.2⟩)
  exact hh.trans_eq (by ring)

/-- The relative-coordinate face exponent is exactly the manuscript
`N^2 - 2j - 3`, with `N = n + 2`; natural subtraction does not truncate
the density exponent under the displayed order hypothesis. -/
theorem shape_flux_power_eq_manuscript (n j : ℕ)
    (horder : 2*j+1 ≤ (n+2)*(n+1)) :
    ((n+2)*(n+1)-(2*j+1))+n = (n+2)^2-(2*j+3) := by
  have hdim : (n+2)^2 = (n+2)*(n+1)+n+2 := by ring
  omega

/-- All earlier Lie stages have vanishing genuine cylinder flux on one
common geometric neighborhood. The radius is fixed before epsilon, the
signed phase, the particle number, the selected pair and the stage.
The puncture limit is still taken at fixed epsilon and particle number,
as required by the frozen manuscript. -/
theorem ht_shape_cylinder_flux_vanishes_finite {d : LocalBranchData}
    (B : BranchEstimates d) (hcsmall : d.c₀ < Real.sin d.theta/2)
    (M p k : ℕ) (hp : 1 ≤ p) (hk : k ≤ (p^2-1)/2) (hM : 2*k+2 < M) :
    ∃ r : ℝ, 0 < r ∧ ∀ ε : ℝ, 0 < ε → ε ≤ r → ∀ α : ℝ,
      ∀ n : ℕ, p+2 ≤ n+2 → ∀ j : ℕ, j ≤ k →
      ∀ a b : Fin (n+2), a ≠ b → ∀ center : Fin (n+2),
      Tendsto (fun ρ => shapeCylinderFlux center r ρ
        (signedOriginalFlux (Complex.exp (Complex.I*(α:ℂ))) d ε M j a b))
        (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hMs (j : Fin (k+1)) : 2*j.val+2 < M := by
    have hj := j.isLt
    omega
  have hh := fun j : Fin (k+1) =>
    signed_shape_flux_power_bound B hcsmall M j.val (hMs j)
  choose R hR hbound using hh
  let r : ℝ := Finset.univ.inf' Finset.univ_nonempty R
  have hr : 0 < r :=
    (Finset.lt_inf'_iff Finset.univ_nonempty).mpr (fun j _ => hR j)
  have hrle (j : Fin (k+1)) : r ≤ R j :=
    Finset.inf'_le _ (Finset.mem_univ j)
  refine ⟨r,hr,?_⟩
  intro ε hε hεr α n hN j hj a b hab center
  let jj : Fin (k+1) := ⟨j,by omega⟩
  have horder : 2*j+1 ≤ (n+2)*(n+1) := by
    have ho := exterior_source_degree (N := n+2) hp hN (hj.trans hk)
    simpa only [show n+2-1=n+1 by omega] using ho
  have hn : 0 < n := by omega
  have hpower : 0 < ((n+2)*(n+1)-(2*j+1))+n := by omega
  obtain ⟨C,hC,hflux⟩ := hbound jj ε hε (hεr.trans (hrle jj)) α n
    horder a b hab center
  let S := Icc (-r/2) (r/2)
  apply flux_tendsto_zero_of_power_bound _ (fun ρ => ρ) (C*volume.real S)
    (((n+2)*(n+1)-(2*j+1))+n) hpower continuousWithinAt_id
  filter_upwards [hflux] with ρ hρ
  have hnorm : ‖shapeCylinderFlux center r ρ
      (signedOriginalFlux (Complex.exp (Complex.I*(α:ℂ))) d ε M j a b)‖ ≤
      (C*ρ^(((n+2)*(n+1)-(2*j+1))+n))*volume.real S := by
    apply norm_setIntegral_le_of_norm_le_const (μ := volume) isCompact_Icc.measure_lt_top
    intro c hc
    apply hρ c
    have hcr : |c| ≤ r/2 := abs_le.mpr ⟨by linarith [hc.1],hc.2⟩
    have hRj := hrle jj
    linarith
  exact hnorm.trans_eq (by ring)

end
end IsingBulk.HT.Lie
