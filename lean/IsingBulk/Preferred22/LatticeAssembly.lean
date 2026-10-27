import IsingBulk.Preferred22.PhysicalBranches
import Mathlib.Topology.Algebra.InfiniteSum.Constructions

/-! Precise physical-lattice obligations and their logical assembly. The
unproved Fourier/Fubini obligation is internal mathematics, never part of the
published Palmer--Tracy/Yang interfaces. Both pure phases and the origin are
included by the literal full Z×Z sum. -/
namespace IsingBulk.Preferred22
noncomputable section
open Complex Set

/-- Remaining Proposition 2.1 Fourier/Fubini obligation for the actual site
coefficients. Absolute summability is over the joint particle/site index. -/
def PreferredLatticeFubiniStatement : Prop :=
  ∀ x : ℝ, 1 < x →
    Summable (fun q : ℕ × (ℤ × ℤ) =>
      ‖siteCoefficient (2*(q.1+1)) q.2.1 q.2.2 (x:ℂ)‖) ∧
    ∀ n : ℕ, (∑' ab : ℤ × ℤ,siteCoefficient (2*(n+1)) ab.1 ab.2 (x:ℂ))=
      coefficient (2*(n+1)) (x:ℂ)

theorem connectedLatticeSum_eq_bulk_of_fubini
    (hF : PreferredLatticeFubiniStatement)
    {correlation : ℝ → ℤ → ℤ → ℂ} {M : ℝ → ℂ}
    (hPT : PalmerTracyInput correlation M) (hYang : YangInput M)
    {x : ℝ} (hx : 1 < x) :
    connectedLatticeSum correlation M x=bulkFunction (x:ℂ) := by
  obtain ⟨habs,hcoeff⟩ := hF x hx
  have hs := habs.of_norm
  unfold connectedLatticeSum
  have hsite : (fun ab : ℤ × ℤ => correlation x ab.1 ab.2-M x)=
      (fun ab : ℤ × ℤ => M x*(∑' n : ℕ,siteCoefficient (2*(n+1)) ab.1 ab.2 (x:ℂ))) :=
    funext (fun ab => connected_site_of_PalmerTracy hPT hx ab.1 ab.2)
  rw [hsite]
  rw [tsum_mul_left,hs.tsum_comm]
  simp_rw [hcoeff]
  rw [hYang x hx]
  rfl

theorem connectedLattice_absolute_of_fubini
    (hF : PreferredLatticeFubiniStatement)
    {correlation : ℝ → ℤ → ℤ → ℂ} {M : ℝ → ℂ}
    (hPT : PalmerTracyInput correlation M) {x : ℝ} (hx : 1 < x) :
    Summable (fun ab : ℤ × ℤ => ‖correlation x ab.1 ab.2-M x‖) := by
  have habs := (hF x hx).1
  apply (habs.prod_symm.prod.mul_left ‖M x‖).of_nonneg_of_le
    (fun _ => norm_nonneg _)
  intro ab
  rw [connected_site_of_PalmerTracy hPT hx,norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm (habs.prod_symm.prod_factor ab))
    (norm_nonneg _)

/-- Exactly the permitted real-temperature interfaces in both pure phases.
There is no assumed bulk identity, tail bound or complex continuation. -/
def PublishedPhysicalInputs (correlation : Bool → ℝ → ℤ → ℤ → ℂ)
    (M : ℝ → ℂ) : Prop :=
  YangInput M ∧ ∀ phase : Bool, PalmerTracyInput (correlation phase) M

def PreferredFullTarget : Prop :=
  PreferredLatticeFubiniStatement ∧
  (∀ (correlation : Bool → ℝ → ℤ → ℤ → ℂ) (M : ℝ → ℂ),
    PublishedPhysicalInputs correlation M → ∀ phase : Bool, ∀ x : ℝ, 1 < x →
      Summable (fun ab : ℤ × ℤ => ‖correlation phase x ab.1 ab.2-M x‖) ∧
      connectedLatticeSum (correlation phase) M x=bulkFunction (x:ℂ)) ∧
  AnalyticOnNhd ℂ bulkFunction {s : ℂ | 1 < ‖s‖} ∧
  (∀ ζ : ℂ, ‖ζ‖=1 → ¬ HasExteriorExtension bulkFunction ζ) ∧
  (∀ J : ℝ, 0 < J → ∀ ζ : ℂ, ‖ζ‖=1 →
    ¬ HasPhysicalBoundaryExtension J bulkFunction ζ)

/-- CONDITIONAL ASSEMBLY. This theorem exposes the two remaining mathematical
inputs in its type. It is not an unconditional proof of PreferredFullTarget. -/
theorem preferredFullTarget_of_obligations
    (hF : PreferredLatticeFubiniStatement)
    (hselected : PreferredSelectedAnalyticObligations) : PreferredFullTarget := by
  refine ⟨hF,?_,fun _ hs => bulkFunction_analyticAt hs,
    bulkFunction_boundary_of_selected_obligations hselected,?_⟩
  · intro correlation M hInputs phase x hx
    exact ⟨connectedLattice_absolute_of_fubini hF (hInputs.2 phase) hx,
      connectedLatticeSum_eq_bulk_of_fubini hF (hInputs.2 phase) hInputs.1 hx⟩
  · intro J hJ
    exact physical_bulk_boundary_of_selected_obligations hselected hJ

end
end IsingBulk.Preferred22
