import IsingBulk.Tail.SectorIntegralDecomposition
import IsingBulk.Tail.SectorPartitionSupport

/-! The actual named current has no all-branch term, identically in the
complex parameter and therefore at every parameter derivative order. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First MeasureTheory Set Filter
open scoped BigOperators Topology

theorem constructed_current_all_branch_zero {b eta : ℝ} (hb : 0 < b) (hbpi : b < Real.pi)
    (heta : 0 < eta) (hetasmall : eta ≤ Real.sin b/4) :
    ∃ outer0 : ℝ, 0 < outer0 ∧ ∀ outer : ℝ, ∀ ho : 0 < outer,
      outer ≤ outer0 → ∀ alpha : ℝ, 0 < alpha → alpha < Real.sin b/4 →
      ∀ N : ℕ, ∀ q : Fin N, ∀ r tau lam inner : ℝ, ∀ hi : 0 < inner,
        currentSectorIntegral N (constructedSelector b eta alpha) r tau lam q b outer inner ho hi none = 0 := by
  obtain ⟨outer0,ho0,hcover⟩ := current_named_sector_nonbranch hb hbpi heta hetasmall
  refine ⟨outer0,ho0,?_⟩
  intro outer ho hout alpha halpha hasmall N q r tau lam inner hi
  funext s
  change (∫ theta in angleBox N,
    namedCurrentMultiplier (constructedSelector b eta alpha) tau q theta *
      ((∏ i, sectorBranch b outer ho (theta i)):ℝ) *
        pulledDensity (constructedSelector b eta alpha) r tau lam s theta)=0
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro theta htheta
  by_cases hz : namedSelectorDerivative (constructedSelector b eta alpha) q theta=0
  · simp [namedCurrentMultiplier,hz]
  · have hnot := hcover outer ho hout alpha halpha hasmall N q theta htheta (subset_closure hz)
    have hq : sectorBranch b outer ho (theta q)=0 := by
      by_contra hq
      exact hnot (subset_closure hq)
    have hp : (∏ i, sectorBranch b outer ho (theta i))=0 :=
      Finset.prod_eq_zero (Finset.mem_univ q) hq
    rw [hp,Complex.ofReal_zero,mul_zero,zero_mul]

theorem constructed_current_all_branch_derivatives_zero {b eta : ℝ} (hb : 0 < b) (hbpi : b < Real.pi)
    (heta : 0 < eta) (hetasmall : eta ≤ Real.sin b/4) :
    ∃ outer0 : ℝ, 0 < outer0 ∧ ∀ outer : ℝ, ∀ ho : 0 < outer,
      outer ≤ outer0 → ∀ alpha : ℝ, 0 < alpha → alpha < Real.sin b/4 →
      ∀ N : ℕ, ∀ q : Fin N, ∀ r tau lam inner : ℝ, ∀ hi : 0 < inner, ∀ j : ℕ, ∀ s : ℂ,
        iteratedDeriv j (currentSectorIntegral N (constructedSelector b eta alpha)
          r tau lam q b outer inner ho hi none) s = 0 := by
  obtain ⟨outer0,ho0,hzero⟩ := constructed_current_all_branch_zero hb hbpi heta hetasmall
  refine ⟨outer0,ho0,?_⟩
  intro outer ho hout alpha halpha hasmall N q r tau lam inner hi j s
  rw [hzero outer ho hout alpha halpha hasmall N q r tau lam inner hi]
  simp

end
end IsingBulk.Tail
