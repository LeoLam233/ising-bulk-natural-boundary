import IsingBulk.Tail.AllBranchExteriorAngularWindow
import Mathlib.Data.Finset.Lattice.Fold

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Branch Filter
open scoped Topology BigOperators

/-- All derivative orders use the same angular width, microcore scale,
and equality scale. No parameter is chosen after N or the radial limit. -/
theorem allBranchExterior_angular_window_finite {d : LocalBranchData}
    (B : BranchEstimates d) (hcsmall : d.c₀ < Real.sin d.theta/2)
    (hα : d.alpha < Real.sin d.thetaB/4) (J : ℕ) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ η δ : ℝ, ∀ hδ : 0 < δ, δ ≤ δ₀ →
      ∀ Aμ cμ : ℝ, 0 ≤ Aμ → 0 < cμ → cμ ≤ 1 →
      ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β : ℝ, β₀ ≤ β → ∀ j : ℕ, j ≤ J →
      ∃ S : ℕ → ℝ, Summable S ∧ (∀ N, 0 ≤ S N) ∧
      ∀ Dwin : ℝ, 0 ≤ Dwin → ∀ᶠ H : ℝ in atTop, ∀ n : ℕ,
        (n+1:ℝ) ≤ Dwin*Real.sqrt H → 2*j+1 ≤ (n+1)*n →
        allBranchExteriorAngularNorm (n+1) d η δ (Real.exp (-H))
          (allBranchMicroRadius Aμ cμ (n+1)) (allBranchEqualityRadius β (n+1)) hδ j
          ≤ S (n+1)*(H+1)^2 := by
  have hh := fun j : Fin (J+1) => allBranchExterior_angular_window B hcsmall hα j.val
  choose δ hδ hwindow using hh
  let δ₀ : ℝ := Finset.univ.inf' Finset.univ_nonempty δ
  have hδ₀ : 0 < δ₀ := (Finset.lt_inf'_iff Finset.univ_nonempty).mpr (fun j _ => hδ j)
  have hδle (j : Fin (J+1)) : δ₀ ≤ δ j := Finset.inf'_le _ (Finset.mem_univ j)
  refine ⟨δ₀,hδ₀,?_⟩
  intro η δ' hδ' hδsmall Aμ cμ hAμ hcμ hcμ1
  have hh := fun j : Fin (J+1) => hwindow j η δ' hδ' (hδsmall.trans (hδle j)) Aμ cμ hAμ hcμ hcμ1
  choose β hβ hbound using hh
  let β₀ : ℝ := ∑ j, β j
  have hβle (j : Fin (J+1)) : β j ≤ β₀ :=
    Finset.single_le_sum (fun i _ => (hβ i).le) (Finset.mem_univ j)
  refine ⟨β₀,(hβ 0).trans_le (hβle 0),?_⟩
  intro β' hβ' j hj
  exact hbound ⟨j,by omega⟩ β' ((hβle ⟨j,by omega⟩).trans hβ')

end
end IsingBulk.Tail
