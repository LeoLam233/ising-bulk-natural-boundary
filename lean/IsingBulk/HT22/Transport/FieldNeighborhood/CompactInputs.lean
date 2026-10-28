import IsingBulk.HT22.Transport.FieldNeighborhood.ActualDomain

/-! # Original partial jet constants from a compact actual inverse branch

One compact inverse-domain set supplies the constants before particle
number, diameter, and derivative order of the residual field are selected.
-/
namespace IsingBulk.HT22
noncomputable section
open Geometry

/-- Compactness supplies precisely the original one-body bounds needed by
the true source ball theorem; none of these functions is a residual field. -/
theorem sourceInversePartials_compact_bound (K : Set (ℂ × ℂ)) (hK : IsCompact K)
    (hU : ∀ z∈K, AnalyticAt ℂ (fun p : ℂ × ℂ => regularInverse p.1 p.2) z) :
    ∃ C : ℝ, 0<C ∧ ∀ z∈K,
      ‖sourceInverseT z.1 z.2‖≤C ∧
      ‖fderiv ℂ (fun p : ℂ × ℂ => sourceInverseV p.1 p.2) z‖≤C ∧
      ‖fderiv ℂ (fun p : ℂ × ℂ => sourceInverseT p.1 p.2) z‖≤C := by
  have hTa : AnalyticOnNhd ℂ (fun p : ℂ × ℂ => sourceInverseT p.1 p.2) K :=
    fun z hz => inverseT_joint_analytic z.1 z.2 (hU z hz)
  have hVa : AnalyticOnNhd ℂ (fun p : ℂ × ℂ => sourceInverseV p.1 p.2) K :=
    fun z hz => inverseV_joint_analytic z.1 z.2 (hU z hz)
  obtain ⟨A,hA⟩ := hK.exists_bound_of_continuousOn
    (fun z hz => (hTa z hz).continuousAt.continuousWithinAt)
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn
    (fun z hz => (hVa z hz).fderiv.continuousAt.continuousWithinAt)
  obtain ⟨D,hD⟩ := hK.exists_bound_of_continuousOn
    (fun z hz => (hTa z hz).fderiv.continuousAt.continuousWithinAt)
  refine ⟨max 1 (max A (max B D)), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro z hz
  exact ⟨(hA z hz).trans ((le_max_left _ _).trans (le_max_right _ _)),
    (hB z hz).trans ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))),
    (hD z hz).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))⟩

end
end IsingBulk.HT22
