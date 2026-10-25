import IsingBulk.Joint.RegularEdges.FamilyFiniteAway

namespace IsingBulk.Joint.RegularEdges
noncomputable section
open Set Filter Metric MeasureTheory IsingBulk.First IsingBulk.Tail
open IsingBulk.Anisotropic.RegularEdges
open scoped Topology BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The entire angular complement has a common full-complex-disk jet bound. -/
theorem compact_family_complement_integral_bound {n : ℕ} {b : ℝ} (B S : ℂ × E → ℂ)
    (hb : |b|<1) {Q : Set E} (hQ : IsCompact Q)
    (hB : ∀eta∈Q,AnalyticAt ℂ B (0,eta)) (hBi : ∀eta∈Q,0<(B (0,eta)).im)
    (hS : ∀eta∈Q,AnalyticAt ℂ S (0,eta)) (hS0 : ∀eta∈Q,S (0,eta)≠0)
    {R : ℝ} (hR : 0<R) (j : ℕ) :
    ∃δ C : ℝ,0<δ ∧ 0≤C ∧ ∀eta∈Q,∀u : ℂ,‖u‖<δ →
      ‖edgeComplementDerivativeIntegral (n:=n) b (fun u=>B (u,eta)) (fun u=>S (u,eta)) j R u‖≤C := by
  let U : Set (Fin n→ℝ) := {q | ‖edgeFreeShape q‖<R/4}
  have hU : IsOpen U := isOpen_lt (edgeFreeShape_continuous n).norm continuous_const
  have h0 : (0:Fin n→ℝ)∈U := by simp [U]; positivity
  obtain ⟨δ,C,hδ,hC,hbound⟩ := compact_family_constrained_jet_bound B S hb hQ hB hBi hS hS0
    (L:=edgeCenteredCube n \ U) (isCompact_Icc.diff hU) (by
      intro eta heta q hq he
      have hz := ((edgeRootProduct_constrained_eq_one_iff hb (hBi eta heta) q
        (fun i=>⟨hq.1.1 i,hq.1.2 i⟩)).mp he).1
      exact hq.2 (hz ▸ h0)) j
  refine ⟨δ,(2*C)*volume.real (edgeCenteredCube n),hδ,by positivity,?_⟩
  intro eta heta u hu
  apply norm_setIntegral_le_of_norm_le_const isCompact_Icc.measure_lt_top
  intro q hq
  by_cases hqU : q∈U
  · have he : edgeShapeCutoff R (edgeFreeShape q)=1 := edgeShapeCutoff_eq_one hR (le_of_lt hqU)
    simp only [he,sub_self,zero_mul,norm_zero]
    positivity
  · rw [norm_mul]
    have hw : ‖1-edgeShapeCutoff R (edgeFreeShape q)‖≤2 := by
      calc
        _ ≤ ‖(1:ℂ)‖+‖edgeShapeCutoff R (edgeFreeShape q)‖ := norm_sub_le _ _
        _ ≤ 2 := by rw [norm_one]; linarith [(edgeShapeCutoff_properties (n:=n) hR).2.2.1 (edgeFreeShape q)]
    exact mul_le_mul hw (hbound eta heta u hu q ⟨hq,hqU⟩) (norm_nonneg _) (by norm_num)

end
end IsingBulk.Joint.RegularEdges
