import IsingBulk.Joint.Transverse.FamilyNormalization
namespace IsingBulk.Joint.Transverse
noncomputable section
open Set Filter Metric
open scoped Topology
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- Shrinking a genuine common inverse preserves both inverse identities. -/
def FamilyNormalization.restrictRadius {f : ℂ × E→ℂ} {eta₀ : E}
    (N : FamilyNormalization f eta₀) (r : ℝ) (hr : 0<r) (hrN : r≤N.radius) :
    FamilyNormalization f eta₀ where
  inverse := N.inverse
  radius := r
  radius_pos := hr
  analytic := fun u eta hu heta=>N.analytic u eta (hu.trans_le hrN) (heta.trans_le hrN)
  center := fun eta heta hz=>N.center eta (heta.trans_le hrN) hz
  right_inv := fun u eta hu heta=>N.right_inv u eta (hu.trans_le hrN) (heta.trans_le hrN)
  left_inv := fun z eta hz heta=>N.left_inv z eta (hz.trans_le hrN) (heta.trans_le hrN)

/-- The inverse disk can simultaneously lie in the original family's analytic
center neighborhood. This is an internally constructed local common radius. -/
theorem exists_familyNormalization_with_analytic_centers {f : ℂ × E→ℂ}
    (curve : ℂ × E→Coupling) {eta₀ : E} (hc : AnalyticAt ℂ curve (0,eta₀))
    (hf : AnalyticAt ℂ f (0,eta₀)) (hzero : f (0,eta₀)=0)
    (hd : deriv (fun z=>f (z,eta₀)) 0≠0) :
    ∃N : FamilyNormalization f eta₀,∀eta,‖eta-eta₀‖<N.radius →
      AnalyticAt ℂ curve (0,eta) := by
  obtain ⟨N⟩ := exists_familyNormalization hf hzero hd
  have hmap : ContinuousAt (fun eta : E=>((0:ℂ),eta)) eta₀ :=
    continuousAt_const.prodMk continuousAt_id
  have hev : ∀ᶠeta in 𝓝 eta₀,AnalyticAt ℂ curve (0,eta) :=
    hmap.tendsto.eventually hc.eventually_analyticAt
  obtain ⟨r,hr,hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨N.restrictRadius (min N.radius r) (lt_min N.radius_pos hr) (min_le_left _ _),?_⟩
  intro eta heta
  exact hball (by simpa only [dist_eq_norm] using heta.trans_le (min_le_right _ _))

end
end IsingBulk.Joint.Transverse
