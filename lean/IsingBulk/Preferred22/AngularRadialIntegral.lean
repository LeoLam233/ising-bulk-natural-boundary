import IsingBulk.Preferred22.CompactRadialIntegral

/-! The compact derivative theorem on the unchanged angular Haar box. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set MeasureTheory
open scoped BigOperators Topology ContDiff

/-- The exact physical angular box differs from its compact closure only
on a null set, so the compact parameter derivative theorem applies. -/
theorem preferred_angular_radial_integral_hasDerivAt {n : ℕ}
    (F : ℝ × (Fin n → ℝ) → ℂ) {a b t : ℝ} (ht : t∈Ioo a b)
    (hF : ∀ u∈Ioo a b,∀ x,ContDiffAt ℝ ∞ F (u,x)) :
    HasDerivAt (fun u : ℝ => ∫ x in angularBox n,F (u,x))
      (∫ x in angularBox n,fderiv ℝ F (t,x) (1,0)) t := by
  let K : Set (Fin n → ℝ) := pi univ (fun _ => Icc (-Real.pi) Real.pi)
  have hK : IsCompact K := isCompact_univ_pi (fun _ => isCompact_Icc)
  have hbox : angularBox n=ᵐ[volume] K := Measure.pi_Ioc_ae_eq_pi_Icc
  have hh := preferred_compact_radial_integral_hasDerivAt K hK F ht
    (fun u hu x _ => hF u hu x)
  convert hh using 1
  · funext u
    exact setIntegral_congr_set hbox
  · exact setIntegral_congr_set hbox

end
end IsingBulk.Preferred22
