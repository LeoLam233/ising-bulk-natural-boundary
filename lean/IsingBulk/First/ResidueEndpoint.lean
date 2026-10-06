import IsingBulk.First.ResidueAdmissibility
import IsingBulk.First.ResidueRegularity

/-! Source-facing residue endpoint on the manuscript's chosen admissible circle. -/
namespace IsingBulk.First
noncomputable section
open Set MeasureTheory

theorem source_pair_on_admissible_circle {r : ℝ} {s : ℂ} {z : ℂ → ℂ}
    (h : ScalarResidueAdmissible r s z) (a b : ℂ) (ha : ‖a‖=r) (hb : ‖b‖=r) :
    pairKernel (z a) (z b) * pairKernel a b =
      -(a-b)^2*z a*z b/(a*b*(1-z a*z b)^2) := by
  have ha0 : a ≠ 0 := by intro he; simp [he] at ha; linarith [h.radius_pos]
  have hb0 : b ≠ 0 := by intro he; simp [he] at hb; linarith [h.radius_pos]
  have hz0 := quadratic_root_ne_zero (residue_quadratic_eq (h.root_quadratic a ha))
  have hw0 := quadratic_root_ne_zero (residue_quadratic_eq (h.root_quadratic b hb))
  exact source_pair_identity ha0 hb0 hz0 hw0 (h.root_quadratic a ha) (h.root_quadratic b hb)
    (one_sub_mul_ne_zero_of_norm_lt_one (ha.trans_lt h.radius_lt_one) (hb.trans_lt h.radius_lt_one))
    (one_sub_mul_ne_zero_of_norm_lt_one ((h.root_inside a ha).trans h.radius_lt_one)
      ((h.root_inside b hb).trans h.radius_lt_one))

/-- The actual normalized residue theorem, the complete canceled pair, and
weighted integral existence all follow from the same genuine source domain. -/
theorem lemma_residue (N : ℕ) (hN : 0 < N) (r : ℝ) (s : ℂ) (z : ℂ → ℂ)
    (h : ScalarResidueAdmissible r s z) :
    doubleFormFactor N r s = reducedFormFactor N r z ∧
    (∀ a b : ℂ, ‖a‖=r → ‖b‖=r → pairKernel (z a) (z b)*pairKernel a b =
      -(a-b)^2*z a*z b/(a*b*(1-z a*z b)^2)) ∧
    ∀ w : (Fin N → ℝ) → ℝ, Continuous w →
      weightedDoubleFormFactor N r s w = weightedReducedFormFactor N r z w ∧
      IntegrableOn (weightedDoubleAngleDensity r s w) (angleBox N ×ˢ angleBox N) ∧
      IntegrableOn (weightedReducedAngleDensity r z w) (angleBox N) ∧
      AngleStagesIntegrable N (weightedReducedAngleDensity r z w) := by
  have ht : ∀ θ : Fin N → ℝ, ResidueAdmissible r s (angleTuple r θ)
      (fun i => z (anglePoint r (θ i))) := by
    intro θ
    apply h.toTuple N (angleTuple r θ)
    intro i
    exact anglePoint_norm h.radius_pos.le _
  refine ⟨residue_reduction N hN r h.radius_pos s z (h.toTuple N),
    source_pair_on_admissible_circle h, ?_⟩
  intro w hw
  have hi := residue_integrals_exist N hN r s z w hw ht
  exact ⟨weighted_residue_reduction N hN r s z w ht, hi.1, hi.2.2.2.1, hi.2.2.2.2⟩

end
end IsingBulk.First
