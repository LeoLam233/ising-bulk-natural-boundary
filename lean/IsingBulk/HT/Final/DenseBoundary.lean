import IsingBulk.Final.DenseBoundary

/-! Dense-boundary propagation suitable for HT: no evenness hypothesis.
HT requires its independently obstructed positive and negative upper families;
only conjugation is used to reach the lower semicircle. -/
namespace IsingBulk.HT.Final
noncomputable section
open Set Filter IsingBulk.Final
open scoped Topology

/-- Obstructions dense on both upper quadrants and real conjugation suffice.
The density and selected obstructions are explicit hypotheses of this general
transport lemma; no HT estimates are assumed under an endpoint name. -/
theorem unit_circle_no_extension_of_upper_dense {f : ℂ → ℂ} {S : Set ℂ}
    (hreal : ∀ t : ℂ, 1 < ‖t‖ → f (star t)=star (f t))
    (hselected : ∀ z ∈ S, ¬ HasExteriorExtension f z)
    (hdense : ∀ theta : ℝ, 0 < theta → theta < Real.pi →
      unitAngle theta ∈ closure S) :
    ∀ z : ℂ, ‖z‖=1 → ¬ HasExteriorExtension f z := by
  have hupper (theta : ℝ) (ht : 0 ≤ theta) (htpi : theta ≤ Real.pi) :
      ¬ HasExteriorExtension f (unitAngle theta) := by
    have hI : theta ∈ closure (Ioo (0:ℝ) Real.pi) := by
      rw [closure_Ioo (by linarith [Real.pi_pos] : (0:ℝ) ≠ Real.pi)]
      exact ⟨ht,htpi⟩
    have hcl := image_closure_subset_closure_image unitAngle_continuous
      (mem_image_of_mem unitAngle hI)
    have hsub : unitAngle '' Ioo (0:ℝ) Real.pi ⊆ closure S := by
      rintro _ ⟨theta,htheta,rfl⟩
      exact hdense theta htheta.1 htheta.2
    exact no_extension_on_closure hselected
      ((closure_minimal hsub isClosed_closure) hcl)
  intro z hz
  have heq : unitAngle z.arg=z := by
    simpa only [hz,Complex.ofReal_one,one_mul,unitAngle] using
      Complex.norm_mul_exp_arg_mul_I z
  rw [← heq]
  by_cases hpos : 0 ≤ z.arg
  · exact hupper z.arg hpos (Complex.arg_le_pi z)
  · have h := no_extension_conjugate_of_real_symmetry hreal
      (hupper (-z.arg) (by linarith) (by linarith [Complex.neg_pi_lt_arg z]))
    simpa only [unitAngle_conjugate,neg_neg] using h

end
end IsingBulk.HT.Final
