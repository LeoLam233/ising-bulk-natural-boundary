import IsingBulk.Final.SymmetryObstruction
import IsingBulk.Algebra.PrimeDensity

/-! The actual selected prime family and the two source symmetries obstruct
every unit point. Endpoint density is proved, not omitted. -/
namespace IsingBulk.Final
noncomputable section
open Set Filter IsingBulk.PrimeFamily
open scoped Topology

def unitAngle (t : ℝ) : ℂ := Complex.exp ((t:ℂ)*Complex.I)

theorem unitAngle_continuous : Continuous unitAngle := by
  exact Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)

theorem unitAngle_conjugate (t : ℝ) : star (unitAngle t) = unitAngle (-t) := by
  unfold unitAngle
  rw [show star (Complex.exp ((t:ℂ)*Complex.I)) =
    Complex.exp (star ((t:ℂ)*Complex.I)) from (Complex.exp_conj _).symm]
  congr 1
  simp

theorem unitAngle_add_pi (t : ℝ) : unitAngle (t+Real.pi) = -unitAngle t := by
  unfold unitAngle
  rw [Complex.ofReal_add,add_mul,Complex.exp_add,Complex.exp_pi_mul_I]
  ring

theorem selectedFamily_dense_closed_arc {t : ℝ} (ht : 0 ≤ t) (htpi : t ≤ Real.pi/2) :
    unitAngle t ∈ closure selectedFamily := by
  have hI : t ∈ closure (Ioo (0:ℝ) (Real.pi/2)) := by
    rw [closure_Ioo (by positivity : (0:ℝ) ≠ Real.pi/2)]
    exact ⟨ht,htpi⟩
  have hi := image_closure_subset_closure_image unitAngle_continuous (mem_image_of_mem unitAngle hI)
  apply (closure_minimal (s := unitAngle '' Ioo (0:ℝ) (Real.pi/2)) _ isClosed_closure) hi
  rintro _ ⟨a,ha,rfl⟩
  exact selectedFamily_dense_arc ha.1 ha.2

/-- Natural-boundary propagation is a theorem about actual open-neighborhood
extensions, and includes all four axis points via closed-arc density. -/
theorem unit_circle_no_extension_of_selected {f : ℂ → ℂ}
    (heven : ∀ s : ℂ, 1 < ‖s‖ → f (-s)=f s)
    (hreal : ∀ s : ℂ, 1 < ‖s‖ → f (star s)=star (f s))
    (hselected : ∀ z ∈ selectedFamily, ¬ HasExteriorExtension f z) :
    ∀ z : ℂ, ‖z‖ = 1 → ¬ HasExteriorExtension f z := by
  have hquarter (t : ℝ) (ht : 0 ≤ t) (htpi : t ≤ Real.pi/2) :
      ¬ HasExteriorExtension f (unitAngle t) :=
    no_extension_on_closure hselected (selectedFamily_dense_closed_arc ht htpi)
  intro z hz
  have heq : unitAngle z.arg = z := by
    simpa only [hz,Complex.ofReal_one,one_mul,unitAngle] using Complex.norm_mul_exp_arg_mul_I z
  rw [← heq]
  by_cases hpos : 0 ≤ z.arg
  · by_cases hsmall : z.arg ≤ Real.pi/2
    · exact hquarter _ hpos hsmall
    · have ht : 0 ≤ Real.pi-z.arg := by linarith [Complex.arg_le_pi z]
      have htpi : Real.pi-z.arg ≤ Real.pi/2 := by linarith
      have h := no_extension_neg_of_even heven
        (no_extension_conjugate_of_real_symmetry hreal (hquarter _ ht htpi))
      rw [unitAngle_conjugate,show -(Real.pi-z.arg)=z.arg-Real.pi by ring] at h
      have hid : -unitAngle (z.arg-Real.pi)=unitAngle z.arg := by
        have ha := unitAngle_add_pi (z.arg-Real.pi)
        simpa only [sub_add_cancel] using ha.symm
      rwa [hid] at h
  · have hneg : z.arg ≤ 0 := le_of_not_ge hpos
    by_cases hsmall : -Real.pi/2 ≤ z.arg
    · have h := no_extension_conjugate_of_real_symmetry hreal
        (hquarter (-z.arg) (by linarith) (by linarith))
      simpa only [unitAngle_conjugate,neg_neg] using h
    · have ht : 0 ≤ z.arg+Real.pi := by linarith [Complex.neg_pi_lt_arg z]
      have htpi : z.arg+Real.pi ≤ Real.pi/2 := by linarith
      have h := no_extension_neg_of_even heven (hquarter _ ht htpi)
      simpa only [unitAngle_add_pi,neg_neg] using h

end
end IsingBulk.Final
