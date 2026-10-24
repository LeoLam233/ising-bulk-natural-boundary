import IsingBulk.Anisotropic.RegularEdges.RetainedDimension

namespace IsingBulk.Anisotropic.RegularEdges
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators

/-- The probability product normalization is exactly the original angular
Lebesgue normalization, including dimension zero. -/
theorem edgeAngleMeasure_pi_eq (n : ℕ) :
    (Measure.pi fun _ : Fin n => edgeAngleMeasure)=
      ((ENNReal.ofReal (2*Real.pi))⁻¹)^n •
        (volume : Measure (Fin n → ℝ)).restrict
          (Icc (fun _ => -Real.pi) (fun _ => Real.pi)) := by
  have hbox : Icc (fun _ : Fin n => -Real.pi) (fun _ => Real.pi)=
      Set.univ.pi (fun _ : Fin n => Icc (-Real.pi) Real.pi) := by
    ext v
    simp [Set.mem_Icc]
  rw [hbox,volume_pi,Measure.restrict_pi_pi]
  apply Measure.pi_eq
  intro s _
  simp only [Measure.smul_apply,smul_eq_mul,Measure.pi_pi,edgeAngleMeasure]
  simp only [Finset.prod_mul_distrib,
    Finset.prod_const,Finset.card_univ,Fintype.card_fin]

theorem edgeAngleMeasure_integral_eq (n : ℕ) (f : (Fin n → ℝ) → ℂ) :
    (∫ v, f v ∂(Measure.pi fun _ : Fin n => edgeAngleMeasure))=
      ((2*Real.pi : ℂ)⁻¹)^n *
        ∫ v in Icc (fun _ => -Real.pi) (fun _ => Real.pi), f v := by
  rw [edgeAngleMeasure_pi_eq,integral_smul_measure]
  simp only [ENNReal.toReal_pow,ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (by positivity : 0≤2*Real.pi),Complex.real_smul,
    Complex.ofReal_pow,Complex.ofReal_inv,Complex.ofReal_mul,Complex.ofReal_ofNat]

end
end IsingBulk.Anisotropic.RegularEdges
