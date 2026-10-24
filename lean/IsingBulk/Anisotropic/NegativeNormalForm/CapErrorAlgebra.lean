import IsingBulk.Anisotropic.NegativeNormalForm.ActualDensityBetaUniform

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section

/-- Exact center multiplication preserves relative error, including the factor
two for the reflected pair of central winding sectors. -/
theorem centered_cap_model_error (center cap cut error period M : ℂ) (ed et : ℝ)
    (hcap : cap=center*(cut+error)) (hM : 2*center*period=M)
    (hd : ‖error‖≤ed*‖period‖) (ht : ‖cut-period‖≤et*‖period‖) :
    ‖2*cap-M‖≤(ed+et)*‖M‖ := by
  rw [←hM]
  have he : 2*cap-2*center*period=(2*center)*((cut-period)+error) := by rw [hcap]; ring
  rw [he,norm_mul,norm_mul (2*center) period]
  calc
    _ ≤ ‖2*center‖*(‖cut-period‖+‖error‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)
    _ ≤ ‖2*center‖*(et*‖period‖+ed*‖period‖) :=
      mul_le_mul_of_nonneg_left (add_le_add ht hd) (norm_nonneg _)
    _ = _ := by ring

end
end IsingBulk.Anisotropic.NegativeNormalForm
