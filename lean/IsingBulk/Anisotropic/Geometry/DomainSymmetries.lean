import IsingBulk.Anisotropic.Geometry.AxisDomains

namespace IsingBulk.Anisotropic
noncomputable section
open Set

theorem omegaH_conj_iff (lam : ℝ) (z : ℂ) : star z∈omegaH lam ↔ z∈omegaH lam := by
  simp [omegaH,sliceH,mul_neg,Real.cos_neg]

theorem omegaL_conj_iff (lam : ℝ) (z : ℂ) : star z∈omegaL lam ↔ z∈omegaL lam := by
  simp [omegaL,sliceL,mul_neg,Real.cos_neg]

def realScaleHomeomorph (lam : ℝ) (hlam : lam≠0) : ℂ ≃ₜ ℂ where
  toFun z := (lam:ℂ)*z
  invFun z := ((lam⁻¹:ℝ):ℂ)*z
  left_inv := axis_exchange_scale hlam
  right_inv z := by simpa only [inv_inv] using axis_exchange_scale (inv_ne_zero hlam) z
  continuous_toFun := continuous_const.mul continuous_id
  continuous_invFun := continuous_const.mul continuous_id

theorem frontier_omegaH_axis_exchange_iff {lam : ℝ} (hlam : 0<lam) (z : ℂ) :
    (lam:ℂ)*z∈frontier (omegaH (lam⁻¹)) ↔ z∈frontier (omegaH lam) := by
  let h := realScaleHomeomorph lam hlam.ne'
  have he : h ⁻¹' omegaH (lam⁻¹)=omegaH lam := Set.ext (omegaH_axis_exchange_iff hlam)
  have hf := h.preimage_frontier (omegaH (lam⁻¹))
  rw [he] at hf
  change z∈h ⁻¹' frontier (omegaH (lam⁻¹)) ↔ _
  rw [hf]

theorem frontier_omegaL_axis_exchange_iff {lam : ℝ} (hlam : 0<lam) (z : ℂ) :
    (lam:ℂ)*z∈frontier (omegaL (lam⁻¹)) ↔ z∈frontier (omegaL lam) := by
  let h := realScaleHomeomorph lam hlam.ne'
  have he : h ⁻¹' omegaL (lam⁻¹)=omegaL lam := Set.ext (omegaL_axis_exchange_iff hlam)
  have hf := h.preimage_frontier (omegaL (lam⁻¹))
  rw [he] at hf
  change z∈h ⁻¹' frontier (omegaL (lam⁻¹)) ↔ _
  rw [hf]

theorem frontier_omegaH_conj_iff (lam : ℝ) (z : ℂ) :
    star z∈frontier (omegaH lam) ↔ z∈frontier (omegaH lam) := by
  let h := Complex.conjLIE.toHomeomorph
  have he : h ⁻¹' omegaH lam=omegaH lam := Set.ext (omegaH_conj_iff lam)
  have hf := h.preimage_frontier (omegaH lam)
  rw [he] at hf
  change z∈h ⁻¹' frontier (omegaH lam) ↔ _
  rw [hf]

theorem frontier_omegaL_conj_iff (lam : ℝ) (z : ℂ) :
    star z∈frontier (omegaL lam) ↔ z∈frontier (omegaL lam) := by
  let h := Complex.conjLIE.toHomeomorph
  have he : h ⁻¹' omegaL lam=omegaL lam := Set.ext (omegaL_conj_iff lam)
  have hf := h.preimage_frontier (omegaL lam)
  rw [he] at hf
  change z∈h ⁻¹' frontier (omegaL lam) ↔ _
  rw [hf]

end
end IsingBulk.Anisotropic
