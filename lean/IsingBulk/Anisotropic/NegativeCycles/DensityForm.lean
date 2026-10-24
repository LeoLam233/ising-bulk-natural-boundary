import IsingBulk.Anisotropic.NegativeCycles.HolomorphicTransport
import Mathlib.Topology.Algebra.Group.Matrix

noncomputable section
namespace IsingBulk.Anisotropic.NegativeCycles

/-- The standard complex volume form, with its literal determinant normalization. -/
def complexVolumeForm (n : ℕ) : (Fin n → ℂ) [⋀^Fin n]→L[ℂ] ℂ where
  toAlternatingMap := Matrix.detRowAlternating
  cont := continuous_id.matrix_det

@[simp] theorem complexVolumeForm_apply (n : ℕ) (v : Fin n → Fin n → ℂ) :
    complexVolumeForm n v=Matrix.det v := rfl

/-- The actual density times the standard complex volume form. -/
def densityForm {n : ℕ} (f : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) :
    (Fin n → ℂ) [⋀^Fin n]→L[ℂ] ℂ := f z • complexVolumeForm n

theorem densityForm_differentiableAt {n : ℕ} {f : (Fin n → ℂ) → ℂ} {z : Fin n → ℂ}
    (hf : DifferentiableAt ℂ f z) : DifferentiableAt ℂ (densityForm f) z :=
  hf.smul_const _

@[simp] theorem densityForm_chainPullback {n : ℕ} (f : (Fin n → ℂ) → ℂ)
    (H : ParameterSpace n → Fin n → ℂ) (x : ParameterSpace n)
    (v : Fin n → ParameterSpace n) :
    chainPullback (densityForm f) H x v=
      f (H x)*Matrix.det (fun i => fderiv ℝ H x (v i)) := rfl

end IsingBulk.Anisotropic.NegativeCycles
