import IsingBulk.Anisotropic.NegativeNormalForm.Algebra
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! The radial Hadamard integral with the zero-mean projection retained.
The analytic derivative bounds for the specific ANISO implicit map are not
asserted here; this module supplies the exact integral identity used with them. -/
namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open scoped BigOperators
open MeasureTheory

/-- The radial integral in (4.28), in actual component coordinates. -/
def radialField {n : ℕ} (grad : Config n → Config n) (w : Config n) : Config n :=
  fun i => ∫ t : ℝ in 0..1, grad (fun k => (t : ℂ) * w k) i

theorem pairing_project_right {n : ℕ} (w u : Config n) (hw : ZeroMean w) :
    pairing w (project u) = pairing w u := by
  simp only [pairing, project, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [show ∑ i, w i = 0 from hw]
  ring

theorem pairing_radialField {n : ℕ} (grad : Config n → Config n) (w : Config n)
    (hint : ∀ i, IntervalIntegrable (fun t : ℝ => grad (fun k => (t : ℂ) * w k) i)
      volume 0 1) :
    pairing w (radialField grad w) =
      ∫ t : ℝ in 0..1, pairing w (grad (fun k => (t : ℂ) * w k)) := by
  unfold pairing radialField
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    exact (intervalIntegral.integral_const_mul _ _).symm
  · intro i _
    exact (hint i).const_mul (w i)

/-- Actual construction of a zero-mean Hadamard field. The derivative premise
is an ordinary one-variable chain-rule premise, not the desired mean identity. -/
theorem radial_hadamard_identity {n : ℕ} (hn : n ≠ 0)
    (mu : Config n → ℂ) (grad : Config n → Config n) (w : Config n)
    (hw : ZeroMean w) (hzero : mu 0 = 0)
    (hint : ∀ i, IntervalIntegrable (fun t : ℝ => grad (fun k => (t : ℂ) * w k) i)
      volume 0 1)
    (hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => mu (fun k => (s : ℂ) * w k))
        (pairing w (grad (fun k => (t : ℂ) * w k))) t) :
    let ell := project (radialField grad w)
    ZeroMean ell ∧ pairing w ell = mu w := by
  refine ⟨project_zeroMean hn _, ?_⟩
  rw [pairing_project_right w _ hw, pairing_radialField grad w hint]
  have hi : IntervalIntegrable
      (fun t : ℝ => pairing w (grad (fun k => (t : ℂ) * w k))) volume 0 1 := by
    unfold pairing
    convert (IntervalIntegrable.sum Finset.univ
      (fun i _ => (hint i).const_mul (w i))) using 1
    ext t
    simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hi]
  simpa [hzero]

/-- The genuine complex-bilinear derivative represented by a gradient vector. -/
def pairingMap {n : ℕ} (u : Config n) : Config n →L[ℂ] ℂ :=
  ∑ i, u i • ContinuousLinearMap.proj i

@[simp] theorem pairingMap_apply {n : ℕ} (u w : Config n) :
    pairingMap u w = pairing w u := by
  simp [pairingMap, pairing, mul_comm]

/-- The required real-path derivative follows from the genuine complex
Fréchet derivative, including its restriction of scalars. -/
theorem radial_path_hasDerivAt {n : ℕ} (mu : Config n → ℂ)
    (grad : Config n → Config n) (w : Config n) (t : ℝ)
    (h : HasFDerivAt mu (pairingMap (grad (fun k => (t : ℂ) * w k)))
      (fun k => (t : ℂ) * w k)) :
    HasDerivAt (fun s : ℝ => mu (fun k => (s : ℂ) * w k))
      (pairing w (grad (fun k => (t : ℂ) * w k))) t := by
  have hp : HasDerivAt (fun s : ℝ => fun k => (s : ℂ) * w k) w t := by
    convert! (hasDerivAt_id t).smul_const w using 1
    ext s
    simp
  convert! (h.restrictScalars ℝ).comp_hasDerivAt t hp using 1
  simp

/-- Hadamard's formula from an actual complex derivative representation.
No bilinear mean identity is assumed. -/
theorem radial_hadamard_of_fderiv {n : ℕ} (hn : n ≠ 0)
    (mu : Config n → ℂ) (grad : Config n → Config n) (w : Config n)
    (hw : ZeroMean w) (hzero : mu 0 = 0)
    (hint : ∀ i, IntervalIntegrable (fun t : ℝ => grad (fun k => (t : ℂ) * w k) i)
      volume 0 1)
    (hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasFDerivAt mu (pairingMap (grad (fun k => (t : ℂ) * w k)))
        (fun k => (t : ℂ) * w k)) :
    let ell := project (radialField grad w)
    ZeroMean ell ∧ pairing w ell = mu w := by
  apply radial_hadamard_identity hn mu grad w hw hzero hint
  intro t ht
  exact radial_path_hasDerivAt mu grad w t (hderiv t ht)

end
end IsingBulk.Anisotropic.NegativeNormalForm
