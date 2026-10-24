import IsingBulk.Anisotropic.NegativeNormalForm.Dispersion
import IsingBulk.Anisotropic.NegativeNormalForm.Symmetry

/-! The actual permutation-invariant negative-edge phase sum (4.8),
its exact central zero, simple parameter derivative and vanishing first
variation on the zero-mean plane. -/
namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open scoped BigOperators

def poleEquation {n : ℕ} (B : ℂ → ℂ) (phi : ℝ) (hphi : Real.sin phi ≠ 0)
    (d t : ℂ) (v : Config n) : ℂ :=
  ∑ i, (negativePhase B phi hphi t (d + v i) - (phi : ℂ) * Complex.I)

theorem poleEquation_center {n : ℕ} (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi ≠ 0) (d : ℂ) :
    poleEquation B phi hphi d (1 - Complex.cos d) (0 : Config n) = 0 := by
  simp [poleEquation, negativePhase_center]

theorem poleEquation_permute {n : ℕ} (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi ≠ 0) (d t : ℂ) (v : Config n) (e : Equiv.Perm (Fin n)) :
    poleEquation B phi hphi d t (permute e v) = poleEquation B phi hphi d t v :=
  Equiv.sum_comp e (fun i => negativePhase B phi hphi t (d + v i) - (phi : ℂ) * Complex.I)

theorem poleEquation_hasDerivAt_center {n : ℕ} (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi ≠ 0) (d B' : ℂ)
    (hB : HasDerivAt B B' (1 - Complex.cos d)) :
    HasDerivAt (fun t => poleEquation B phi hphi d t (0 : Config n))
      (n * (((Real.sin phi : ℂ) * Complex.I)⁻¹ * B (1 - Complex.cos d)))
      (1 - Complex.cos d) := by
  have h := (negativePhase_hasDerivAt_center B phi hphi d B' hB).sub_const
    ((phi : ℂ) * Complex.I)
  have hh := HasDerivAt.sum (u := (Finset.univ : Finset (Fin n))) (fun _ _ => h)
  convert hh using 1
  · ext t
    simp only [poleEquation, Pi.zero_apply, add_zero, Finset.sum_apply]
  · simp

theorem poleEquation_parameter_derivative_ne_zero {n : ℕ} (hn : n ≠ 0)
    (B : ℂ → ℂ) (phi : ℝ) (hphi : Real.sin phi ≠ 0) (d : ℂ)
    (hB : B (1 - Complex.cos d) ≠ 0) :
    (n : ℂ) * (((Real.sin phi : ℂ) * Complex.I)⁻¹ * B (1 - Complex.cos d)) ≠ 0 := by
  apply mul_ne_zero (by exact_mod_cast hn)
  apply mul_ne_zero _ hB
  exact inv_ne_zero (mul_ne_zero (by exact_mod_cast hphi) Complex.I_ne_zero)

/-- The first variation vanishes exactly, by the actual momentum constraint. -/
theorem poleEquation_zeroMean_first_variation {n : ℕ} (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi ≠ 0) (d : ℂ) (v : Config n) (hv : ZeroMean v) :
    HasDerivAt (fun s : ℂ => poleEquation B phi hphi d (1 - Complex.cos d)
      (fun i => s * v i)) 0 0 := by
  let c := ((Real.sin phi : ℂ) * Complex.I)⁻¹ *
    (-B (1 - Complex.cos d) * Complex.sin d)
  have hi (i : Fin n) : HasDerivAt
      (fun s : ℂ => negativePhase B phi hphi (1 - Complex.cos d) (d + s * v i) -
        (phi : ℂ) * Complex.I) (c * v i) 0 := by
    have hl : HasDerivAt (fun s : ℂ => d + s * v i) (v i) 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).mul_const (v i)).const_add d
    have hg := negativePhase_hasDerivAt_delta_center B phi hphi d
    have hg' : HasDerivAt (negativePhase B phi hphi (1 - Complex.cos d)) c
        (d + 0 * v i) := by simpa [c] using hg
    have h := hg'.comp (0 : ℂ) hl
    exact h.sub_const ((phi : ℂ) * Complex.I)
  have hh := HasDerivAt.sum (u := (Finset.univ : Finset (Fin n))) (fun i _ => hi i)
  have hz : ∑ i, c * v i = 0 := by rw [← Finset.mul_sum, hv, mul_zero]
  rw [hz] at hh
  convert hh using 1
  ext s
  simp [poleEquation]

end
end IsingBulk.Anisotropic.NegativeNormalForm
