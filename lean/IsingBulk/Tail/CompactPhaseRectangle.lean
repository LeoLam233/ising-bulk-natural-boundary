import IsingBulk.Tail.CompactRightPhaseJets
import IsingBulk.Tail.SelectorDefinitions
import IsingBulk.Tail.CompactRightShapeCoarea

/-! Literal unwrapped source phases fit an N-by-N period rectangle.
No phase-map multiplicity is inferred from a principal argument of a product. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First Set
open scoped BigOperators

def currentUnwrappedPhase {N : ℕ} (f : SelectorFunctions) (r τ lam : ℝ) (s : ℂ)
    (θ : Fin N → ℝ) : ℝ :=
  ∑ i, (continuedPhase (sourceW s (deformedPoint f r τ lam θ i))).re

theorem continuedPhase_re (W : ℂ) : (continuedPhase W).re= -Complex.arg (continuedRoot W) := by
  simp [continuedPhase,Complex.mul_re,Complex.log_im]

theorem continuedPhase_re_abs_le (W : ℂ) : |(continuedPhase W).re|≤Real.pi := by
  rw [continuedPhase_re,abs_neg]
  exact Complex.abs_arg_le_pi _

theorem currentUnwrappedPhase_abs_le {N : ℕ} (f : SelectorFunctions) (r τ lam : ℝ) (s : ℂ)
    (θ : Fin N → ℝ) : |currentUnwrappedPhase f r τ lam s θ|≤(N:ℝ)*Real.pi := by
  unfold currentUnwrappedPhase
  exact (Finset.abs_sum_le_sum_abs _ _).trans (by
    simpa using Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => continuedPhase_re_abs_le
      (sourceW s (deformedPoint f r τ lam θ i))))

theorem angular_sum_abs_le {N : ℕ} (θ : Fin N → ℝ) (hθ : ∀ i, |θ i|≤Real.pi) :
    |∑ i, θ i|≤(N:ℝ)*Real.pi :=
  (Finset.abs_sum_le_sum_abs _ _).trans (by simpa using Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => hθ i))

theorem shape_angular_sum {N : ℕ} (t ρ : ℝ) (ω : Fin N → ℝ) (hzero : ∑ i, ω i=0) :
    (∑ i, (t+ρ*ω i))=(N:ℝ)*t := by
  simp [Finset.sum_add_distrib,← Finset.mul_sum,hzero]

theorem current_phase_rectangle {N : ℕ} (f : SelectorFunctions) (r τ lam : ℝ) (s : ℂ)
    (θ : Fin N → ℝ) (hθ : ∀ i, |θ i|≤Real.pi) :
    ((∑ i, θ i),currentUnwrappedPhase f r τ lam s θ) ∈
      Icc (-(N:ℝ)*Real.pi) ((N:ℝ)*Real.pi) ×ˢ Icc (-(N:ℝ)*Real.pi) ((N:ℝ)*Real.pi) := by
  have hF := abs_le.mp (angular_sum_abs_le θ hθ)
  have hG := abs_le.mp (currentUnwrappedPhase_abs_le f r τ lam s θ)
  exact ⟨⟨by linarith, hF.2⟩,⟨by linarith,hG.2⟩⟩

theorem phase_rectangle_period_count (N : ℕ) :
    (N:ℝ)*Real.pi= -(N:ℝ)*Real.pi+(N:ℝ)*(2*Real.pi) := by ring

/-- The Z phase is the sum of individual phases, including all winding.
The real part of the sum is not replaced by the argument of Z. -/
theorem product_root_unwrapped_phase {N : ℕ} (W : Fin N → ℂ) :
    coordinateProduct (fun i => continuedRoot (W i))=
      Complex.exp (-Complex.I*∑ i, continuedPhase (W i)) := by
  unfold coordinateProduct continuedPhase
  rw [Finset.mul_sum,Complex.exp_sum]
  apply Finset.prod_congr rfl
  intro i _
  have he : -Complex.I*(Complex.I*Complex.log (continuedRoot (W i)))=Complex.log (continuedRoot (W i)) := by
    rw [← mul_assoc]
    simp
  rw [he,Complex.exp_log (continuedRoot_nonzero _)]

end
end IsingBulk.Tail
