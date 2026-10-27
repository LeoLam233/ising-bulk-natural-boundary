import IsingBulk.Preferred22.PhysicalTransportIteration

/-! Actual weighted right-sector descendants. The fixed smooth angular
multiplier is inserted into the original seed before any transport step;
all derivatives of it are consequently retained by the literal recurrence. -/
namespace IsingBulk.Preferred22
noncomputable section

def preferredWeightedPhysicalDensity {N : ℕ} (ψ : (Fin N → ℝ) → ℂ)
    (τ : ℝ) (η p m r : ℝ → ℝ) : ℕ → ℂ → (Fin N → ℝ) → ℂ
  | 0 => fun s θ => ψ θ*preferredPhysicalSeed .right τ η p m r s θ
  | j+1 => preferredTransportStep (preferredSourceAngularField .right τ p m)
      (preferredWeightedPhysicalDensity ψ τ η p m r j)

def preferredWeightedRegularScalar {N : ℕ} (ψ : (Fin N → ℝ) → ℂ)
    (τ : ℝ) (η p m r : ℝ → ℝ) : ℕ → ℂ → (Fin N → ℝ) → ℂ
  | 0 => fun s θ => ψ θ*preferredRegularSeed τ η p m r s θ
  | j+1 => preferredRegularTransportStep τ p m
      (preferredWeightedRegularScalar ψ τ η p m r j)

theorem preferredWeightedPhysicalDensity_one {N : ℕ}
    (τ : ℝ) (η p m r : ℝ → ℝ) (j : ℕ) :
    preferredWeightedPhysicalDensity (fun _ : Fin N → ℝ => 1) τ η p m r j=
      preferredTransportedDensity .right τ η p m r j := by
  induction j with
  | zero => funext s θ; exact one_mul _
  | succ j ih =>
    simp only [preferredWeightedPhysicalDensity,preferredTransportedDensity,ih]

theorem preferredWeightedRegularScalar_one {N : ℕ}
    (τ : ℝ) (η p m r : ℝ → ℝ) (j : ℕ) :
    preferredWeightedRegularScalar (fun _ : Fin N → ℝ => 1) τ η p m r j=
      preferredRegularTransportedScalar τ η p m r j := by
  induction j with
  | zero => funext s θ; exact one_mul _
  | succ j ih =>
    simp only [preferredWeightedRegularScalar,preferredRegularTransportedScalar,ih]

end
end IsingBulk.Preferred22
