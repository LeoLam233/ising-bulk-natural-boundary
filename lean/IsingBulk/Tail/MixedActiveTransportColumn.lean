import IsingBulk.Tail.MixedActiveChartDifferential
import IsingBulk.Tail.MixedDensityJetRecurrence

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Jets
open scoped BigOperators

def mixedActiveParameterDirection (N : ℕ) : MixedActiveSpace N := (1,(0,0))
def mixedActiveBranchDirection {N : ℕ} (j : Fin N) : MixedActiveSpace N := (0,(Pi.single j 1,0))
def mixedActiveCompactDirection (N : ℕ) : MixedActiveSpace N := (0,(0,1))

def mixedActiveBranchResidual {N : ℕ} (J : Finset (Fin N)) (j q : Fin N)
    (s : ℂ) (φ y : Fin N → ℂ) (u : MixedActiveSpace N) : ℂ :=
  (N:ℂ)*mixedResidualCore (mixedActiveResidualData J j q s φ y u)

def mixedActiveCompactResidual {N : ℕ} (J : Finset (Fin N)) (j q : Fin N)
    (s : ℂ) (φ y : Fin N → ℂ) (u : MixedActiveSpace N) : ℂ :=
  -(N:ℂ)*mixedCompactCore (mixedActiveResidualData J j q s φ y u)

theorem mixed_displacement_transport_column {N : ℕ} (J : Finset (Fin N)) (j q : Fin N)
    (hj : j∈J) (τ b v : Fin N → ℂ) (R₁ R₂ : ℂ)
    (hR : ∀ i∈J, τ i-b i*v i=if i=j then R₁ else 0) (hQ : -v q=R₂) :
    mixedDisplacementParameterColumn J τ-
      ∑ k, v k • mixedDisplacementAngularColumn J q k b =
    mixedActiveParameterDirection N+R₁ • mixedActiveBranchDirection j+
      R₂ • mixedActiveCompactDirection N := by
  apply Prod.ext
  · simp [mixedDisplacementParameterColumn,mixedDisplacementAngularColumn,
      mixedActiveParameterDirection,mixedActiveBranchDirection,mixedActiveCompactDirection,
      Prod.fst_sum]
  · apply Prod.ext
    · ext i
      by_cases hi : i∈J
      · simpa [mixedDisplacementParameterColumn,mixedDisplacementAngularColumn,
          mixedActiveParameterDirection,mixedActiveBranchDirection,mixedActiveCompactDirection,
          hi,Pi.single_apply,mul_ite,mul_comm,Prod.snd_sum,Prod.fst_sum,Finset.sum_apply] using hR i hi
      · have hij : i≠j := by intro he; subst i; exact hi hj
        simp [mixedDisplacementParameterColumn,mixedDisplacementAngularColumn,
          mixedActiveParameterDirection,mixedActiveBranchDirection,mixedActiveCompactDirection,
          hi,hij,Prod.snd_sum,Prod.fst_sum,Finset.sum_apply]
    · simpa [mixedDisplacementParameterColumn,mixedDisplacementAngularColumn,
        mixedActiveParameterDirection,mixedActiveBranchDirection,mixedActiveCompactDirection,mul_ite,
        Prod.snd_sum] using hQ

/-- The literal source transport has only two nonzero spatial residuals.
The compact residual has the opposite sign to the compact angular velocity. -/
theorem mixed_actual_transport_column {N : ℕ} (hN : 0<N)
    (J : Finset (Fin N)) (j q : Fin N) (hj : j∈J) (hq : q∉J)
    (f : SelectorFunctions) {r : ℝ} (hr : 0<r) (τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ)
    (hbranch : ∀ i∈J,Real.sin (θ i)<0) (hΩ : (s,θ)∈mixedSeparatedDomain J j q f r τ lam) :
    let y := deformedPoint f r τ lam θ
    let φ := fun i => mixedSourcePhase s (y i)
    mixedDisplacementParameterColumn J (fun i => mixedSourceTau s (y i))-
      ∑ k, mixedContourVelocity J j q f r τ lam s θ k •
        mixedDisplacementAngularColumn J q k (fun i => mixedSourceSlope s (y i)) =
    mixedActiveParameterDirection N+mixedActiveBranchResidual J j q s φ y 0 • mixedActiveBranchDirection j+
      mixedActiveCompactResidual J j q s φ y 0 • mixedActiveCompactDirection N := by
  let y := deformedPoint f r τ lam θ
  have hb : mixedSourceSlope s (y j)≠0 := by
    unfold mixedSourceSlope
    exact div_ne_zero (mul_ne_zero Complex.I_ne_zero (hΩ.2.2.1 j hj))
      (mul_ne_zero (by norm_num) (mixedSourcePhase_sin_ne (hΩ.2.1 j)))
  apply mixed_displacement_transport_column J j q hj
  · intro i hi
    by_cases hij : i=j
    · subst i
      simp only [ite_true]
      exact mixedBranchResidual_zero_source hN J j q f hr τ lam s θ hj hq hbranch hΩ.2.1
        (hΩ.2.2.1 j hj) hb hΩ.2.2.2.1
    · simp only [hij,ite_false,mixedContourVelocity]
      rw [mixedVelocity_other_branch _ _ _ _ _ hi hij hq,mixedSourceSlope_mul_A (hΩ.2.2.1 i hi),sub_self]
  · have hh := mixedCompactVelocity_zero_source hN J j q f hr τ lam s θ hj hq hbranch hΩ.2.1 hb hΩ.2.2.2.1
    rw [hh]
    simp only [mixedActiveCompactResidual,neg_mul]

end
end IsingBulk.Tail
