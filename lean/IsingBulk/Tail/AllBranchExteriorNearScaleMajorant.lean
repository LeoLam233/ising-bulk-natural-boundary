import IsingBulk.Tail.AllBranchExteriorScaleEnvelope
import IsingBulk.Tail.CollisionScaleSummability

namespace IsingBulk.Tail
noncomputable section

/-- Scalar near budget including the finite anchor/pair count, kernel N^4
factor, and its one inverse diameter. The coarse slope (1+2U)/b is used only
after its geometric validity is established by the calling theorem. -/
def allBranchExteriorNearScaleMajorant (j G C : ℕ)
    (D c A C₀ C₁ K Aμ cμ U L Kker B : ℝ) (N : ℕ) : ℝ :=
  let b := allBranchMicroRadius Aμ cμ N
  (N:ℝ)^7*allBranchExteriorNearLocalCost j N G C D c A
    (allBranchExteriorNearChartJetCost j N C₀ C₁ K b) ((1+2*U)/b)*
      Kker*L^N*(b/4)⁻¹*(4*allBranchEqualityRadius B N)^(N*(N-1)-(2*j+1))

theorem allBranchExterior_near_scale_majorant_summable (j G C : ℕ)
    (D c A C₀ C₁ K Aμ cμ U L Kker : ℝ) :
    ∃ B₀ : ℝ, 0 < B₀ ∧ ∀ B : ℝ, B₀ ≤ B →
      Summable (allBranchExteriorNearScaleMajorant j G C D c A C₀ C₁ K Aμ cμ U L Kker B) := by
  let f := fun N : ℕ => (N:ℝ)^7*allBranchExteriorNearLocalCost j N G C D c A
    (allBranchExteriorNearChartJetCost j N C₀ C₁ K (allBranchMicroRadius Aμ cμ N)) 1*
      Kker*L^N*(4*(allBranchMicroRadius Aμ cμ N)⁻¹)
  let h := fun N : ℕ => (1+2*U)*(allBranchMicroRadius Aμ cμ N)⁻¹
  have hL : NatExponentialEnvelope 1 (fun N => L^N) :=
    NatExponentialEnvelope.const_pow L (fun N => N) (fun _ _ => by simp)
  have hb := allBranchExterior_micro_inverse_envelope Aμ cμ
  have hf : NatExponentialEnvelope 2 f :=
    (((((NatExponentialEnvelope.id.pow 7).mono_degree (by omega)).mul
      (allBranchExterior_near_local_prefactor_envelope j G C D c A C₀ C₁ K Aμ cμ)).mul
        (NatExponentialEnvelope.const 2 Kker)).mul (hL.mono_degree (by omega))).mul
          (((NatExponentialEnvelope.const 1 4).mul hb).mono_degree (by omega))
  have hh : NatExponentialEnvelope 1 h := (NatExponentialEnvelope.const 1 (1+2*U)).mul hb
  obtain ⟨B₀,hB₀,hSum⟩ := collision_scale_summable hf hh (2*j+1)
  refine ⟨B₀,hB₀,?_⟩
  intro B hB
  apply (hSum B hB).congr
  intro N
  dsimp [f,h,allBranchExteriorNearScaleMajorant,allBranchEqualityRadius,allBranchExteriorNearLocalCost]
  simp only [one_pow,mul_one,div_eq_mul_inv]
  ring

end
end IsingBulk.Tail
