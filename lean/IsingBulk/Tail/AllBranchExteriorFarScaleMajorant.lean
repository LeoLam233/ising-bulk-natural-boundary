import IsingBulk.Tail.AllBranchExteriorScaleEnvelope
import IsingBulk.Tail.AllBranchExteriorFarSourceBudget
import IsingBulk.Tail.AllBranchExteriorFarChartCutoff
import IsingBulk.Tail.GaussianEnvelopeSummability

namespace IsingBulk.Tail
noncomputable section

theorem allBranchExterior_far_separation_inverse_envelope (B : ℝ) :
    NatExponentialEnvelope 1 (fun N => (allBranchEqualityRadius B N/Real.sqrt (N:ℝ))⁻¹) := by
  have hsqrt : NatExponentialEnvelope 1 (fun N => Real.sqrt (N:ℝ)) := by
    apply NatExponentialEnvelope.id.mono_abs
    intro N hN
    have hn : 1 ≤ (N:ℝ) := by exact_mod_cast hN
    rw [abs_of_nonneg (Real.sqrt_nonneg _),abs_of_nonneg (Nat.cast_nonneg N (α := ℝ))]
    exact Real.sqrt_le_iff.mpr ⟨Nat.cast_nonneg _,by nlinarith⟩
  convert hsqrt.mul (allBranchExterior_equality_inverse_envelope B) using 1
  funext N
  rw [inv_div,div_eq_mul_inv]

theorem allBranchExterior_far_cutoff_envelope (j : ℕ) (C₀ C₁ K A c B : ℝ) :
    NatExponentialEnvelope 1 (fun N => allBranchExteriorFarChartJetCost j N C₀ C₁ K
      (allBranchMicroRadius A c N) (allBranchEqualityRadius B N)) := by
  have hpoly : NatExponentialEnvelope 1 (fun N => (1+24*N:ℝ)^j) :=
    ((NatExponentialEnvelope.const 1 1).add ((NatExponentialEnvelope.const 1 24).mul NatExponentialEnvelope.id)).pow j
  have hC₀ : NatExponentialEnvelope 1 (fun N => C₀^N) :=
    NatExponentialEnvelope.const_pow C₀ (fun N => N) (fun _ _ => by simp)
  have hC₁ : NatExponentialEnvelope 1 (fun N => C₁^N) :=
    NatExponentialEnvelope.const_pow C₁ (fun N => N) (fun _ _ => by simp)
  exact (((NatExponentialEnvelope.const 1 ((2:ℝ)^j)).mul hC₀).mul
    (((NatExponentialEnvelope.const 1 ((2:ℝ)^j)).mul
      (hC₁.mul ((allBranchExterior_micro_inverse_envelope A c).pow j))).mul
        ((NatExponentialEnvelope.const 1 K).mul hpoly))).mul ((allBranchExterior_equality_inverse_envelope B).pow j)

def allBranchExteriorFarScaleMajorant (j G C : ℕ)
    (D c A C₀ C₁ K Aμ cμ L Kker B : ℝ) (N : ℕ) : ℝ :=
  let b := allBranchMicroRadius Aμ cμ N
  let ρ := allBranchEqualityRadius B N
  let σ := ρ/Real.sqrt (N:ℝ)
  (N:ℝ)^7*allBranchExteriorFarLocalCost j N G C D c A
    (allBranchExteriorFarChartJetCost j N C₀ C₁ K b ρ) σ*Kker*L^N*(b/2)⁻¹*σ⁻¹

theorem allBranchExterior_far_scale_majorant_summable (j G C : ℕ)
    (D c A C₀ C₁ K Aμ cμ L Kker B : ℝ) (hA : 1 ≤ A) :
    Summable (allBranchExteriorFarScaleMajorant j G C D c A C₀ C₁ K Aμ cμ L Kker B) := by
  let b := allBranchMicroRadius Aμ cμ
  let ρ := allBranchEqualityRadius B
  let σ := fun N : ℕ => ρ N/Real.sqrt (N:ℝ)
  let W := fun N => allBranchExteriorFarChartJetCost j N C₀ C₁ K (b N) (ρ N)
  let f := fun N : ℕ => (N:ℝ)^7*(3+3*N:ℝ)^j*
    (2^j*((2^j*(G:ℝ)*(N:ℝ)^G*D)*(max 1 c⁻¹)^(2*j)))*W N*(σ N)⁻¹^(2*j)*
      ((C:ℝ)*(N:ℝ)^C)*Kker*L^N*(2*(b N)⁻¹)*(σ N)⁻¹
  have hpoly : NatExponentialEnvelope 1 (fun N => (3+3*N:ℝ)^j) :=
    ((NatExponentialEnvelope.const 1 3).add ((NatExponentialEnvelope.const 1 3).mul NatExponentialEnvelope.id)).pow j
  have hguard : NatExponentialEnvelope 1 (fun N => 2^j*((2^j*(G:ℝ)*(N:ℝ)^G*D)*(max 1 c⁻¹)^(2*j))) :=
    (NatExponentialEnvelope.const 1 ((2:ℝ)^j)).mul
      ((((NatExponentialEnvelope.const 1 ((2:ℝ)^j*(G:ℝ))).mul (NatExponentialEnvelope.id.pow G)).mul
        (NatExponentialEnvelope.const 1 D)).mul (NatExponentialEnvelope.const 1 ((max 1 c⁻¹)^(2*j))))
  have hcoeff : NatExponentialEnvelope 1 (fun N => (C:ℝ)*(N:ℝ)^C) :=
    (NatExponentialEnvelope.const 1 (C:ℝ)).mul (NatExponentialEnvelope.id.pow C)
  have hσ : NatExponentialEnvelope 1 (fun N => (σ N)⁻¹) := allBranchExterior_far_separation_inverse_envelope B
  have hW : NatExponentialEnvelope 1 W := allBranchExterior_far_cutoff_envelope j C₀ C₁ K Aμ cμ B
  have hL : NatExponentialEnvelope 1 (fun N => L^N) :=
    NatExponentialEnvelope.const_pow L (fun N => N) (fun _ _ => by simp)
  have hf : NatExponentialEnvelope 1 f :=
    (((((((((NatExponentialEnvelope.id.pow 7).mul hpoly).mul hguard).mul hW).mul (hσ.pow (2*j))).mul hcoeff).mul
      (NatExponentialEnvelope.const 1 Kker)).mul hL).mul
        ((NatExponentialEnvelope.const 1 2).mul (allBranchExterior_micro_inverse_envelope Aμ cμ))).mul hσ
  apply (linear_envelope_numerator_gaussian_summable hf j A hA).congr
  intro N
  dsimp [f,W,b,ρ,σ,allBranchExteriorFarScaleMajorant,allBranchExteriorFarLocalCost,
    allBranchExteriorFarNumeratorCost,allBranchNumeratorJetBudget]
  simp only [div_eq_mul_inv,inv_pow]
  ring

end
end IsingBulk.Tail
