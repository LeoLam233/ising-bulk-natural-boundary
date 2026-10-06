import IsingBulk.Tail.NatExponentialEnvelope
import IsingBulk.Tail.AllBranchExteriorNearSourceBudget
import IsingBulk.Tail.AllBranchExteriorChartCutoffJets
import Mathlib.Data.Nat.Choose.Bounds

namespace IsingBulk.Tail
noncomputable section

theorem allBranchExterior_micro_inverse_envelope (A c : ℝ) :
    NatExponentialEnvelope 1 (fun N => (allBranchMicroRadius A c N)⁻¹) := by
  have hh := ((NatExponentialEnvelope.const 1 c⁻¹).mul NatExponentialEnvelope.id).mul
    (NatExponentialEnvelope.exp_monomial 1 (A+4))
  convert hh using 1
  funext N
  simp only [pow_one]
  unfold allBranchMicroRadius
  rw [inv_div,div_eq_mul_inv,mul_inv_rev,← Real.exp_neg]
  rw [show - (-(A+4)*(N:ℝ))=(A+4)*(N:ℝ) by ring]
  ring

theorem allBranchExterior_equality_inverse_envelope (B : ℝ) :
    NatExponentialEnvelope 1 (fun N => (allBranchEqualityRadius B N)⁻¹) := by
  simpa only [allBranchEqualityRadius,← Real.exp_neg,neg_mul,neg_neg,pow_one] using
    NatExponentialEnvelope.exp_monomial 1 B

theorem allBranchExterior_choose_envelope :
    NatExponentialEnvelope 1 (fun N => (N.choose 2:ℝ)+1) := by
  apply (NatExponentialEnvelope.id.pow 2).mono_abs
  intro N hN
  have hn : 1 ≤ (N:ℝ) := by exact_mod_cast hN
  rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ (N.choose 2:ℝ)+1),
    abs_of_nonneg (sq_nonneg (N:ℝ)),Nat.cast_choose_two]
  nlinarith

theorem allBranchExterior_near_numerator_envelope (A : ℝ) (j : ℕ) :
    NatExponentialEnvelope 2 (fun N => allBranchExteriorNearNumeratorCost A j N) := by
  exact (((NatExponentialEnvelope.const 2 ((2:ℝ)^(2*j))).mul
    (NatExponentialEnvelope.const_pow 8 (fun N => N.choose 2) (fun N _ => Nat.choose_le_pow N 2))).mul
      ((allBranchExterior_choose_envelope.pow j).mono_degree (by omega))).mul
    (NatExponentialEnvelope.exp_monomial 2 A)

theorem allBranchExterior_near_cutoff_envelope (j : ℕ) (C₀ C₁ K A c : ℝ) :
    NatExponentialEnvelope 1 (fun N => allBranchExteriorNearChartJetCost j N C₀ C₁ K (allBranchMicroRadius A c N)) := by
  have hpoly : NatExponentialEnvelope 1 (fun N => (1+24*N:ℝ)^j) :=
    ((NatExponentialEnvelope.const 1 1).add ((NatExponentialEnvelope.const 1 24).mul NatExponentialEnvelope.id)).pow j
  have hC₀ : NatExponentialEnvelope 1 (fun N => C₀^N) := by
    exact NatExponentialEnvelope.const_pow C₀ (fun N => N) (fun _ _ => by simp)
  have hC₁ : NatExponentialEnvelope 1 (fun N => C₁^N) := by
    exact NatExponentialEnvelope.const_pow C₁ (fun N => N) (fun _ _ => by simp)
  exact (((NatExponentialEnvelope.const 1 ((2:ℝ)^j)).mul hC₀).mul
    (((NatExponentialEnvelope.const 1 ((2:ℝ)^j)).mul
      (hC₁.mul ((allBranchExterior_micro_inverse_envelope A c).pow j))).mul
        ((NatExponentialEnvelope.const 1 K).mul hpoly))).mul (NatExponentialEnvelope.const 1 ((4:ℝ)^j))

/-- The coefficient excluding the variable collision-slope power has a
quadratic exponential envelope, before any equality scale is chosen. -/
theorem allBranchExterior_near_local_prefactor_envelope (j G C : ℕ)
    (D c A C₀ C₁ K Aμ cμ : ℝ) :
    NatExponentialEnvelope 2 (fun N => allBranchExteriorNearLocalCost j N G C D c A
      (allBranchExteriorNearChartJetCost j N C₀ C₁ K (allBranchMicroRadius Aμ cμ N)) 1) := by
  have hpoly : NatExponentialEnvelope 1 (fun N => (3+3*N:ℝ)^j) :=
    ((NatExponentialEnvelope.const 1 3).add ((NatExponentialEnvelope.const 1 3).mul NatExponentialEnvelope.id)).pow j
  have hguard : NatExponentialEnvelope 1 (fun N =>
      2^j*((2^j*(G:ℝ)*(N:ℝ)^G*D)*(max 1 c⁻¹)^(2*j))) :=
    (NatExponentialEnvelope.const 1 ((2:ℝ)^j)).mul
      ((((NatExponentialEnvelope.const 1 ((2:ℝ)^j*(G:ℝ))).mul (NatExponentialEnvelope.id.pow G)).mul
        (NatExponentialEnvelope.const 1 D)).mul (NatExponentialEnvelope.const 1 ((max 1 c⁻¹)^(2*j))))
  have hcoeff : NatExponentialEnvelope 1 (fun N => (C:ℝ)*(N:ℝ)^C) :=
    (NatExponentialEnvelope.const 1 (C:ℝ)).mul (NatExponentialEnvelope.id.pow C)
  have hh := (hpoly.mul ((hguard.mul (allBranchExterior_near_cutoff_envelope j C₀ C₁ K Aμ cμ)).mul hcoeff)).mono_degree
    (by omega : 1 ≤ 2) |>.mul (allBranchExterior_near_numerator_envelope A j)
  convert hh using 1
  funext N
  simp only [allBranchExteriorNearLocalCost,one_pow,mul_one]
  ring

end
end IsingBulk.Tail
