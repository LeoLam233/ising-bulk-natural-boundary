import IsingBulk.HT22.Anchor.AmplitudeJets
import IsingBulk.HT22.Tail.SeedCalculus
namespace IsingBulk.HT22.Anchor
noncomputable section
open IsingBulk.Preferred22 IsingBulk.HT22.Geometry
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Literal fixed-v odd amplitude, including the signed product resolvent. -/
def fixedAmplitude {N : ℕ} (σ t : ℂ) (v : Fin N → ℂ) : ℂ :=
  ((1+σ*Tail.regularProductPhase t v)/(1-σ*Tail.regularProductPhase t v))*
    (Tail.regularBorderedKernel t v).det * (∏ i,Tail.regularOneBody t (v i)) /
    ((N.factorial:ℂ)*(2*Real.pi:ℂ)^(N-1))

theorem ordinaryPair_moving_adapter (t v w : ℂ) :
    ordinaryPair t (v-preferredMovingBranch t) (w-preferredMovingBranch t) =
      Algebra.ordinaryEntry
        (Complex.exp (Complex.I*regularInverse t v))
        (Complex.exp (Complex.I*regularInverse t w))
        (Complex.exp (-Complex.I*regularPhase t v))
        (Complex.exp (-Complex.I*regularPhase t w)) := by
  simp only [ordinaryPair,preferredRegularDiskRoot,←regularInverse_moving_adapter,
    ←Tail.regularPhase_moving_adapter]

theorem fixedAmplitude_moving_adapter {N : ℕ} (σ t : ℂ) (v : Fin N → ℂ) :
    fixedAmplitude σ t v=amplitude σ t (fun i => v i-preferredMovingBranch t) := by
  have hk : borderedKernel t (fun i => v i-preferredMovingBranch t)=Tail.regularBorderedKernel t v := by
    unfold borderedKernel Tail.regularBorderedKernel Algebra.constantBorderFirst
    simp_rw [ordinaryPair_moving_adapter]
  have hz : Tail.regularProductPhase t v=
      ∏ i,preferredRegularDiskRoot t (v i-preferredMovingBranch t) := by
    simp only [Tail.regularProductPhase,preferredRegularDiskRoot,
      ←Tail.regularPhase_moving_adapter,Finset.mul_sum,Complex.exp_sum]
  simp only [fixedAmplitude,amplitude,hk,hz,Tail.regularOneBody_moving_adapter]

/-- This is an equality of the actual source scalar, not an identification
of fixed-v and moving-q parameter derivatives. -/
theorem fixedAmplitude_source_adapter {N : ℕ} (σ : ℂ) (τ : ℝ) (p m : ℝ → ℝ)
    (t : ℂ) (θ : Fin N → ℝ) :
    fixedAmplitude σ t (Tail.sourceCoordinate τ p m t θ)=
      amplitude σ t (preferredSourceCoordinate τ p m t θ) := by
  rw [fixedAmplitude_moving_adapter]
  simp only [Tail.sourceCoordinate_moving_adapter]
end
end IsingBulk.HT22.Anchor
