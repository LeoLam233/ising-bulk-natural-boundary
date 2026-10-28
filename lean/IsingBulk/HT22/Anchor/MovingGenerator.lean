import IsingBulk.HT22.Anchor.Recurrence
import IsingBulk.HT22.Anchor.BranchJets
namespace IsingBulk.HT22.Anchor
noncomputable section
open IsingBulk.Preferred22 IsingBulk.HT22.Geometry IsingBulk.HT22.Tail Filter
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false

/-- Correct moving-q velocity: subtract b' in EVERY coordinate. -/
def movingSourceResidual {N : ℕ} (anchor : Fin N) (τ : ℝ) (p m : ℝ → ℝ)
    (t : ℂ) (θ : Fin N → ℝ) (i : Fin N) : ℂ :=
  residualField anchor t (sourceCoordinate τ p m t θ) i-deriv preferredMovingBranch t

def movingTransportStep {N : ℕ} (anchor : Fin N) (τ : ℝ) (p m : ℝ → ℝ)
    (F : ℂ → (Fin N → ℝ) → ℂ) (t : ℂ) (θ : Fin N → ℝ) : ℂ :=
  preferredParameterFrame τ p m F t θ+
    (∑ a,movingSourceResidual anchor τ p m t θ a*preferredCoordinateFrame τ p m a F t θ)+
    (∑ a,preferredCoordinateFrame τ p m a (fun s x => movingSourceResidual anchor τ p m s x a) t θ)*F t θ

theorem movingDivergence_eq {N : ℕ} (anchor : Fin N) (τ : ℝ) (p m : ℝ → ℝ)
    (t : ℂ) (θ : Fin N → ℝ) :
    (∑ a,preferredCoordinateFrame τ p m a (fun s x => movingSourceResidual anchor τ p m s x a) t θ)=
      regularDivergence anchor τ p m t θ := by
  unfold regularDivergence
  simp only [movingSourceResidual,preferredCoordinateFrame,Tail.coordinateFrame,
    Tail.inverseV_moving_adapter,sourceCoordinate_moving_adapter,deriv_sub_const]

theorem movingAngularRepresentative_eq {N : ℕ} (anchor : Fin N) (τ δ : ℝ) (p m : ℝ → ℝ)
    (t : ℂ) (θ : Fin N → ℝ) (h : PreferredFramePoint τ δ p m t θ) :
    preferredAngularRepresentative (preferredContourMatrix τ p m θ)
      (fun i => preferredSourceUDot t (preferredSourceCoordinate τ p m t θ i))
      (fun i => preferredSourceUQ t (preferredSourceCoordinate τ p m t θ i))
      (movingSourceResidual anchor τ p m t θ)=angularField anchor τ p m t θ := by
  have ht (i : Fin N) := inverseT_moving_adapter t (sourceCoordinate τ p m t θ i)
    (framePoint_inverse_analytic h i) (preferredMovingBranch_analyticAt_upper t h.trace_im).differentiableAt
  simp only [sourceCoordinate_moving_adapter,inverseV_moving_adapter] at ht
  unfold angularField preferredAngularRepresentative movingSourceResidual
  funext i
  simp only [Matrix.mulVec,dotProduct,inverseV_moving_adapter,sourceCoordinate_moving_adapter,ht]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem movingTransportStep_eq {N : ℕ} (anchor : Fin N) (τ δ : ℝ) (p m : ℝ → ℝ)
    (t : ℂ) (θ : Fin N → ℝ) (h : PreferredFramePoint τ δ p m t θ)
    (F : ℂ → (Fin N → ℝ) → ℂ) :
    movingTransportStep anchor τ p m F t θ=regularTransportStep anchor τ p m F t θ := by
  have hdiv := movingDivergence_eq anchor τ p m t θ
  rw [movingTransportStep,hdiv,regularTransportStep]
  rw [←movingAngularRepresentative_eq anchor τ δ p m t θ h]
  unfold preferredParameterFrame preferredCoordinateFrame preferredAngularRepresentative
  simp only [Matrix.mulVec,dotProduct,Finset.mul_sum,Finset.sum_mul,neg_mul,
    Finset.sum_neg_distrib,sub_neg_eq_add]
  congr 1
  rw [add_assoc]
  congr 1
  rw [Finset.sum_comm (f := fun a i => movingSourceResidual anchor τ p m t θ a *
    ((preferredContourMatrix τ p m θ)⁻¹ i a *
      preferredSourceUQ t (preferredSourceCoordinate τ p m t θ a) *
      deriv (fun x : ℝ => F t (Function.update θ i x)) (θ i)))]
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  ring
end
end IsingBulk.HT22.Anchor
