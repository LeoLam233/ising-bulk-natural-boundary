import IsingBulk.Tail.CompactPhaseRectangle
import IsingBulk.Tail.CompactRetractionJets

/-! Exact permutation symmetry of the actual coupled source phase. The
occupancy sum and every off-diagonal coupling are retained. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First
open scoped BigOperators

theorem occupancy_equiv {N : ℕ} (p : Fin N → ℝ) (σ : Equiv.Perm (Fin N)) :
    occupancy (p ∘ σ)=occupancy p := by
  unfold occupancy
  exact Equiv.sum_comp σ p

theorem deformedPoint_equiv {N : ℕ} (f : SelectorFunctions) (r τ lam : ℝ)
    (θ : Fin N → ℝ) (σ : Equiv.Perm (Fin N)) (i : Fin N) :
    deformedPoint f r τ lam (θ ∘ σ) i=deformedPoint f r τ lam θ (σ i) := by
  have hP : occupancy (fun j => f.p ((θ ∘ σ) j))=occupancy (fun j => f.p (θ j)) :=
    occupancy_equiv (fun j => f.p (θ j)) σ
  unfold deformedPoint retractionShift
  rw [hP]
  rfl

def currentComplexPhase {N : ℕ} (f : SelectorFunctions) (r τ lam : ℝ) (s : ℂ)
    (θ : Fin N → ℝ) : ℂ :=
  ∑ i, continuedPhase (sourceW s (deformedPoint f r τ lam θ i))

theorem currentComplexPhase_equiv {N : ℕ} (f : SelectorFunctions) (r τ lam : ℝ) (s : ℂ)
    (θ : Fin N → ℝ) (σ : Equiv.Perm (Fin N)) :
    currentComplexPhase f r τ lam s (θ ∘ σ)=currentComplexPhase f r τ lam s θ := by
  unfold currentComplexPhase
  simp_rw [deformedPoint_equiv]
  exact Equiv.sum_comp σ (fun i => continuedPhase (sourceW s (deformedPoint f r τ lam θ i)))

theorem currentUnwrappedPhase_eq_re {N : ℕ} (f : SelectorFunctions) (r τ lam : ℝ) (s : ℂ)
    (θ : Fin N → ℝ) : currentUnwrappedPhase f r τ lam s θ=(currentComplexPhase f r τ lam s θ).re := by
  simp only [currentUnwrappedPhase,currentComplexPhase,Complex.re_sum]

theorem currentUnwrappedPhase_equiv {N : ℕ} (f : SelectorFunctions) (r τ lam : ℝ) (s : ℂ)
    (θ : Fin N → ℝ) (σ : Equiv.Perm (Fin N)) :
    currentUnwrappedPhase f r τ lam s (θ ∘ σ)=currentUnwrappedPhase f r τ lam s θ := by
  rw [currentUnwrappedPhase_eq_re,currentComplexPhase_equiv,currentUnwrappedPhase_eq_re]

def unwrappedLogY {N : ℕ} (f : SelectorFunctions) (r τ lam : ℝ) (θ : Fin N → ℝ) : ℂ :=
  (∑ i, ((Real.log r+lam*retractionShift τ (fun j => f.p (θ j)) (fun j => f.m (θ j)) i:ℝ):ℂ))+
    Complex.I*(∑ i, (θ i:ℂ))

theorem unwrappedLogY_equiv {N : ℕ} (f : SelectorFunctions) (r τ lam : ℝ)
    (θ : Fin N → ℝ) (σ : Equiv.Perm (Fin N)) :
    unwrappedLogY f r τ lam (θ ∘ σ)=unwrappedLogY f r τ lam θ := by
  have hP : occupancy (fun j => f.p ((θ ∘ σ) j))=occupancy (fun j => f.p (θ j)) :=
    occupancy_equiv (fun j => f.p (θ j)) σ
  unfold unwrappedLogY retractionShift
  rw [hP]
  congr 1
  · exact Equiv.sum_comp σ (fun i => ((Real.log r+lam*retractionShift τ
      (fun j => f.p (θ j)) (fun j => f.m (θ j)) i:ℝ):ℂ))
  · congr 1
    exact Equiv.sum_comp σ (fun i => (θ i:ℂ))


theorem unwrappedLogY_exp {N : ℕ} (f : SelectorFunctions) {r : ℝ} (hr : 0<r)
    (τ lam : ℝ) (θ : Fin N → ℝ) :
    Complex.exp (unwrappedLogY f r τ lam θ)=coordinateProduct (deformedPoint f r τ lam θ) := by
  unfold unwrappedLogY coordinateProduct
  rw [Finset.mul_sum,← Finset.sum_add_distrib,Complex.exp_sum]
  apply Finset.prod_congr rfl
  intro i _
  rw [deformedPoint_polar f hr τ lam θ i]
  congr 2
  ring

end
end IsingBulk.Tail
