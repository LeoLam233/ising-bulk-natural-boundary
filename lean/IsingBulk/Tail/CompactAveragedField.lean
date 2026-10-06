import IsingBulk.Tail.CompactFreezingDeterminant
import IsingBulk.Tail.AveragedPairField

/-! Cancellation-safe actual angular freezing field. Current pair sets can
exclude the distinguished coordinate before any averaging or derivative. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First
open scoped BigOperators
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

def complexCoordinateFunctional {N : ℕ} (A : Fin N → ℂ) : (Fin N → ℂ) →ₗ[ℝ] ℂ where
  toFun V := ∑ i, A i*V i
  map_add' V W := by simp [mul_add,Finset.sum_add_distrib]
  map_smul' c V := by simp [Complex.real_smul,Finset.mul_sum,mul_left_comm]

theorem complexCoordinateFunctional_single {N : ℕ} (A : Fin N → ℂ) (i : Fin N) (z : ℂ) :
    complexCoordinateFunctional A (Pi.single i z)=A i*z := by
  simp [complexCoordinateFunctional,Pi.single_apply,mul_ite]

def cancelledAngularPair {N : ℕ} (A : Fin N → ℂ) (Q C : ℂ) (i j : Fin N) : Fin N → ℂ :=
  Pi.single i (-Q*A j/C)+Pi.single j (Q*A i/C)

theorem cancelledAngularPair_functionals {N : ℕ} (A B : Fin N → ℂ) (Q C : ℂ)
    (i j : Fin N) {d : ℝ} (hC : C≠0) (hD : A i*B j-A j*B i=(d:ℂ)*C) :
    complexCoordinateFunctional A (cancelledAngularPair A Q C i j)=0 ∧
    complexCoordinateFunctional B (cancelledAngularPair A Q C i j)=d • Q := by
  simp only [cancelledAngularPair,map_add,complexCoordinateFunctional_single]
  constructor
  · ring
  · rw [Complex.real_smul]
    calc
      _ = Q*(A i*B j-A j*B i)/C := by ring
      _ = _ := by rw [hD]; field_simp

def currentPhaseParameterDerivative {N : ℕ} (f : SelectorFunctions) (r τ lam : ℝ)
    (s : ℂ) (θ : Fin N → ℝ) : ℂ := deriv (fun z => currentComplexPhase f r τ lam z θ) s

def currentAngularLogYCoefficient {N : ℕ} (f : SelectorFunctions) (r τ lam : ℝ)
    (θ : Fin N → ℝ) (i : Fin N) : ℂ := fderiv ℝ (unwrappedLogY f r τ lam) θ (Pi.single i 1)

def currentAngularPhaseCoefficient {N : ℕ} (f : SelectorFunctions) (r τ lam : ℝ)
    (s : ℂ) (θ : Fin N → ℝ) (i : Fin N) : ℂ :=
  fderiv ℝ (currentComplexPhase f r τ lam s) θ (Pi.single i 1)

def currentCancelledPairField {N : ℕ} (f : SelectorFunctions) (r τ lam : ℝ)
    (s : ℂ) (θ : Fin N → ℝ) (p : Fin N × Fin N) : Fin N → ℂ :=
  cancelledAngularPair (currentAngularLogYCoefficient f r τ lam θ)
    (currentPhaseParameterDerivative f r τ lam s θ)
    (currentAngularDividedDifference f r τ lam s p.1 p.2 θ) p.1 p.2

def fullAngularPairSet (N : ℕ) : Finset (Fin N × Fin N) :=
  Finset.univ.filter (fun p => p.1<p.2)

def freeAngularPairSet {N : ℕ} (q : Fin N) : Finset (Fin N × Fin N) :=
  (fullAngularPairSet N).filter (fun p => p.1≠q ∧ p.2≠q)

def currentAveragedField {N : ℕ} (P : Finset (Fin N × Fin N))
    (f : SelectorFunctions) (r τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ) : Fin N → ℂ :=
  cancelledAverageField P (fun p => θ p.1-θ p.2) (currentCancelledPairField f r τ lam s θ)

theorem currentCancelledPairField_freezes {N : ℕ} (hN : 0<N)
    (f : SelectorFunctions) (hf : RegularSelector f) {r τ lam : ℝ}
    (hr : 0<r) (hr1 : r<1) (hτ : 0≤τ) (hlam : 0≤lam)
    {s : ℂ} (hmargin : r⁻¹-r<(sourceS s).im) (θ : Fin N → ℝ) (p : Fin N × Fin N)
    (hC : currentAngularDividedDifference f r τ lam s p.1 p.2 θ≠0) :
    complexCoordinateFunctional (currentAngularLogYCoefficient f r τ lam θ)
      (currentCancelledPairField f r τ lam s θ p)=0 ∧
    complexCoordinateFunctional (currentAngularPhaseCoefficient f r τ lam s θ)
      (currentCancelledPairField f r τ lam s θ p)=
        (θ p.1-θ p.2) • currentPhaseParameterDerivative f r τ lam s θ := by
  have hdiv := (currentAngularDeterminant_smooth_division hN f hf hr hr1 hτ hlam hmargin p.1 p.2).2 θ
  exact cancelledAngularPair_functionals _ _ _ _ _ _ hC (by
    simpa only [currentAngularDeterminant,angularPairDeterminant,currentAngularLogYCoefficient,
      currentAngularPhaseCoefficient,Complex.real_smul] using hdiv)

theorem currentAveragedField_freezes {N : ℕ} (hN : 0<N)
    (P : Finset (Fin N × Fin N)) (f : SelectorFunctions) (hf : RegularSelector f) {r τ lam : ℝ}
    (hr : 0<r) (hr1 : r<1) (hτ : 0≤τ) (hlam : 0≤lam)
    {s : ℂ} (hmargin : r⁻¹-r<(sourceS s).im) (θ : Fin N → ℝ)
    (hS : pairSquareMass P (fun p => θ p.1-θ p.2)≠0)
    (hC : ∀ p∈P, currentAngularDividedDifference f r τ lam s p.1 p.2 θ≠0) :
    complexCoordinateFunctional (currentAngularLogYCoefficient f r τ lam θ)
      (currentAveragedField P f r τ lam s θ)=0 ∧
    complexCoordinateFunctional (currentAngularPhaseCoefficient f r τ lam s θ)
      (currentAveragedField P f r τ lam s θ)=currentPhaseParameterDerivative f r τ lam s θ := by
  apply cancelledAverageField_freezes_two P _ _ hS _ _ 0 _
  intro p hp _
  have hh := currentCancelledPairField_freezes hN f hf hr hr1 hτ hlam hmargin θ p (hC p hp)
  simpa only [smul_zero] using hh

theorem currentAveragedField_free_coordinate {N : ℕ} (q : Fin N)
    (f : SelectorFunctions) (r τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ) :
    currentAveragedField (freeAngularPairSet q) f r τ lam s θ q=0 := by
  unfold currentAveragedField cancelledAverageField
  rw [Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro p hp
  obtain ⟨_,hpq⟩ := Finset.mem_filter.mp hp
  simp only [Pi.smul_apply,currentCancelledPairField,cancelledAngularPair,Pi.add_apply,
    Pi.single_eq_of_ne (Ne.symm hpq.1),Pi.single_eq_of_ne (Ne.symm hpq.2),add_zero,smul_zero]

end
end IsingBulk.Tail
