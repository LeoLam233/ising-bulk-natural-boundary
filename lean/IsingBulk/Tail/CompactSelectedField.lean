import IsingBulk.Tail.CompactKernelTransport

/-! The selected-pair representation of compact freezing. Its only pole is
the actual angular determinant; all regularity is local to its nonzero set.
This representation permits polynomial selected-pair weights to cancel the
pole without requiring derivative estimates for a divided determinant. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Lie Set Filter
open scoped Topology BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def currentSelectedPairField {N : ℕ} (f : SelectorFunctions) (r τ lam : ℝ)
    (i j : Fin N) (s : ℂ) (θ : Fin N → ℝ) : Fin N → ℂ :=
  cancelledAngularPair (currentAngularLogYCoefficient f r τ lam θ)
    (currentPhaseParameterDerivative f r τ lam s θ)
    (currentAngularDeterminant f r τ lam s i j θ) i j

theorem compactSource_determinant_smooth {N : ℕ} (hN : 0 < N)
    (f : SelectorFunctions) (hf : RegularSelector f) {r τ lam : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ) (hlam : 0 ≤ lam) (i j : Fin N) :
    ParameterSmoothOn (compactSourceDomain N r)
      (fun s θ => currentAngularDeterminant f r τ lam s i j θ) := by
  have hΩ := compactSourceDomain_isOpen N r
  have hA := compactSource_logY_smooth (N := N) f hf r τ lam
  have hB := compactSource_phase_smooth hN f hf hr hr1 hτ hlam
  exact ((hA.angularDirection hΩ (Pi.single i 1)).mul (hB.angularDirection hΩ (Pi.single j 1))).sub
    ((hA.angularDirection hΩ (Pi.single j 1)).mul (hB.angularDirection hΩ (Pi.single i 1)))

def compactSelectedDomain {N : ℕ} (f : SelectorFunctions) (r τ lam : ℝ) (i j : Fin N) :
    Set (ℂ × (Fin N → ℝ)) :=
  compactSourceDomain N r ∩ {p | currentAngularDeterminant f r τ lam p.1 i j p.2 ≠ 0}

theorem compactSelectedDomain_isOpen {N : ℕ} (hN : 0 < N)
    (f : SelectorFunctions) (hf : RegularSelector f) {r τ lam : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ) (hlam : 0 ≤ lam) (i j : Fin N) :
    IsOpen (compactSelectedDomain f r τ lam i j) := by
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  have hD := compactSource_determinant_smooth hN f hf hr hr1 hτ hlam i j
  filter_upwards [(compactSourceDomain_isOpen N r).mem_nhds hp.1,
    (hD p hp.1).1.continuousAt.eventually_ne hp.2] with z hz hd
  exact ⟨hz,hd⟩

theorem currentSelectedPairField_smooth {N : ℕ} (hN : 0 < N)
    (f : SelectorFunctions) (hf : RegularSelector f) {r τ lam : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ) (hlam : 0 ≤ lam) (i j l : Fin N) :
    ParameterSmoothOn (compactSelectedDomain f r τ lam i j)
      (fun s θ => currentSelectedPairField f r τ lam i j s θ l) := by
  let Ω := compactSelectedDomain f r τ lam i j
  have hOpen := compactSourceDomain_isOpen N r
  have hQ : ParameterSmoothOn Ω (currentPhaseParameterDerivative f r τ lam) :=
    fun p hp => ((compactSource_phase_smooth hN f hf hr hr1 hτ hlam).paramDeriv hOpen) p hp.1
  have hA (k : Fin N) : ParameterSmoothOn Ω (fun _ θ => currentAngularLogYCoefficient f r τ lam θ k) :=
    fun p hp => ((compactSource_logY_smooth f hf r τ lam).angularDirection hOpen (Pi.single k 1)) p hp.1
  have hD : ParameterSmoothOn Ω (fun s θ => currentAngularDeterminant f r τ lam s i j θ) :=
    fun p hp => (compactSource_determinant_smooth hN f hf hr hr1 hτ hlam i j) p hp.1
  have hLeft := (((ParameterSmoothOn.const Ω (-1)).mul hQ).mul (hA j)).div hD (fun _ hp => hp.2)
  have hRight := (hQ.mul (hA i)).div hD (fun _ hp => hp.2)
  have h1 : ParameterSmoothOn Ω (fun s θ => if l=i then
      -currentPhaseParameterDerivative f r τ lam s θ*currentAngularLogYCoefficient f r τ lam θ j /
        currentAngularDeterminant f r τ lam s i j θ else 0) := by
    by_cases hli : l=i
    · simpa only [hli,ite_true,neg_one_mul] using hLeft
    · simpa only [hli,ite_false] using ParameterSmoothOn.const Ω 0
  have h2 : ParameterSmoothOn Ω (fun s θ => if l=j then
      currentPhaseParameterDerivative f r τ lam s θ*currentAngularLogYCoefficient f r τ lam θ i /
        currentAngularDeterminant f r τ lam s i j θ else 0) := by
    by_cases hlj : l=j
    · simpa only [hlj,ite_true] using hRight
    · simpa only [hlj,ite_false] using ParameterSmoothOn.const Ω 0
  simpa only [currentSelectedPairField,cancelledAngularPair,Pi.add_apply,Pi.single_apply] using h1.add h2

theorem currentSelectedPairField_free_coordinate {N : ℕ} (f : SelectorFunctions)
    (r τ lam : ℝ) (i j q : Fin N) (hiq : i ≠ q) (hjq : j ≠ q) (s : ℂ) (θ : Fin N → ℝ) :
    currentSelectedPairField f r τ lam i j s θ q=0 := by
  simp [currentSelectedPairField,cancelledAngularPair,Pi.single_eq_of_ne (Ne.symm hiq),
    Pi.single_eq_of_ne (Ne.symm hjq)]

theorem currentSelectedPairField_kernel_frozen {n : ℕ}
    (f : SelectorFunctions) (hf : RegularSelector f) {r τ lam : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ) (hlam : 0 ≤ lam) (i j : Fin (n+1))
    {s : ℂ} (hs : s ∈ dampingDomain r) (θ : AngularSpace n)
    (hD : currentAngularDeterminant f r τ lam s i j θ ≠ 0) :
    transport (currentSelectedPairField f r τ lam i j) (mixedSimpleKernel f r τ lam) s θ=0 := by
  have hh := cancelledAngularPair_functionals (currentAngularLogYCoefficient f r τ lam θ)
    (currentAngularPhaseCoefficient f r τ lam s θ) (currentPhaseParameterDerivative f r τ lam s θ)
    (currentAngularDeterminant f r τ lam s i j θ) i j (d := 1) hD (by
      simp only [Complex.ofReal_one,one_mul,currentAngularDeterminant,angularPairDeterminant,
        currentAngularLogYCoefficient,currentAngularPhaseCoefficient])
  have hy : (∑ k,currentSelectedPairField f r τ lam i j s θ k*
      fderiv ℝ (unwrappedLogY f r τ lam) θ (Pi.single k 1))=0 := by
    simpa only [complexCoordinateFunctional,LinearMap.coe_mk,AddHom.coe_mk,
      currentAngularLogYCoefficient,currentSelectedPairField,mul_comm] using hh.1
  have hz : (∑ k,currentSelectedPairField f r τ lam i j s θ k*
      fderiv ℝ (currentComplexPhase f r τ lam s) θ (Pi.single k 1))=
        deriv (fun z => currentComplexPhase f r τ lam z θ) s := by
    simpa only [complexCoordinateFunctional,LinearMap.coe_mk,AddHom.coe_mk,one_smul,
      currentAngularPhaseCoefficient,currentPhaseParameterDerivative,currentSelectedPairField,mul_comm] using hh.2
  apply compact_kernel_frozen_of_phases _ f hf hr hr1 hτ hlam hs θ
  constructor
  · simp only [transport,deriv_const,hy,sub_self]
  · simp only [transport,hz,sub_self]

end
end IsingBulk.Tail
