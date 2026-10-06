import IsingBulk.Tail.LeftCompactSourceJets
import IsingBulk.Tail.CompactAveragedField

/-! Joint real smoothness and complex parameter differentiability for the
literal compact source factors, on the genuine damping domain. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First Set
open scoped Topology ContDiff BigOperators
set_option backward.isDefEq.respectTransparency false

def compactSourceDomain (N : ℕ) (r : ℝ) : Set (ℂ × (Fin N → ℝ)) :=
  dampingDomain r ×ˢ univ

theorem compactSourceDomain_isOpen (N : ℕ) (r : ℝ) : IsOpen (compactSourceDomain N r) :=
  (dampingDomain_isOpen r).prod isOpen_univ

theorem compactSource_y_smooth {N : ℕ} (f : SelectorFunctions) (hf : RegularSelector f)
    (r τ lam : ℝ) (i : Fin N) :
    ParameterSmoothOn (compactSourceDomain N r) (fun _ θ => deformedPoint f r τ lam θ i) :=
  ParameterSmoothOn.angular _ _ (deformedPoint_fixed_contDiff f r τ lam hf.p_smooth hf.m_smooth i)

theorem compactSource_W_smooth {N : ℕ} (f : SelectorFunctions) (hf : RegularSelector f)
    {r : ℝ} (hr : 0 < r) (τ lam : ℝ) (i : Fin N) :
    ParameterSmoothOn (compactSourceDomain N r) (fun s θ => sourceW s (deformedPoint f r τ lam θ i)) := by
  let Ω := compactSourceDomain N r
  have hs := ParameterSmoothOn.parameter Ω
  have hy := compactSource_y_smooth f hf r τ lam i
  exact (hs.add (hs.inv (fun _ h => h.1.1))).sub
    ((hy.add (hy.inv (fun p _ => deformedPoint_nonzero f hr.ne' τ lam p.2 i))).div
      (ParameterSmoothOn.const Ω 2) (by intro p _; norm_num))

theorem compactSource_phase_smooth {N : ℕ} (hN : 0 < N)
    (f : SelectorFunctions) (hf : RegularSelector f) {r τ lam : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ) (hlam : 0 ≤ lam) :
    ParameterSmoothOn (compactSourceDomain N r) (currentComplexPhase f r τ lam) := by
  apply ParameterSmoothOn.sum Finset.univ
  intro i _
  exact (compactSource_W_smooth f hf hr τ lam i).complex_comp continuedPhase
    (fun p hp => continuedPhase_analyticAt_upper
      (deformed_sourceW_upper_on_damping hN f hf hr hr1 hτ hlam hp.1 p.2 i))

theorem compactSource_logY_smooth {N : ℕ} (f : SelectorFunctions) (hf : RegularSelector f)
    (r τ lam : ℝ) :
    ParameterSmoothOn (compactSourceDomain N r) (fun (_ : ℂ) (θ : Fin N → ℝ) => unwrappedLogY f r τ lam θ) :=
  ParameterSmoothOn.angular _ _ (unwrappedLogY_contDiff f r τ lam hf.p_smooth hf.m_smooth)

theorem compactSource_Y_smooth {N : ℕ} (f : SelectorFunctions) (hf : RegularSelector f)
    (r τ lam : ℝ) :
    ParameterSmoothOn (compactSourceDomain N r) (fun _ θ => coordinateProduct (deformedPoint (N := N) f r τ lam θ)) :=
  ParameterSmoothOn.prod Finset.univ _ (fun i _ => compactSource_y_smooth f hf r τ lam i)

theorem compactSource_selectedRoot_smooth {N : ℕ} (hN : 0 < N)
    (f : SelectorFunctions) (hf : RegularSelector f) {r τ lam : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ) (hlam : 0 ≤ lam) (i : Fin N) :
    ParameterSmoothOn (compactSourceDomain N r)
      (fun s θ => selectedContinuedRoot s (deformedPoint f r τ lam θ i)) :=
  (compactSource_W_smooth f hf hr τ lam i).complex_comp continuedRoot
    (fun p hp => continuedRoot_analyticAt (Or.inl (Or.inl
      (deformed_sourceW_upper_on_damping hN f hf hr hr1 hτ hlam hp.1 p.2 i))))

theorem compactSource_root_smooth {N : ℕ} (hN : 0 < N)
    (f : SelectorFunctions) (hf : RegularSelector f) {r τ lam : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ) (hlam : 0 ≤ lam) (i : Fin N) :
    ParameterSmoothOn (compactSourceDomain N r)
      (fun s θ => globalRoot s (deformedPoint f r τ lam θ i)) := by
  apply (compactSource_selectedRoot_smooth hN f hf hr hr1 hτ hlam i).congr
    (compactSourceDomain_isOpen N r)
  intro p hp
  exact (continuedRoot_eq_interiorRoot
    (deformed_sourceW_upper_on_damping hN f hf hr hr1 hτ hlam hp.1 p.2 i)).symm

theorem compactSource_Z_smooth {N : ℕ} (hN : 0 < N)
    (f : SelectorFunctions) (hf : RegularSelector f) {r τ lam : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ) (hlam : 0 ≤ lam) :
    ParameterSmoothOn (compactSourceDomain N r)
      (fun s θ => coordinateProduct (fun i => globalRoot s (deformedPoint f r τ lam θ i))) :=
  ParameterSmoothOn.prod Finset.univ _ (fun i _ => compactSource_root_smooth hN f hf hr hr1 hτ hlam i)

theorem compactSource_kernel_smooth {N : ℕ} (hN : 0 < N)
    (f : SelectorFunctions) (hf : RegularSelector f) {r τ lam : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ) (hlam : 0 ≤ lam) :
    ParameterSmoothOn (compactSourceDomain N r) (mixedSimpleKernel f r τ lam) := by
  let Ω := compactSourceDomain N r
  have hZ := compactSource_Z_smooth hN f hf hr hr1 hτ hlam
  have hY := compactSource_Y_smooth (N := N) f hf r τ lam
  exact (((ParameterSmoothOn.const Ω 1).sub hZ).inv (fun p hp =>
    one_sub_coordinateProduct_ne_zero hN (fun i => interiorRoot_norm_lt_one
      (deformed_sourceW_upper_on_damping hN f hf hr hr1 hτ hlam hp.1 p.2 i)))).mul
    (((ParameterSmoothOn.const Ω 1).sub hY).inv (fun p _ =>
      homotopy_y_gap_nonzero hN f hr hr1 hτ hlam p.2 hf.p_nonneg hf.m_le_one))

end
end IsingBulk.Tail
