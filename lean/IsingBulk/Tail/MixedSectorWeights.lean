import IsingBulk.Tail.MixedSectorDomain
import IsingBulk.Tail.PeriodicLieStages

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First Set
open scoped Topology ContDiff BigOperators

def originalMixedWeight {N : ℕ} (f : SelectorFunctions) (b outer inner : ℝ)
    (ho : 0<outer) (hi : 0< inner) (q : Fin N) (sigma : Fin N → Fin 3) (θ : Fin N → ℝ) : ℂ :=
  (angularSelector f θ*nestedSectorWeight b outer inner ho hi q sigma θ : ℝ)

def currentMixedWeight {N : ℕ} (f : SelectorFunctions) (b outer inner : ℝ)
    (ho : 0<outer) (hi : 0< inner) (qS a : Fin N) (sigma : Fin N → Fin 3) (τ : ℝ) (θ : Fin N → ℝ) : ℂ :=
  -2*Complex.I*(τ:ℂ)*(namedSelectorDerivative f qS θ*nestedSectorWeight b outer inner ho hi a sigma θ : ℝ)

theorem sectorLabel_periodic (b d : ℝ) (hd : 0<d) (a : Fin 3) :
    Function.Periodic (sectorLabel b d hd a) (2*Real.pi) := by
  obtain ⟨hL,hR,hB⟩ := sector_labels_periodic b d hd
  fin_cases a <;> simpa only [sectorLabel,Fin.isValue,↓reduceIte] using (by assumption)

theorem sectorAssignmentWeight_periodic {N : ℕ} (b d : ℝ) (hd : 0<d) (sigma : Fin N → Fin 3)
    (θ : Fin N → ℝ) (q : Fin N) :
    sectorAssignmentWeight b d hd sigma (Function.update θ q (θ q+2*Real.pi))=sectorAssignmentWeight b d hd sigma θ := by
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i=q
  · subst i
    simp only [Function.update_self]
    exact sectorLabel_periodic b d hd (sigma q) (θ q)
  · rw [Function.update_of_ne hi]

theorem sectorOuterAnchor_periodic {N : ℕ} (b d : ℝ) (hd : 0<d) (a : Fin N)
    (θ : Fin N → ℝ) (q : Fin N) :
    sectorOuterAnchor b d hd a (Function.update θ q (θ q+2*Real.pi))=sectorOuterAnchor b d hd a θ := by
  unfold sectorOuterAnchor
  rw [periodic_tuple_update (sector_labels_periodic b d hd).2.2]

theorem nestedSectorWeight_smooth {N : ℕ} (b outer inner : ℝ) (ho : 0<outer) (hi : 0< inner)
    (a : Fin N) (sigma : Fin N → Fin 3) : ContDiff ℝ ∞ (nestedSectorWeight b outer inner ho hi a sigma) :=
  (sectorOuterAnchor_smooth b outer ho a).mul (sector_assignment_smooth b inner hi sigma)

theorem nestedSectorWeight_periodic {N : ℕ} (b outer inner : ℝ) (ho : 0<outer) (hi : 0< inner)
    (a : Fin N) (sigma : Fin N → Fin 3) (θ : Fin N → ℝ) (q : Fin N) :
    nestedSectorWeight b outer inner ho hi a sigma (Function.update θ q (θ q+2*Real.pi))=
      nestedSectorWeight b outer inner ho hi a sigma θ := by
  unfold nestedSectorWeight
  rw [sectorOuterAnchor_periodic,sectorAssignmentWeight_periodic]

theorem namedSelectorDerivative_smooth {N : ℕ} (f : SelectorFunctions) (hf : RegularSelector f) (q : Fin N) :
    ContDiff ℝ ∞ (namedSelectorDerivative f q) := by
  have ha := hf.a_smooth
  have hd : ContDiff ℝ ∞ (deriv f.a) := ContDiff.deriv' (by simpa using ha)
  unfold namedSelectorDerivative
  fun_prop

theorem namedSelectorDerivative_periodic {N : ℕ} (f : SelectorFunctions) (hf : RegularSelector f)
    (a : Fin N) (θ : Fin N → ℝ) (q : Fin N) :
    namedSelectorDerivative f a (Function.update θ q (θ q+2*Real.pi))=namedSelectorDerivative f a θ := by
  have ha := periodic_tuple_update hf.a_periodic θ q
  have hd := periodic_tuple_update (periodic_derivative hf.a_periodic) θ q
  unfold namedSelectorDerivative
  rw [show deriv f.a (Function.update θ q (θ q+2*Real.pi) a)=deriv f.a (θ a) from congrFun hd a]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [show f.a (Function.update θ q (θ q+2*Real.pi) i)=f.a (θ i) from congrFun ha i]

theorem originalMixedWeight_smooth {N : ℕ} (f : SelectorFunctions) (hf : RegularSelector f)
    (b outer inner : ℝ) (ho : 0<outer) (hi : 0< inner) (q : Fin N) (sigma : Fin N → Fin 3) :
    ContDiff ℝ ∞ (originalMixedWeight f b outer inner ho hi q sigma) :=
  Complex.ofRealCLM.contDiff.comp ((angularSelector_contDiff f hf).mul (nestedSectorWeight_smooth b outer inner ho hi q sigma))

theorem currentMixedWeight_smooth {N : ℕ} (f : SelectorFunctions) (hf : RegularSelector f)
    (b outer inner : ℝ) (ho : 0<outer) (hi : 0< inner) (qS a : Fin N) (sigma : Fin N → Fin 3) (τ : ℝ) :
    ContDiff ℝ ∞ (currentMixedWeight f b outer inner ho hi qS a sigma τ) :=
  contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
    ((namedSelectorDerivative_smooth f hf qS).mul (nestedSectorWeight_smooth b outer inner ho hi a sigma)))

theorem originalMixedWeight_periodic {N : ℕ} (f : SelectorFunctions) (hf : RegularSelector f)
    (b outer inner : ℝ) (ho : 0<outer) (hi : 0< inner) (q : Fin N) (sigma : Fin N → Fin 3) :
    CoordinatePeriodic N (originalMixedWeight f b outer inner ho hi q sigma) := by
  intro θ i
  unfold originalMixedWeight
  rw [angularSelector_periodic f hf,nestedSectorWeight_periodic]

theorem currentMixedWeight_periodic {N : ℕ} (f : SelectorFunctions) (hf : RegularSelector f)
    (b outer inner : ℝ) (ho : 0<outer) (hi : 0< inner) (qS a : Fin N) (sigma : Fin N → Fin 3) (τ : ℝ) :
    CoordinatePeriodic N (currentMixedWeight f b outer inner ho hi qS a sigma τ) := by
  intro θ i
  unfold currentMixedWeight
  rw [namedSelectorDerivative_periodic f hf,nestedSectorWeight_periodic]

theorem originalMixedWeight_support {N : ℕ} (f : SelectorFunctions) (b outer inner : ℝ)
    (ho : 0<outer) (hi : 0< inner) (q : Fin N) (sigma : Fin N → Fin 3) :
    tsupport (originalMixedWeight f b outer inner ho hi q sigma) ⊆
      tsupport (fun θ => angularSelector f θ*nestedSectorWeight b outer inner ho hi q sigma θ) :=
  tsupport_comp_subset (g := Complex.ofReal) (by simp) _

theorem currentMixedWeight_support {N : ℕ} (f : SelectorFunctions) (b outer inner : ℝ)
    (ho : 0<outer) (hi : 0< inner) (qS a : Fin N) (sigma : Fin N → Fin 3) (τ : ℝ) :
    tsupport (currentMixedWeight f b outer inner ho hi qS a sigma τ) ⊆
      tsupport (fun θ => namedSelectorDerivative f qS θ*sectorAssignmentWeight b inner hi sigma θ) := by
  exact tsupport_mul_subset_right.trans ((tsupport_comp_subset (g := Complex.ofReal) (by simp) _).trans
    (named_nested_sector_support_subset f b outer inner ho hi qS a sigma))

theorem currentMixedWeight_density {N : ℕ} (f : SelectorFunctions) (b outer inner : ℝ)
    (ho : 0<outer) (hi : 0< inner) (qS a : Fin N) (sigma : Fin N → Fin 3)
    (r τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ) :
    currentMixedWeight f b outer inner ho hi qS a sigma τ θ*pulledDensity f r τ lam s θ=
      (nestedSectorWeight b outer inner ho hi a sigma θ:ℂ)*namedCurrentDensity f r τ lam s qS θ := by
  unfold currentMixedWeight namedCurrentDensity
  push_cast
  ring

end
end IsingBulk.Tail
