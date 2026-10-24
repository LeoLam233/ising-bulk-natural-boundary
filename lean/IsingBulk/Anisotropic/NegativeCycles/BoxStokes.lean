import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.MeasureTheory.Integral.DivergenceTheorem

/-! Actual Stokes transport for closed forms on a parameter box. No cycle equality
is a premise: the identity follows from the Bochner divergence theorem. -/
namespace IsingBulk.Anisotropic.NegativeCycles
noncomputable section
open Set MeasureTheory
open scoped BigOperators

abbrev ParameterSpace (n : ℕ) := Fin (n+1) → ℝ

def boxBoundaryFlux {n : ℕ}
    (ω : ParameterSpace n → ParameterSpace n [⋀^Fin n]→L[ℝ] ℂ)
    (a b : ParameterSpace n) : ℂ :=
  ∑ i : Fin (n+1),
    ((∫ x in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
       (-1:ℤ)^i.val • ω (i.insertNth (b i) x) (i.removeNth (fun k => (Pi.single k (1:ℝ) : ParameterSpace n)))) -
     ∫ x in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
       (-1:ℤ)^i.val • ω (i.insertNth (a i) x) (i.removeNth (fun k => (Pi.single k (1:ℝ) : ParameterSpace n))))

theorem boxBoundaryFlux_eq_zero {n : ℕ}
    (ω : ParameterSpace n → ParameterSpace n [⋀^Fin n]→L[ℝ] ℂ)
    {a b : ParameterSpace n} (hab : a≤b)
    (hω : ∀x∈Icc a b, DifferentiableAt ℝ ω x)
    (hclosed : ∀x∈Icc a b, extDeriv ω x=0) :
    boxBoundaryFlux ω a b=0 := by
  let e : Fin (n+1) → ParameterSpace n := fun k => (Pi.single k (1:ℝ) : ParameterSpace n)
  let f : Fin (n+1) → ParameterSpace n → ℂ :=
    fun i x => (-1:ℤ)^i.val • ω x (i.removeNth e)
  let f' : Fin (n+1) → ParameterSpace n → ParameterSpace n →L[ℝ] ℂ :=
    fun i x => (-1:ℤ)^i.val • fderiv ℝ (fun y => ω y (i.removeNth e)) x
  have hd (x) (hx : x∈Icc a b) (i : Fin (n+1)) : HasFDerivAt (f i) (f' i x) x := by
    have hh := ((hω x hx).hasFDerivAt.continuousAlternatingMap_apply_const
      (i.removeNth e)).differentiableAt
    exact hh.hasFDerivAt.const_smul ((-1:ℤ)^i.val)
  have hz (x) (hx : x∈Icc a b) : (∑ i, f' i x (e i))=0 := by
    change (∑ i, (-1:ℤ)^i.val • fderiv ℝ (fun y => ω y (i.removeNth e)) x (e i))=0
    rw [←extDeriv_apply (hω x hx) e,hclosed x hx]
    rfl
  have hi : IntegrableOn (fun x => ∑ i, f' i x (e i)) (Icc a b) :=
    (integrableOn_zero : IntegrableOn (fun _ : ParameterSpace n => (0:ℂ)) (Icc a b)).congr_fun
      (fun x hx => (hz x hx).symm) measurableSet_Icc
  have hh := integral_divergence_of_hasFDerivAt_off_countable' a b hab f f' ∅
    Set.countable_empty (fun i x hx => (hd x hx i).continuousAt.continuousWithinAt)
    (fun x hx i => hd x (by
      constructor <;> intro k
      · exact (hx.1 k (Set.mem_univ k)).1.le
      · exact (hx.1 k (Set.mem_univ k)).2.le) i) hi
  change (∫ x in Icc a b, ∑ i, f' i x (e i))=boxBoundaryFlux ω a b at hh
  rw [←hh]
  exact integral_eq_zero_of_ae (ae_restrict_of_forall_mem measurableSet_Icc hz)

theorem boxBoundaryFlux_eq_integral_extDeriv {n : ℕ}
    (ω : ParameterSpace n → ParameterSpace n [⋀^Fin n]→L[ℝ] ℂ)
    {a b : ParameterSpace n} (hab : a≤b)
    (hω : ∀x∈Icc a b, DifferentiableAt ℝ ω x)
    (hiω : IntegrableOn (fun x => extDeriv ω x (fun k => (Pi.single k (1:ℝ) : ParameterSpace n))) (Icc a b)) :
    boxBoundaryFlux ω a b=
      ∫ x in Icc a b, extDeriv ω x (fun k => (Pi.single k (1:ℝ) : ParameterSpace n)) := by
  let e : Fin (n+1) → ParameterSpace n := fun k => (Pi.single k (1:ℝ) : ParameterSpace n)
  let f : Fin (n+1) → ParameterSpace n → ℂ :=
    fun i x => (-1:ℤ)^i.val • ω x (i.removeNth e)
  let f' : Fin (n+1) → ParameterSpace n → ParameterSpace n →L[ℝ] ℂ :=
    fun i x => (-1:ℤ)^i.val • fderiv ℝ (fun y => ω y (i.removeNth e)) x
  have hd (x) (hx : x∈Icc a b) (i : Fin (n+1)) : HasFDerivAt (f i) (f' i x) x := by
    have hh := ((hω x hx).hasFDerivAt.continuousAlternatingMap_apply_const
      (i.removeNth e)).differentiableAt
    exact hh.hasFDerivAt.const_smul ((-1:ℤ)^i.val)
  have hz (x) (hx : x∈Icc a b) : (∑ i, f' i x (e i))=extDeriv ω x e := by
    change (∑ i, (-1:ℤ)^i.val • fderiv ℝ (fun y => ω y (i.removeNth e)) x (e i))=_
    exact (extDeriv_apply (hω x hx) e).symm
  have hi : IntegrableOn (fun x => ∑ i, f' i x (e i)) (Icc a b) :=
    hiω.congr_fun (fun x hx => (hz x hx).symm) measurableSet_Icc
  have hh := integral_divergence_of_hasFDerivAt_off_countable' a b hab f f' ∅
    Set.countable_empty (fun i x hx => (hd x hx i).continuousAt.continuousWithinAt)
    (fun x hx i => hd x (by
      constructor <;> intro k
      · exact (hx.1 k (Set.mem_univ k)).1.le
      · exact (hx.1 k (Set.mem_univ k)).2.le) i) hi
  change (∫ x in Icc a b, ∑ i, f' i x (e i))=boxBoundaryFlux ω a b at hh
  rw [←hh]
  exact setIntegral_congr_fun measurableSet_Icc hz

end
end IsingBulk.Anisotropic.NegativeCycles
