import IsingBulk.First.CompactParameterIntegral
import IsingBulk.First.JointPoleRegularity

/-! All parameter derivatives of an actual compact shape integral. A fixed
continuous shape weight is kept outside every complex derivative. -/
namespace IsingBulk.First
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def jointParameterJet (F : ℂ × E → ℂ) (k : ℕ) : ℂ × E → ℂ :=
  parameterDeriv^[k] F

theorem jointParameterJet_analyticAt {F : ℂ × E → ℂ} {p : ℂ × E}
    (hF : AnalyticAt ℂ F p) (k : ℕ) : AnalyticAt ℂ (jointParameterJet F k) p := by
  induction k with
  | zero => exact hF
  | succ k ih =>
    simpa only [jointParameterJet, Function.iterate_succ', Function.comp_apply] using parameterDeriv_analyticAt ih

omit [NormedAddCommGroup E] [NormedSpace ℂ E] in
theorem jointParameterJet_eq (F : ℂ × E → ℂ) (k : ℕ) (p : ℂ × E) :
    jointParameterJet F k p = (deriv^[k] (fun s => F (s,p.2))) p.1 := by
  induction k generalizing p with
  | zero => rfl
  | succ k ih =>
    simp only [jointParameterJet, Function.iterate_succ', Function.comp_apply, parameterDeriv]
    congr 1
    funext s
    exact ih (s,p.2)

theorem compact_analytic_shape_integral_iteratedDeriv
    {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasureOnCompacts μ] {K : Set X} (hK : IsCompact K)
    {U : Set ℂ} (hU : IsOpen U) (F : ℂ × E → ℂ) (psi : X → E) (hpsi : Continuous psi)
    (chi : X → ℂ) (hchi : Continuous chi)
    (hF : ∀ s ∈ U, ∀ x ∈ K, AnalyticAt ℂ F (s,psi x)) (k : ℕ) :
    ∀ s ∈ U,
      (deriv^[k] (fun z => ∫ x in K, chi x*F (z,psi x) ∂μ)) s =
        ∫ x in K, chi x*(deriv^[k] (fun z => F (z,psi x))) s ∂μ := by
  let H := fun j s x => chi x*jointParameterJet F j (s,psi x)
  have hc (j : ℕ) : ContinuousOn (fun p : ℂ × X => H j p.1 p.2) (U ×ˢ K) := by
    intro p hp
    have ha : ContinuousAt (jointParameterJet F j) (p.1,psi p.2) :=
      (jointParameterJet_analyticAt (hF p.1 hp.1 p.2 hp.2) j).continuousAt
    have hg : Continuous (fun q : ℂ × X => (q.1,psi q.2)) :=
      continuous_fst.prodMk (hpsi.comp continuous_snd)
    have hcomp : ContinuousAt (fun q : ℂ × X => jointParameterJet F j (q.1,psi q.2)) p :=
      ha.comp (f := fun q : ℂ × X => (q.1,psi q.2)) hg.continuousAt
    have hw : ContinuousAt (fun q : ℂ × X => chi q.2) p :=
      (hchi.comp continuous_snd).continuousAt
    exact (hw.mul hcomp).continuousWithinAt
  have hd (j : ℕ) (s : ℂ) (hs : s ∈ U) (x : X) (hx : x ∈ K) :
      HasDerivAt (fun z => H j z x) (H (j+1) s x) s := by
    have ha := (jointParameterJet_analyticAt (hF s hs x hx) j).comp
      (f := fun z : ℂ => (z,psi x)) (analyticAt_id.prod analyticAt_const)
    convert ha.differentiableAt.hasDerivAt.const_mul (chi x) using 1 <;>
      simp only [H, jointParameterJet, Function.iterate_succ', Function.comp_def, parameterDeriv]
  have hstep (j : ℕ) (s : ℂ) (hs : s ∈ U) :
      HasDerivAt (fun z => ∫ x in K, H j z x ∂μ) (∫ x in K, H (j+1) s x ∂μ) s :=
    hasDerivAt_compact_integral hK (hU.mem_nhds hs) (H j) (H (j+1)) (hc j) (hc (j+1)) (hd j)
  have hjet : ∀ j : ℕ, ∀ s ∈ U,
      (deriv^[j] (fun z => ∫ x in K, H 0 z x ∂μ)) s = ∫ x in K, H j s x ∂μ := by
    intro j
    induction j with
    | zero => intro s hs; rfl
    | succ j ih =>
      intro s hs
      rw [Function.iterate_succ', Function.comp_apply]
      have heq : (deriv^[j] (fun z => ∫ x in K, H 0 z x ∂μ)) =ᶠ[𝓝 s]
          (fun z => ∫ x in K, H j z x ∂μ) :=
        (show ∀ᶠ z in 𝓝 s, z ∈ U from hU.mem_nhds hs).mono (fun z hz => ih z hz)
      rw [heq.deriv_eq]
      exact (hstep j s hs).deriv
  intro s hs
  simpa only [H, jointParameterJet_eq, Function.iterate_zero_apply] using hjet k s hs

end
end IsingBulk.First
