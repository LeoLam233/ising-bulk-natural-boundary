import IsingBulk.Joint.RegularEdges.FamilyFiniteCoefficients
import IsingBulk.Joint.RegularEdges.FamilyFiniteComplement

namespace IsingBulk.Joint.RegularEdges
noncomputable section
open Set Filter Metric MeasureTheory IsingBulk.First IsingBulk.Tail
open IsingBulk.Anisotropic.RegularEdges
open scoped Topology BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Every actual parameter jet is continuous in all real angles on the physical
upper side. This assertion concerns the literal density, not a local model. -/
theorem edgeConstrainedJet_upper_continuous {n : ℕ} {b : ℝ} {B S : ℂ → ℂ} {u : ℂ}
    (hB : AnalyticAt ℂ B u) (hS : AnalyticAt ℂ S u)
    (hu : 0<u.im) (hBi : 0<(B u).im) (hS0 : S u≠0) (j : ℕ) :
    Continuous (fun q : Fin n → ℝ => edgeConstrainedJet b B S j (u,q)) := by
  apply continuous_iff_continuousAt.mpr
  intro q
  let F : ℂ × (Fin (n+1) → ℂ) → ℂ := fun p => complexDensity b B S p.1 p.2
  let G : (Fin n → ℝ) → ℂ × (Fin (n+1) → ℂ) :=
    fun q => (u,fun i => ((shapeExtend q i:ℝ):ℂ))
  have hG : Continuous G := by unfold G shapeExtend; fun_prop
  have hF : AnalyticAt ℂ F (G q) :=
    complexDensity_joint_analyticAt (by omega) hB hS hu hBi hS0 (shapeExtend q)
  have hj := (jointParameterJet_analyticAt hF j).continuousAt.comp
    (f:=G) (x:=q) hG.continuousAt
  simpa only [Function.comp_def,G,F,jointParameterJet_eq,←iteratedDeriv_eq_iterate,
    complexDensity_real,edgeConstrainedJet] using hj

/-- The exact local/complement integral decomposition holds on a common disk
before choosing a family member. All normalization and cutoff factors are kept. -/
theorem compact_family_full_decomposition {n : ℕ} {b : ℝ} (B S : ℂ × E → ℂ)
    (_hb : |b|<1) {Q : Set E} (hQ : IsCompact Q)
    (hB : ∀eta∈Q,AnalyticAt ℂ B (0,eta)) (hBi : ∀eta∈Q,0<(B (0,eta)).im)
    (hS : ∀eta∈Q,AnalyticAt ℂ S (0,eta)) (hS0 : ∀eta∈Q,S (0,eta)≠0)
    {R : ℝ} (hR : 0<R) (hRpi : R≤Real.pi) (j : ℕ) :
    ∃δ : ℝ,0<δ ∧ ∀eta∈Q,∀t : ℝ,0<t → t<δ →
      edgeFullDerivativeIntegral (n:=n) b (fun u=>B (u,eta)) (fun u=>S (u,eta)) j
        (Complex.I*(t:ℂ)^2)=
      (Real.sqrt (n+1))⁻¹ • edgeActualLocalDerivativeIntegral (n:=n) b
        (fun u=>B (u,eta)) (fun u=>S (u,eta)) j R t+
      edgeComplementDerivativeIntegral (n:=n) b (fun u=>B (u,eta)) (fun u=>S (u,eta)) j R
        (Complex.I*(t:ℂ)^2) := by
  obtain ⟨r,hr,hdata⟩ := compact_family_upper_data B S hQ hB hBi hS hS0
  refine ⟨Real.sqrt r,Real.sqrt_pos.mpr hr,?_⟩
  intro eta heta t ht htr
  have htsq : t^2<r := by nlinarith [Real.sq_sqrt hr.le]
  have hu : ‖Complex.I*(t:ℂ)^2‖<r := by simpa using htsq
  have hi : 0<(Complex.I*(t:ℂ)^2).im := by
    simp only [←Complex.ofReal_pow,Complex.mul_im,Complex.I_re,Complex.I_im,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,one_mul,zero_add]
    positivity
  obtain ⟨hBa,hSa,hBpos,hSn⟩ := hdata eta heta _ hu
  have hcont := edgeConstrainedJet_upper_continuous (n:=n) (b:=b)
    (hBa.comp (f:=fun u : ℂ => (u,eta)) (analyticAt_id.prod analyticAt_const))
    (hSa.comp (f:=fun u : ℂ => (u,eta)) (analyticAt_id.prod analyticAt_const)) hi hBpos hSn j
  have hw : Continuous (fun q : Fin n→ℝ => edgeShapeCutoff R (edgeFreeShape q)) :=
    (edgeShapeCutoff_properties (n:=n) hR).1.comp (edgeFreeShape_continuous n)
  have hi1 := (hw.mul hcont).continuousOn.integrableOn_compact (μ:=volume) (show IsCompact (edgeCenteredCube n) from isCompact_Icc)
  have hi2 := (((continuous_const (y:=(1:ℂ))).sub hw).mul hcont).continuousOn.integrableOn_compact
    (μ:=volume) (show IsCompact (edgeCenteredCube n) from isCompact_Icc)
  rw [←edge_local_derivative_integral_eq b (fun u=>B (u,eta)) (fun u=>S (u,eta)) hR hRpi t]
  unfold edgeFullDerivativeIntegral edgeComplementDerivativeIntegral
  have hsum := integral_add hi1 hi2
  dsimp only [Pi.mul_apply,Pi.sub_apply,Function.comp_def] at hsum
  unfold edgeCenteredCube at hsum ⊢
  rw [←hsum]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro q
  dsimp only
  ring

end
end IsingBulk.Joint.RegularEdges
