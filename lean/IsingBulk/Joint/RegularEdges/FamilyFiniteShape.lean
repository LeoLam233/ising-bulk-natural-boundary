import IsingBulk.Joint.RegularEdges.FamilyFiniteLocal

namespace IsingBulk.Joint.RegularEdges
noncomputable section
open Set Filter Metric MeasureTheory IsingBulk.First IsingBulk.Tail
open IsingBulk.Anisotropic.RegularEdges
open scoped Topology BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem complex_shape_coordinate_norm_le {n : ℕ} (x : ShapeSpace n) :
    ‖fun i => (x.1 i:ℂ)‖≤‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).2
  intro i
  rw [Complex.norm_real]
  exact PiLp.norm_apply_le x.1 i

/-- Common local continuity and bounds for the actual numerator of every
fixed derivative, with the original complex shape denominator. -/
theorem compact_family_shape_local_bounds {n : ℕ} {b : ℝ} (B S : ℂ × E → ℂ)
    (hb : |b|<1) {Q : Set E} (hQ : IsCompact Q)
    (hB : ∀eta∈Q,AnalyticAt ℂ B (0,eta)) (hBi : ∀eta∈Q,0<(B (0,eta)).im)
    (hS : ∀eta∈Q,AnalyticAt ℂ S (0,eta)) (hS0 : ∀eta∈Q,S (0,eta)≠0) (j : ℕ) :
    ∃R M : ℝ,0<R ∧ R≤Real.pi ∧ 0≤M ∧ ∀eta∈Q,∀t : ℝ,|t|<R →
      ContinuousOn (edgeShapeAmplitude (n:=n) b (fun u=>B (u,eta)) (fun u=>S (u,eta)) j t) (ball 0 R) ∧
      ContinuousOn (edgeShapeDenominator (n:=n) b (fun u=>B (u,eta)) t) (ball 0 R) ∧
      ∀x : ShapeSpace n,x∈ball 0 R →
        ‖edgeShapeAmplitude b (fun u=>B (u,eta)) (fun u=>S (u,eta)) j t x‖≤M := by
  obtain ⟨r,M,hr,hM,hfac⟩ := compact_family_local_factors (N:=n+1) B S hb hQ hB hBi hS hS0 j
  let R := min 1 (min r Real.pi)
  have hR : 0<R := lt_min zero_lt_one (lt_min hr Real.pi_pos)
  have hRr : R≤r := (min_le_right _ _).trans (min_le_left _ _)
  refine ⟨R,M,hR,(min_le_right _ _).trans (min_le_right _ _),hM.le,?_⟩
  intro eta heta t ht
  have ht1 : |t|<1 := ht.trans_le (min_le_left _ _)
  have htr : |t|<r := ht.trans_le hRr
  have hu : ‖Complex.I*(t:ℂ)^2‖<r := by
    simp only [norm_mul,Complex.norm_I,one_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs]
    nlinarith [abs_nonneg t]
  have hfacx (x : ShapeSpace n) (hx : x∈ball 0 R) :=
    hfac eta heta (Complex.I*(t:ℂ)^2) (fun i=>(x.1 i:ℂ)) hu
      ((complex_shape_coordinate_norm_le x).trans_lt ((show ‖x‖<R by simpa using hx).trans_le hRr))
  have hc (x : ShapeSpace n) : ContinuousAt
      (fun x : ShapeSpace n => (Complex.I*(t:ℂ)^2,(eta,fun i=>(x.1 i:ℂ)))) x := by fun_prop
  refine ⟨?_,?_,?_⟩
  · intro x hx
    have hJ : AnalyticAt ℂ (familyEdgeJet b B S j)
        (Complex.I*(t:ℂ)^2,(eta,fun i=>(x.1 i:ℂ))) :=
      quotientJetNumerator_joint_analyticAt (hfacx x hx).1 (hfacx x hx).2.1 j
    exact (((edgeSincFactor_continuous (n+1)).continuousAt.comp
      (f:=fun x : ShapeSpace n => fun i=>x.1 i) (x:=x) (by fun_prop)).mul
        (hJ.continuousAt.comp (f:=fun x : ShapeSpace n =>
          (Complex.I*(t:ℂ)^2,(eta,fun i=>(x.1 i:ℂ)))) (x:=x) (hc x))).continuousWithinAt
  · intro x hx
    exact ((hfacx x hx).2.1.continuousAt.comp (f:=fun x : ShapeSpace n =>
      (Complex.I*(t:ℂ)^2,(eta,fun i=>(x.1 i:ℂ)))) (x:=x) (hc x)).continuousWithinAt
  · intro x hx
    rw [edgeShapeAmplitude,norm_mul]
    exact (mul_le_mul (edgeSincFactor_norm_le_one _) (hfacx x hx).2.2 (norm_nonneg _) zero_le_one).trans_eq (one_mul M)

/-- Common exact comparison between literal derivatives and the rational local
jet integral. No pointwise choice of a parameter-dependent radius is used. -/
theorem compact_family_actualLocal_eq {n : ℕ} {b : ℝ} (B S : ℂ × E → ℂ)
    (hb : |b|<1) {Q : Set E} (hQ : IsCompact Q)
    (hB : ∀eta∈Q,AnalyticAt ℂ B (0,eta)) (hBi : ∀eta∈Q,0<(B (0,eta)).im)
    (hS : ∀eta∈Q,AnalyticAt ℂ S (0,eta)) (hS0 : ∀eta∈Q,S (0,eta)≠0) :
    ∃r δ : ℝ,0<r ∧ 0<δ ∧ r≤Real.pi ∧ ∀eta∈Q,∀R : ℝ,0<R → R≤r →
      ∀j : ℕ,∀t : ℝ,0<t → t<δ →
      edgeActualLocalDerivativeIntegral (n:=n) b (fun u=>B (u,eta)) (fun u=>S (u,eta)) j R t=
        edgeLocalJetIntegral (n:=n) b (fun u=>B (u,eta)) (fun u=>S (u,eta)) j R t := by
  obtain ⟨r,hr,hid⟩ := compact_family_shape_derivative_neighborhood (n:=n) B S hb hQ hB hBi hS hS0
  obtain ⟨c,δ,hc,hδ,hgap⟩ := compact_family_shapeDenominator_gap (n:=n) B hb hQ hB hBi
  refine ⟨min r Real.pi,min r δ,lt_min hr Real.pi_pos,lt_min hr hδ,min_le_right _ _,?_⟩
  intro eta heta R hR hRr j t ht htδ
  have htr : |t|<r := by rw [abs_of_pos ht]; exact htδ.trans_le (min_le_left _ _)
  unfold edgeActualLocalDerivativeIntegral edgeLocalJetIntegral
  apply integral_congr_ae
  apply Eventually.of_forall
  intro x
  dsimp only
  by_cases hx : edgeShapeCutoff R x=0
  · simp [hx]
  · have hxr := (edgeShapeCutoff_properties (n:=n) hR).2.2.2 x hx
    have hangle (i : Fin (n+1)) : x.1 i∈Icc (-Real.pi) Real.pi := by
      have hh := PiLp.norm_apply_le x.1 i
      rw [Real.norm_eq_abs] at hh
      have hl : |x.1 i|<Real.pi := hh.trans_lt (hxr.trans_le (hRr.trans (min_le_right _ _)))
      exact ⟨(abs_lt.mp hl).1.le,(abs_lt.mp hl).2.le⟩
    have hn : edgeShapeDenominator b (fun u=>B (u,eta)) t x≠0 := by
      intro he
      have hg := hgap eta heta t ht (htδ.trans_le (min_le_right _ _)) x hangle
      rw [he,norm_zero] at hg
      have hp : 0<c*(t^2+‖x‖^2) := by positivity
      linarith
    rw [hid eta heta t htr x (hxr.trans_le (hRr.trans (min_le_left _ _))) hn j]
    ring

end
end IsingBulk.Joint.RegularEdges
