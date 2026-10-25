import IsingBulk.Joint.RegularEdges.FamilyFiniteShape
import IsingBulk.Joint.RegularEdges.FamilyFiniteAway

namespace IsingBulk.Joint.RegularEdges
noncomputable section
open Set Filter Metric MeasureTheory IsingBulk.First IsingBulk.Tail
open IsingBulk.Anisotropic.RegularEdges
open scoped Topology BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
set_option maxHeartbeats 1600000

theorem compact_family_higher_pointwise_bound {n j : ℕ} (hn : 1≤n)
    (hdegree : 2*(j+1)≤(n+1)*n) {b : ℝ} (B S : ℂ × E → ℂ)
    (hb : |b|<1) {Q : Set E} (hQ : IsCompact Q)
    (hB : ∀eta∈Q,AnalyticAt ℂ B (0,eta)) (hBi : ∀eta∈Q,0<(B (0,eta)).im)
    (hS : ∀eta∈Q,AnalyticAt ℂ S (0,eta)) (hS0 : ∀eta∈Q,S (0,eta)≠0) :
    ∃ r δ C : ℝ,0<r ∧ 0<δ ∧ 0≤C ∧ ∀eta∈Q, ∀ t : ℝ,0<t → t<δ →
      ∀ x : ShapeSpace n,‖x‖<r →
        ‖iteratedDeriv j (fun u => edgeAngularDensity b (fun u=>B (u,eta)) (fun u=>S (u,eta)) u (fun i => x.1 i))
          (Complex.I*(t:ℂ)^2)‖≤C := by
  obtain ⟨R,M,hR,hRπ,hM,hlocal⟩ := compact_family_shape_local_bounds (n := n) B S hb hQ hB hBi hS hS0 j
  obtain ⟨r,hr,hid⟩ := compact_family_shape_derivative_neighborhood (n := n) B S hb hQ hB hBi hS hS0
  obtain ⟨c,δ,hc,hδ,hgap⟩ := compact_family_shapeDenominator_gap (n := n) B hb hQ hB hBi
  let L := min 1 (min R r)
  have hL : 0<L := lt_min zero_lt_one (lt_min hR hr)
  have hLR : L≤R := (min_le_right _ _).trans (min_le_left _ _)
  have hLr : L≤r := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨L,min L δ,2^((n+1)*n)*M/c^(j+1),hL,lt_min hL hδ,by positivity,?_⟩
  intro eta heta t ht htδ x hx
  have htL : t<L := htδ.trans_le (min_le_left _ _)
  have htr : |t|<r := by rw [abs_of_pos ht]; exact htL.trans_le hLr
  have htR : |t|<R := by rw [abs_of_pos ht]; exact htL.trans_le hLR
  have hangle (i : Fin (n+1)) : x.1 i∈Icc (-Real.pi) Real.pi := by
    have hh := PiLp.norm_apply_le x.1 i
    rw [Real.norm_eq_abs] at hh
    have hp : |x.1 i|<Real.pi := hh.trans_lt (hx.trans_le (hLR.trans hRπ))
    exact ⟨(abs_lt.mp hp).1.le,(abs_lt.mp hp).2.le⟩
  have hg := hgap eta heta t ht (htδ.trans_le (min_le_right _ _)) x hangle
  have hne : edgeShapeDenominator b (fun u=>B (u,eta)) t x≠0 := by
    intro he
    rw [he,norm_zero] at hg
    have hp : 0<c*(t^2+‖x‖^2) := by positivity
    linarith
  rw [hid eta heta t htr x (hx.trans_le hLr) hne j]
  apply norm_high_shapeQuotient_le hn hdegree hM hc x
    (hx.le.trans (min_le_left _ _)) _ _
    ((hlocal eta heta t htR).2.2 x (by simpa using hx.trans_le hLR))
  nlinarith [mul_nonneg hc.le (sq_nonneg t)]


/-- Higher finite particle jets are uniformly bounded on the entire angular
cube. Both the collision core and its complement use common family constants. -/
theorem compact_family_higher_integral_bound {n j : ℕ} (hn : 1≤n)
    (hdegree : 2*(j+1)≤(n+1)*n) {b : ℝ} (B S : ℂ × E → ℂ)
    (hb : |b|<1) {Q : Set E} (hQ : IsCompact Q)
    (hB : ∀eta∈Q,AnalyticAt ℂ B (0,eta)) (hBi : ∀eta∈Q,0<(B (0,eta)).im)
    (hS : ∀eta∈Q,AnalyticAt ℂ S (0,eta)) (hS0 : ∀eta∈Q,S (0,eta)≠0) :
    ∃δ C : ℝ,0<δ ∧ 0≤C ∧ ∀eta∈Q,∀t : ℝ,0<t → t<δ →
      ‖edgeFullDerivativeIntegral (n:=n) b (fun u=>B (u,eta)) (fun u=>S (u,eta)) j
        (Complex.I*(t:ℂ)^2)‖≤C := by
  obtain ⟨r,δ,M,hr,hδ,hM,hpoint⟩ := compact_family_higher_pointwise_bound hn hdegree B S hb hQ hB hBi hS hS0
  let U : Set (Fin n→ℝ) := {q | ‖edgeFreeShape q‖<r}
  have hU : IsOpen U := isOpen_lt (edgeFreeShape_continuous n).norm continuous_const
  have h0 : (0:Fin n→ℝ)∈U := by simp [U,hr]
  obtain ⟨a,C,ha,hC,haway⟩ := compact_family_constrained_jet_bound B S hb hQ hB hBi hS hS0
    (L:=edgeCenteredCube n \ U) (isCompact_Icc.diff hU) (by
      intro eta heta q hq he
      have hz := ((edgeRootProduct_constrained_eq_one_iff hb (hBi eta heta) q
        (fun i=>⟨hq.1.1 i,hq.1.2 i⟩)).mp he).1
      exact hq.2 (hz ▸ h0)) j
  refine ⟨min δ (Real.sqrt a),max M C*volume.real (edgeCenteredCube n),
    lt_min hδ (Real.sqrt_pos.mpr ha),by positivity,?_⟩
  intro eta heta t ht htδ
  have hta : t^2<a := by
    have hlt := htδ.trans_le (min_le_right _ _)
    nlinarith [Real.sq_sqrt ha.le]
  have hu : ‖Complex.I*(t:ℂ)^2‖<a := by simpa using hta
  apply norm_setIntegral_le_of_norm_le_const isCompact_Icc.measure_lt_top
  intro q hq
  by_cases hqU : q∈U
  · exact (hpoint eta heta t ht (htδ.trans_le (min_le_left _ _))
      (edgeFreeShape q) hqU).trans (le_max_left _ _)
  · exact (haway eta heta _ hu q ⟨hq,hqU⟩).trans (le_max_right _ _)

end
end IsingBulk.Joint.RegularEdges
