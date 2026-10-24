import IsingBulk.Anisotropic.RegularEdges.LeadingAway
import IsingBulk.Anisotropic.RegularEdges.AngularWrapping
import IsingBulk.First.MeanCoordinates

namespace IsingBulk.Anisotropic.RegularEdges
noncomputable section
open IsingBulk.First IsingBulk.Tail Set Filter Metric
open scoped Topology BigOperators

/-- Momentum conservation introduces no additional collisions in the centered free-angle cube. -/
theorem edgeRootProduct_constrained_eq_one_iff {n : ℕ} {b : ℝ} {B : ℂ→ℂ}
    (hb : |b|<1) (hBi : 0<(B 0).im) (q : Fin n→ℝ)
    (hq : ∀ i,q i∈Icc (-Real.pi) Real.pi) :
    edgeRootProduct b B 0 (shapeExtend q)=1 ↔
      q=0 ∧ continuedRoot (b:ℂ)^(n+1)=1 := by
  have he : edgeRootProduct b B 0 (fun i => wrapAngle (shapeExtend q i))=
      edgeRootProduct b B 0 (shapeExtend q) := by
    simp only [edgeRootProduct,edgeParamRoot_wrapAngle]
  constructor
  · intro h
    have hw := (edgeRootProduct_eq_one_iff hb hBi
      (fun i => wrapAngle (shapeExtend q i)) (fun i => wrapAngle_mem _)).mp (he.trans h)
    refine ⟨funext (fun i => ?_),hw.2⟩
    have hz : wrapAngle (q i)=0 := by simpa using hw.1 i.castSucc
    have hc : Real.cos (q i)=1 := by rw [←cos_wrapAngle,hz,Real.cos_zero]
    exact (Real.cos_eq_one_iff_of_lt_of_lt
      (by linarith [Real.pi_pos,(hq i).1]) (by linarith [Real.pi_pos,(hq i).2])).mp hc
  · rintro ⟨rfl,hres⟩
    have hz : shapeExtend (0:Fin n→ℝ)=0 := by
      ext i
      refine Fin.lastCases ?_ (fun k => ?_) i <;> simp
    rw [hz]
    simpa [edgeRootProduct,edgeParamRoot,edgeParamW] using hres

def edgeConstrainedJet {n : ℕ} (b : ℝ) (B S : ℂ→ℂ) (j : ℕ)
    (p : ℂ×(Fin n→ℝ)) : ℂ :=
  iteratedDeriv j (fun u => edgeAngularDensity b B S u (shapeExtend p.2)) p.1

theorem edgeConstrainedJet_eventually_continuousAt {n : ℕ} {b : ℝ} {B S : ℂ→ℂ}
    (hb : |b|<1) (hB : AnalyticAt ℂ B 0) (hBi : 0<(B 0).im)
    (hS : AnalyticAt ℂ S 0) (hS0 : S 0≠0) (q : Fin n→ℝ)
    (hne : edgeRootProduct b B 0 (shapeExtend q)≠1) (j : ℕ) :
    ∀ᶠ p : ℂ×(Fin n→ℝ) in 𝓝 (0,q),ContinuousAt (edgeConstrainedJet b B S j) p := by
  let G : ℂ×(Fin n→ℝ)→ℂ×(Fin (n+1)→ℝ) := fun p => (p.1,shapeExtend p.2)
  have hG : Continuous G := by unfold G shapeExtend; fun_prop
  filter_upwards [(hG.tendsto (0,q)).eventually
    (edgeAngularDensity_jet_eventually_continuousAt hb hB hBi hS hS0 (shapeExtend q) hne j)] with p hp
  exact hp.comp (f := G) (x := p) hG.continuousAt

/-- Uniform boundedness and actual joint continuity of all fixed derivatives on any compact
angular set avoiding lattice poles. The parameter neighborhood is fully complex, not just radial. -/
theorem edgeConstrainedJet_compact_bound {n : ℕ} {b : ℝ} {B S : ℂ→ℂ}
    (hb : |b|<1) (hB : AnalyticAt ℂ B 0) (hBi : 0<(B 0).im)
    (hS : AnalyticAt ℂ S 0) (hS0 : S 0≠0) {K : Set (Fin n→ℝ)} (hK : IsCompact K)
    (hne : ∀ q∈K,edgeRootProduct b B 0 (shapeExtend q)≠1) (j : ℕ) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ u in 𝓝 (0:ℂ),∀ q∈K,
      ContinuousAt (edgeConstrainedJet b B S j) (u,q) ∧ ‖edgeConstrainedJet b B S j (u,q)‖≤C := by
  have he (q) (hq : q∈K) := edgeConstrainedJet_eventually_continuousAt hb hB hBi hS hS0 q (hne q hq) j
  have hc (q) (hq : q∈K) : ContinuousAt (edgeConstrainedJet b B S j) (0,q) :=
    mem_of_mem_nhds (he q hq)
  have hcont : ContinuousOn (fun q => edgeConstrainedJet b B S j (0,q)) K := by
    intro q hq
    exact ((hc q hq).comp (f := fun q => ((0:ℂ),q)) (x := q)
      (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn hcont
  refine ⟨max C 0+1,by positivity,?_⟩
  apply hK.eventually_forall_of_forall_eventually
  intro q hq
  filter_upwards [he q hq,
    (hc q hq).norm.eventually_lt continuousAt_const
      (lt_of_le_of_lt (hC q hq) (lt_add_of_le_of_pos (le_max_left _ _) zero_lt_one))] with p hp hbnd
  exact ⟨hp,hbnd.le⟩

theorem edgeConstrainedJet_away_bound {n : ℕ} {b : ℝ} {B S : ℂ→ℂ}
    (hb : |b|<1) (hB : AnalyticAt ℂ B 0) (hBi : 0<(B 0).im)
    (hS : AnalyticAt ℂ S 0) (hS0 : S 0≠0) {U : Set (Fin n→ℝ)}
    (hU : IsOpen U) (h0 : 0∈U) (j : ℕ) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ u in 𝓝 (0:ℂ),∀ q : Fin n→ℝ,
      (∀ i,q i∈Icc (-Real.pi) Real.pi) → q∉U →
      ContinuousAt (edgeConstrainedJet b B S j) (u,q) ∧ ‖edgeConstrainedJet b B S j (u,q)‖≤C := by
  obtain ⟨C,hC,hev⟩ := edgeConstrainedJet_compact_bound hb hB hBi hS hS0
    ((isCompact_univ_pi (fun _ => isCompact_Icc)).diff hU)
    (fun q hq h => hq.2 (by
      rw [((edgeRootProduct_constrained_eq_one_iff hb hBi q (fun i => hq.1 i (mem_univ i))).mp h).1]
      exact h0)) j
  refine ⟨C,hC,?_⟩
  filter_upwards [hev] with u hu q hq hqU
  exact hu q ⟨fun i _ => hq i,hqU⟩

theorem edgeConstrainedJet_nonresonant_bound {n : ℕ} {b : ℝ} {B S : ℂ→ℂ}
    (hb : |b|<1) (hB : AnalyticAt ℂ B 0) (hBi : 0<(B 0).im)
    (hS : AnalyticAt ℂ S 0) (hS0 : S 0≠0) (hres : continuedRoot (b:ℂ)^(n+1)≠1) (j : ℕ) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ u in 𝓝 (0:ℂ),∀ q : Fin n→ℝ,
      (∀ i,q i∈Icc (-Real.pi) Real.pi) →
      ContinuousAt (edgeConstrainedJet b B S j) (u,q) ∧ ‖edgeConstrainedJet b B S j (u,q)‖≤C := by
  obtain ⟨C,hC,hev⟩ := edgeConstrainedJet_compact_bound hb hB hBi hS hS0
    (isCompact_univ_pi (fun _ : Fin n => isCompact_Icc))
    (fun q hq h => hres
      ((edgeRootProduct_constrained_eq_one_iff hb hBi q (fun i => hq i (mem_univ i))).mp h).2) j
  refine ⟨C,hC,?_⟩
  filter_upwards [hev] with u hu q hq
  exact hu q (fun i _ => hq i)

end
end IsingBulk.Anisotropic.RegularEdges
