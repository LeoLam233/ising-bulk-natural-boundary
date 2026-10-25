import IsingBulk.Joint.RegularEdges.FamilyLeadingScaling
import IsingBulk.Joint.RegularEdges.FamilyFiniteAnalytic

namespace IsingBulk.Joint.RegularEdges
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.Anisotropic.RegularEdges Set Filter
open scoped Topology BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Simultaneous time and anisotropy convergence of the literal full numerator jet. -/
theorem family_shapeAmplitude_filtered_limit {α : Type*} {l : Filter α}
    {τ : α → ℝ} (hτ : Tendsto τ l (𝓝[>] 0)) {eta : α → E} {eta₀ : E}
    (heta : Tendsto eta l (𝓝 eta₀)) {n : ℕ} {b : ℝ} {B S : ℂ × E → ℂ}
    (hb : |b|<1) (hB : AnalyticAt ℂ B (0,eta₀)) (hBi : 0<(B (0,eta₀)).im)
    (hS : AnalyticAt ℂ S (0,eta₀)) (hS0 : S (0,eta₀)≠0) (j : ℕ) (x : ShapeSpace n) :
    Tendsto (fun t : α => edgeShapeAmplitude b (fun u=>B (u,eta t))
      (fun u=>S (u,eta t)) j (τ t) (τ t • x)) l
      (𝓝 (edgeAnalyticJet (N:=n+1) b (fun u=>B (u,eta₀)) (fun u=>S (u,eta₀)) j (0,0))) := by
  have hz : Tendsto (fun t : α => (τ t:ℂ)) l (𝓝 0) := by
    simpa using! Complex.continuous_ofReal.continuousAt.tendsto.comp
      (hτ.mono_right nhdsWithin_le_nhds)
  have hu : Tendsto (fun t : α => Complex.I*(τ t:ℂ)^2) l (𝓝 0) := by
    simpa using! (hz.pow 2).const_mul Complex.I
  have hq : Tendsto (fun t : α => fun i : Fin (n+1) => ((τ t*x.1 i:ℝ):ℂ)) l (𝓝 0) := by
    apply tendsto_pi_nhds.mpr
    intro i
    simpa only [Complex.ofReal_mul,Pi.zero_apply,zero_mul] using hz.mul_const (x.1 i:ℂ)
  have hj := (familyEdgeJet_analyticAt_real hb hB hBi hS hS0
    (0:Fin (n+1)→ℝ) j).continuousAt.tendsto.comp (hu.prodMk_nhds (heta.prodMk_nhds hq))
  have hs : Tendsto (fun t : α => edgeSincFactor (fun i=>τ t*x.1 i)) l (𝓝 (1:ℂ)) := by
    have hh : Continuous (fun t : ℝ => edgeSincFactor (fun i=>t*x.1 i)) :=
      (edgeSincFactor_continuous (n+1)).comp (by fun_prop)
    simpa [edgeSincFactor] using! (hh.tendsto 0).comp (hτ.mono_right nhdsWithin_le_nhds)
  simpa [edgeShapeAmplitude,familyEdgeJet] using! hs.mul hj

omit [NormedSpace ℂ E] in
/-- The quadratic lattice denominator limit is joint in time and all complex
family parameters. The varying value of B is retained throughout the proof. -/
theorem family_shapeDenominator_filtered_limit {α : Type*} {l : Filter α}
    {τ : α → ℝ} (hτ : Tendsto τ l (𝓝[>] 0)) {eta : α → E} {eta₀ : E}
    (heta : Tendsto eta l (𝓝 eta₀)) {n : ℕ} {b : ℝ} {B : ℂ × E → ℂ}
    (hb : |b|<1) (hB : ContinuousAt B (0,eta₀))
    (hres : continuedRoot (b:ℂ)^(n+1)=1) (x : ShapeSpace n) :
    Tendsto (fun t : α => edgeShapeDenominator b (fun u=>B (u,eta t))
      (τ t) (τ t • x)/(τ t:ℂ)^2) l
      (𝓝 (((n+1:ℝ)/Real.sqrt (1-b^2):ℝ)+
        (-Complex.I*B (0,eta₀)/((2*Real.sqrt (1-b^2):ℝ):ℂ))*(‖x‖:ℂ)^2)) := by
  have hz : Tendsto (fun t : α => (τ t:ℂ)) l (𝓝 0) := by
    simpa using! Complex.continuous_ofReal.continuousAt.tendsto.comp
      (hτ.mono_right nhdsWithin_le_nhds)
  have hu : Tendsto (fun t : α => Complex.I*(τ t:ℂ)^2) l (𝓝 0) := by
    simpa using! (hz.pow 2).const_mul Complex.I
  have hV : Tendsto (fun t : α => B (Complex.I*(τ t:ℂ)^2,eta t)) l (𝓝 (B (0,eta₀))) :=
    hB.tendsto.comp (hu.prodMk_nhds heta)
  have hs : (∑ i,(x.1 i:ℂ)^2)=(‖x‖:ℂ)^2 := by
    simp_rw [←Complex.ofReal_pow]
    rw [←Complex.ofReal_sum]
    congr 1
    exact (EuclideanSpace.real_norm_sq_eq x.1).symm
  have h := filtered_root_product_denominator_limit hτ hV hb (fun i=>x.1 i) hres
  rw [hs] at h
  convert! h using 1
  · ext t
    simp [edgeShapeDenominator,edgeComplexDenominator,edgeComplexRoot,
      filteredEdgeIncrement,add_assoc]

  · congr 1
    push_cast
    ring

end
end IsingBulk.Joint.RegularEdges
