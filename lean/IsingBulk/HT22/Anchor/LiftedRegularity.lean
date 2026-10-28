import IsingBulk.HT22.Anchor.IntegralBound
import IsingBulk.Preferred22.AnchorGeometry
namespace IsingBulk.HT22.Anchor
noncomputable section
open Set Filter IsingBulk.Preferred22
open scoped Topology ContDiff BigOperators
set_option backward.isDefEq.respectTransparency false

def current {N : ℕ} (a : Fin N) (σ : ℂ) (τ : ℝ) (p m r : ℝ → ℝ)
    (j : ℕ) (s : ℂ) (θ : Fin N → ℝ) (i : Fin N) : ℂ :=
  angularField a τ p m s θ i*transportedDensity a σ τ preferredPopulationCutoff p m r j s θ

theorem current_upper_zero {N : ℕ} (d : PreferredBranchData) (B : PreferredCoareaBump d)
    (a : Fin N) (σ : ℂ) (τ : ℝ) (r : ℝ → ℝ) (j : ℕ) (s : ℂ) (θ : Fin N → ℝ)
    (v : Fin N) (hv : 1/2<B.p (θ v)) (i : Fin N) : current a σ τ B.p B.m r j s θ i=0 := by
  unfold current
  rw [transportedDensity_zero_of_upper_particle a σ d B τ r j s θ v hv,mul_zero]

theorem transportedDensity_mixed {N : ℕ} (hN : 0<N) (a : Fin N) (σ : ℂ) (hσ : ‖σ‖≤1)
    (τ δ : ℝ) (η p m r : ℝ → ℝ)
    (hη : ContDiff ℝ ∞ η) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m) (hr : ContDiff ℝ ∞ r)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hpoint : ∀ z∈Ω,PreferredFramePoint τ δ p m z.1 z.2) (j : ℕ) :
    PreferredMixedSmoothOn (fun z => transportedDensity a σ τ η p m r j z.1 z.2) Ω := by
  have hh := (Tail.coordinateJacobian_mixed τ δ p m hp hm Ω hpoint).mul
    (regularTransportedScalar_mixed hN a σ hσ τ δ η p m r hη hp hm hr Ω hΩ hpoint j)
  apply hh.congr hΩ
  intro z hz
  exact (transportedDensity_eq_reconstructed hN a σ hσ τ δ η p m r hη hp hm hr Ω hΩ hpoint j z.1 z.2 hz).symm

theorem density_current_contDiffAt_core {N : ℕ} (hN : 0<N) (d : PreferredBranchData)
    (B : PreferredCoareaBump d) (a : Fin N) (σ : ℂ) (hσ : ‖σ‖≤1) (τ δ : ℝ)
    (r : ℝ → ℝ) (hr : ContDiff ℝ ∞ r) (s : ℂ) (θ : Fin N → ℝ) (j : ℕ)
    (hpoint : PreferredFramePoint τ δ B.p B.m s θ)
    (hstrict : ∀ i,θ i∈Ioo (-Real.pi-δ) δ) :
    ContDiffAt ℝ ∞ (fun z : ℂ × (Fin N → ℝ) =>
      transportedDensity a σ τ preferredPopulationCutoff B.p B.m r j z.1 z.2) (s,θ) ∧
    ∀ i,ContDiffAt ℝ ∞ (fun z : ℂ × (Fin N → ℝ) => current a σ τ B.p B.m r j z.1 z.2 i) (s,θ) := by
  obtain ⟨Ω,hΩ,hz,hpts,_hstrict⟩ := preferred_strict_frame_chart τ δ B.p B.m B.smooth B.m_smooth s θ hpoint hstrict
  have hd := transportedDensity_mixed hN a σ hσ τ δ preferredPopulationCutoff B.p B.m r
    preferredPopulationCutoff_smooth B.smooth B.m_smooth hr Ω hΩ hpts j
  have hv := (source_generator_mixed a τ δ B.p B.m B.smooth B.m_smooth Ω hΩ hpts).1
  exact ⟨(hd (s,θ) hz).1,fun i => ((hv i (s,θ) hz).1).mul (hd (s,θ) hz).1⟩

/-- Full-period anchor regularity, including total equality and the seam.
Only primitive actual frame points are needed on the lower support. -/
theorem density_current_lift_contDiffAt {N : ℕ} (hN : 0<N) (d : PreferredBranchData)
    (B : PreferredCoareaBump d) (a : Fin N) (σ : ℂ) (hσ : ‖σ‖≤1) (τ δ : ℝ)
    (r : ℝ → ℝ) (hr : ContDiff ℝ ∞ r) (s : ℂ) (j : ℕ)
    (hpts : ∀ x : Fin N → ℝ,(∀ i,x i∈Icc (-Real.pi-B.delta) B.delta) →
      PreferredFramePoint τ δ B.p B.m s x ∧ ∀ i,x i∈Ioo (-Real.pi-δ) δ)
    (θ : Fin N → ℝ) :
    ContDiffAt ℝ ∞ (fun z : ℂ × (Fin N → ℝ) =>
      transportedDensity a σ τ preferredPopulationCutoff B.p B.m r j z.1
        (preferredLiftedAngles B.delta z.2)) (s,θ) ∧
    ∀ i,ContDiffAt ℝ ∞ (fun z : ℂ × (Fin N → ℝ) =>
      current a σ τ B.p B.m r j z.1 (preferredLiftedAngles B.delta z.2) i) (s,θ) := by
  let w := preferredLiftedAngles B.delta θ
  have hw := preferredLiftedAngles_mem_oneSided B.delta θ
  have hD : ContDiffAt ℝ ∞ (fun z : ℂ × (Fin N → ℝ) =>
      transportedDensity a σ τ preferredPopulationCutoff B.p B.m r j z.1 z.2) (s,w) :=
    preferredLowerSupportedFunction_contDiffAt d B _
      (fun t x i hi => transportedDensity_zero_of_upper_particle a σ d B τ r j t x i hi)
      s w hw (fun hx => (density_current_contDiffAt_core hN d B a σ hσ τ δ r hr s w j (hpts w hx).1 (hpts w hx).2).1)
  have hC (i : Fin N) : ContDiffAt ℝ ∞ (fun z : ℂ × (Fin N → ℝ) => current a σ τ B.p B.m r j z.1 z.2 i) (s,w) :=
    preferredLowerSupportedFunction_contDiffAt d B _
      (fun t x v hv => current_upper_zero d B a σ τ r j t x v hv i)
      s w hw (fun hx => (density_current_contDiffAt_core hN d B a σ hσ τ δ r hr s w j (hpts w hx).1 (hpts w hx).2).2 i)
  exact ⟨preferredLiftedFunction_contDiffAt d B _
    (fun t x i hi => transportedDensity_zero_of_upper_particle a σ d B τ r j t x i hi) s θ (fun _ => hD),
    fun i => preferredLiftedFunction_contDiffAt d B _
      (fun t x v hv => current_upper_zero d B a σ τ r j t x v hv i) s θ (fun _ => hC i)⟩
theorem current_tangent {N : ℕ} (d : PreferredBranchData) (B : PreferredCoareaBump d)
    (a : Fin N) (σ : ℂ) (τ δ : ℝ) (r : ℝ → ℝ) (s : ℂ) (j : ℕ)
    (hpts : ∀ x : Fin N → ℝ,(∀ i,x i∈Icc (-Real.pi-B.delta) B.delta) →
      PreferredFramePoint τ δ B.p B.m s x)
    (θ : Fin N → ℝ) (hθ : ∀ i,θ i∈Ioo (-Real.pi-B.delta) (Real.pi-B.delta)) :
    (∑ i,current a σ τ B.p B.m r j s θ i)=0 := by
  classical
  by_cases hu : ∀ i,θ i≤B.delta
  · have h := hpts θ (fun i => ⟨(hθ i).1.le,hu i⟩)
    have ht := angularField_tangent a τ B.p B.m s θ h.matrix (Tail.source_inverseV_ne_zero h a)
    simp only [current,←Finset.sum_mul,ht,zero_mul]
  · obtain ⟨v,hv⟩ := not_forall.mp hu
    have hp : 1/2<B.p (θ v) := by
      rw [B.plateau (θ v) ⟨(lt_of_not_ge hv).le,(hθ v).2.le⟩]
      norm_num
    exact Finset.sum_eq_zero (fun i _ => current_upper_zero d B a σ τ r j s θ v hp i)

/-- The lifted anchor density/current are genuinely smooth for all orders
on one actual epsilon/tau regime. No excluded collision locus exists. -/
theorem actual_lifted_density_current_smooth (d : PreferredBranchData) (B : PreferredCoareaBump d) :
    ∃ ε₀ τ₀ : ℝ,0<ε₀ ∧ 0<τ₀ ∧
      ∀ N : ℕ,0<N → ∀ a : Fin N,∀ σ : ℂ,‖σ‖≤1 →
      ∀ ε τ : ℝ,0<ε → ε<ε₀ → 0≤τ → τ<τ₀ →
      ∀ r : ℝ → ℝ,ContDiff ℝ ∞ r → ∀ j : ℕ,∀ θ : Fin N → ℝ,
      let s := IsingBulk.Branch.radialParameter d.alpha ε
      ContDiffAt ℝ ∞ (fun z : ℂ × (Fin N → ℝ) =>
        transportedDensity a σ τ preferredPopulationCutoff B.p B.m r j z.1
          (preferredLiftedAngles B.delta z.2)) (s,θ) ∧
      (∀ i,ContDiffAt ℝ ∞ (fun z : ℂ × (Fin N → ℝ) =>
        current a σ τ B.p B.m r j z.1 (preferredLiftedAngles B.delta z.2) i) (s,θ)) ∧
      ((∀ i,θ i∈Ioo (-Real.pi-B.delta) (Real.pi-B.delta)) →
        (∑ i,current a σ τ B.p B.m r j s θ i)=0) := by
  obtain ⟨δ,ε₀,τ₀,_hδ,_hδa,hε₀,hτ₀,hframe⟩ := preferred_actual_whole_frame_points d B
  refine ⟨ε₀,τ₀,hε₀,hτ₀,?_⟩
  intro N hN a σ hσ ε τ hε hεr hτ hτr r hr j θ
  have hpts := hframe N hN ε τ hε hεr hτ hτr
  have hh := density_current_lift_contDiffAt hN d B a σ hσ τ δ r hr
    (IsingBulk.Branch.radialParameter d.alpha ε) j hpts θ
  exact ⟨hh.1,hh.2,fun ht => current_tangent d B a σ τ δ r _ j (fun x hx => (hpts x hx).1) θ ht⟩

theorem density_current_contDiffAt_period {N : ℕ} (hN : 0<N) (d : PreferredBranchData)
    (B : PreferredCoareaBump d) (a : Fin N) (σ : ℂ) (hσ : ‖σ‖≤1) (τ δ : ℝ)
    (r : ℝ → ℝ) (hr : ContDiff ℝ ∞ r) (s : ℂ) (j : ℕ)
    (hpts : ∀ x : Fin N → ℝ,(∀ i,x i∈Icc (-Real.pi-B.delta) B.delta) →
      PreferredFramePoint τ δ B.p B.m s x ∧ ∀ i,x i∈Ioo (-Real.pi-δ) δ)
    (θ : Fin N → ℝ) (hθ : ∀ i,θ i∈Ioc (-Real.pi-B.delta) (Real.pi-B.delta)) :
    ContDiffAt ℝ ∞ (fun z : ℂ × (Fin N → ℝ) =>
      transportedDensity a σ τ preferredPopulationCutoff B.p B.m r j z.1 z.2) (s,θ) ∧
    ∀ i,ContDiffAt ℝ ∞ (fun z : ℂ × (Fin N → ℝ) => current a σ τ B.p B.m r j z.1 z.2 i) (s,θ) := by
  constructor
  · exact preferredLowerSupportedFunction_contDiffAt d B _
      (fun t x i hi => transportedDensity_zero_of_upper_particle a σ d B τ r j t x i hi)
      s θ hθ (fun hx => (density_current_contDiffAt_core hN d B a σ hσ τ δ r hr s θ j (hpts θ hx).1 (hpts θ hx).2).1)
  · intro i
    exact preferredLowerSupportedFunction_contDiffAt d B _
      (fun t x v hv => current_upper_zero d B a σ τ r j t x v hv i)
      s θ hθ (fun hx => (density_current_contDiffAt_core hN d B a σ hσ τ δ r hr s θ j (hpts θ hx).1 (hpts θ hx).2).2 i)

theorem parameter_differentiable_period {N : ℕ} (hN : 0<N) (d : PreferredBranchData)
    (B : PreferredCoareaBump d) (a : Fin N) (σ : ℂ) (hσ : ‖σ‖≤1) (τ δ : ℝ)
    (r : ℝ → ℝ) (hr : ContDiff ℝ ∞ r) (s : ℂ) (j : ℕ)
    (hpts : ∀ x : Fin N → ℝ,(∀ i,x i∈Icc (-Real.pi-B.delta) B.delta) →
      PreferredFramePoint τ δ B.p B.m s x ∧ ∀ i,x i∈Ioo (-Real.pi-δ) δ)
    (θ : Fin N → ℝ) (hθ : ∀ i,θ i∈Ioc (-Real.pi-B.delta) (Real.pi-B.delta)) :
    DifferentiableAt ℂ (fun t => transportedDensity a σ τ preferredPopulationCutoff B.p B.m r j t θ) s := by
  classical
  by_cases hu : ∀ i,θ i≤B.delta
  · have h := hpts θ (fun i => ⟨(hθ i).1.le,hu i⟩)
    obtain ⟨Ω,hΩ,hz,hΩpoint,_hΩstrict⟩ := preferred_strict_frame_chart τ δ B.p B.m B.smooth B.m_smooth s θ h.1 h.2
    exact (transportedDensity_mixed hN a σ hσ τ δ preferredPopulationCutoff B.p B.m r
      preferredPopulationCutoff_smooth B.smooth B.m_smooth hr Ω hΩ hΩpoint j (s,θ) hz).2
  · obtain ⟨i,hi⟩ := not_forall.mp hu
    have hp : 1/2<B.p (θ i) := by
      rw [B.plateau (θ i) ⟨(lt_of_not_ge hi).le,(hθ i).2⟩]
      norm_num
    have he : (fun t => transportedDensity a σ τ preferredPopulationCutoff B.p B.m r j t θ)=fun _ => 0 :=
      funext (fun t => transportedDensity_zero_of_upper_particle a σ d B τ r j t θ i hp)
    rw [he]
    exact differentiableAt_const _

end
end IsingBulk.HT22.Anchor
