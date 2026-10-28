import IsingBulk.HT22.Tail.RegularPoint
import IsingBulk.HT22.Tail.PhysicalSupport
import IsingBulk.Preferred22.PuncturedDensitySmooth

/-! New physical density/current are genuinely smooth after the original
real full-equality puncture, including all partial collisions and lift seams. -/
namespace IsingBulk.HT22.Tail
noncomputable section
open IsingBulk.Preferred22 Set Filter
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false

/-- Literal punctured physical density; the original scalar normalization
is already inside the transported density. -/
def puncturedDensity {N : ℕ} (σ : ℂ) (d : PreferredBranchData) (B : PreferredCoareaBump d)
    (τ R : ℝ) (rcut : ℝ → ℝ) (j : ℕ) (s : ℂ) (θ : Fin N → ℝ) : ℂ :=
  (preferredEqualityCutoff R θ:ℂ)*
    transportedDensity σ τ preferredPopulationCutoff B.p B.m rcut j s θ

/-- Literal punctured current, with the unchanged physical angular field. -/
def puncturedCurrent {N : ℕ} (σ : ℂ) (d : PreferredBranchData) (B : PreferredCoareaBump d)
    (τ R : ℝ) (rcut : ℝ → ℝ) (j : ℕ) (s : ℂ) (θ : Fin N → ℝ) (i : Fin N) : ℂ :=
  (preferredEqualityCutoff R θ:ℂ)*
    (angularField τ B.p B.m s θ i*
      transportedDensity σ τ preferredPopulationCutoff B.p B.m rcut j s θ)

/-- Genuine full-torus punctured smoothness from the already proved actual
regular-domain membership. The statement controls every positive order. -/
theorem puncturedDensity_and_current_lift_contDiffAt {N : ℕ} (hN : 0<N)
    (σ : ℂ) (hσ : ‖σ‖≤1) (d : PreferredBranchData) (B : PreferredCoareaBump d) {δB τ : ℝ}
    (rcut : ℝ → ℝ) (hcut : PreferredRightCutoffData d B δB rcut)
    (s : ℂ) (R : ℝ) (j : ℕ)
    (hreg : ∀ x∈preferredRightAngularBox d B.delta δB N,0<preferredAngularDiameter x →
      RegularPoint τ B.p B.m s x) (θ : Fin N → ℝ) :
    ContDiffAt ℝ ∞ (fun z : ℂ × (Fin N → ℝ) =>
      puncturedDensity σ d B τ R rcut j z.1 (preferredLiftedAngles B.delta z.2)) (s,θ) ∧
    ∀ i,ContDiffAt ℝ ∞ (fun z : ℂ × (Fin N → ℝ) =>
      puncturedCurrent σ d B τ R rcut j z.1 (preferredLiftedAngles B.delta z.2) i) (s,θ) := by
  let P := fun z : ℂ × (Fin N → ℝ) =>
    transportedDensity σ τ preferredPopulationCutoff B.p B.m rcut j z.1 z.2
  have hpzero : ∀ t x,(∀ i,x i∈Ioc (-Real.pi-B.delta) (Real.pi-B.delta)) →
      x∉preferredRightAngularBox d B.delta δB N → P (t,x)=0 := by
    intro t x hx hn
    exact transportedDensity_right_support σ d B τ rcut hcut j t x hx hn
  have hP (x : Fin N → ℝ) (hx : x∈preferredRightAngularBox d B.delta δB N)
      (hd : 0<preferredAngularDiameter x) : ContDiffAt ℝ ∞ P (s,x) :=
    (transportedDensity_regularPoint hN σ hσ τ preferredPopulationCutoff B.p B.m rcut
      preferredPopulationCutoff_smooth B.smooth B.m_smooth hcut.2.2.1 j s x (hreg x hx hd)).1
  have hpu : ∀ t x i,1/2<B.p (x i) → P (t,x)=0 :=
    fun t x i hi => transportedDensity_zero_of_upper_particle σ d B τ rcut j t x i hi
  constructor
  · refine preferredLiftedFunction_contDiffAt d B
      (fun z => puncturedDensity σ d B τ R rcut j z.1 z.2) ?_ s θ ?_
    · intro t x i hi
      change (preferredEqualityCutoff R x:ℂ)*P (t,x)=0
      rw [hpu t x i hi,mul_zero]
    · intro hθ
      exact preferredPuncturedFunction_contDiffAt d B δB R P hpzero s _
        (fun i => ⟨(preferredLiftedAngles_mem_oneSided B.delta θ i).1,hθ i⟩) hP
  · intro i
    let F := fun z : ℂ × (Fin N → ℝ) => angularField τ B.p B.m z.1 z.2 i*P z
    refine preferredLiftedFunction_contDiffAt d B
      (fun z => puncturedCurrent σ d B τ R rcut j z.1 z.2 i) ?_ s θ ?_
    · intro t x a ha
      change (preferredEqualityCutoff R x:ℂ)*(angularField τ B.p B.m t x i*P (t,x))=0
      rw [hpu t x a ha,mul_zero,mul_zero]
    · intro hθ
      refine preferredPuncturedFunction_contDiffAt d B δB R F ?_ s _
        (fun a => ⟨(preferredLiftedAngles_mem_oneSided B.delta θ a).1,hθ a⟩) ?_
      · intro t x hx hn
        simp only [F,hpzero t x hx hn,mul_zero]
      · intro x hx hd
        exact (angularField_regularPoint τ B.p B.m B.smooth B.m_smooth s x (hreg x hx hd) i).mul (hP x hx hd)


end
end IsingBulk.HT22.Tail
