import IsingBulk.HT22.Tail.PuncturedGeometry
import IsingBulk.HT22.Tail.SignedStokes

/-! The actual new punctured current is smooth and tangent; its signed
constrained ambient divergence integrates exactly to zero. -/
namespace IsingBulk.HT22.Tail
noncomputable section
open IsingBulk.Preferred22 Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false

theorem puncturedCurrent_upper_zero {N : ℕ} (σ : ℂ) (d : PreferredBranchData)
    (B : PreferredCoareaBump d) (τ R : ℝ) (rcut : ℝ → ℝ) (j : ℕ)
    (s : ℂ) (θ : Fin N → ℝ) (a : Fin N) (ha : 1/2<B.p (θ a)) (i : Fin N) :
    puncturedCurrent σ d B τ R rcut j s θ i=0 := by
  simp only [puncturedCurrent,
    transportedDensity_zero_of_upper_particle σ d B τ rcut j s θ a ha,mul_zero]

/-- Actual ambient smoothness at every lifted point, including the upper
endpoint and all full/partial equality cases after the exact puncture. -/
theorem puncturedCurrent_contDiffAt {N : ℕ} (hN : 0<N)
    (σ : ℂ) (hσ : ‖σ‖≤1) (d : PreferredBranchData) (B : PreferredCoareaBump d) {δB τ : ℝ}
    (rcut : ℝ → ℝ) (hcut : PreferredRightCutoffData d B δB rcut)
    (s : ℂ) (R : ℝ) (j : ℕ)
    (hreg : ∀ x∈preferredRightAngularBox d B.delta δB N,0<preferredAngularDiameter x →
      RegularPoint τ B.p B.m s x)
    (θ : Fin N → ℝ) (hθ : ∀ i,θ i∈Ioc (-Real.pi-B.delta) (Real.pi-B.delta)) (i : Fin N) :
    ContDiffAt ℝ ∞ (fun z : ℂ × (Fin N → ℝ) => puncturedCurrent σ d B τ R rcut j z.1 z.2 i) (s,θ) := by
  apply preferredPeriodIntervalFunction_contDiffAt d B _
    (fun t x a ha => puncturedCurrent_upper_zero σ d B τ R rcut j t x a ha i) s θ hθ
  intro hθhi
  let P := fun z : ℂ × (Fin N → ℝ) =>
    transportedDensity σ τ preferredPopulationCutoff B.p B.m rcut j z.1 z.2
  let F := fun z : ℂ × (Fin N → ℝ) => angularField τ B.p B.m z.1 z.2 i*P z
  refine preferredPuncturedFunction_contDiffAt d B δB R F ?_ s θ
    (fun a => ⟨(hθ a).1,hθhi a⟩) ?_
  · intro t x hx hn
    have hp := transportedDensity_right_support σ d B τ rcut hcut j t x hx hn
    simp only [F,P,hp,mul_zero]
  · intro x hx hd
    have hp := (transportedDensity_regularPoint hN σ hσ τ preferredPopulationCutoff B.p B.m rcut
      preferredPopulationCutoff_smooth B.smooth B.m_smooth hcut.2.2.1 j s x (hreg x hx hd)).1
    exact (angularField_regularPoint τ B.p B.m B.smooth B.m_smooth s x (hreg x hx hd) i).mul hp

/-- Tangency is used only on the actual physical right source. Elsewhere
the current vanishes by the original cutoff or by the equality puncture. -/
theorem puncturedCurrent_tangent {N : ℕ} (σ : ℂ) (d : PreferredBranchData)
    (B : PreferredCoareaBump d) {δB τ : ℝ} (rcut : ℝ → ℝ)
    (hcut : PreferredRightCutoffData d B δB rcut) (s : ℂ) (R : ℝ) (j : ℕ)
    (htan : ∀ x∈preferredRightAngularBox d B.delta δB N,0<preferredAngularDiameter x →
      (∑ i,angularField τ B.p B.m s x i)=0)
    (θ : Fin N → ℝ) (hθ : ∀ i,θ i∈Ioo (-Real.pi-B.delta) (Real.pi-B.delta)) :
    (∑ i,puncturedCurrent σ d B τ R rcut j s θ i)=0 := by
  by_cases hd : 0<preferredAngularDiameter θ
  · by_cases hb : θ∈preferredRightAngularBox d B.delta δB N
    · simp only [puncturedCurrent,←Finset.mul_sum,←Finset.sum_mul,htan θ hb hd,mul_zero,zero_mul]
    · have hp := transportedDensity_right_support σ d B τ rcut hcut j s θ
        (fun i => ⟨(hθ i).1,(hθ i).2.le⟩) hb
      simp only [puncturedCurrent,hp,mul_zero,Finset.sum_const_zero]
  · have he := (preferredEqualityCutoff_zero_germ R θ
      (le_antisymm (le_of_not_gt hd) Metric.diam_nonneg)).self_of_nhds
    simp only [puncturedCurrent,he,Complex.ofReal_zero,zero_mul,Finset.sum_const_zero]

/-- Exact zero divergence integral of the literal physical punctured
current, including the one-sided lift and the eliminated last particle. -/
theorem punctured_ambient_divergence_integral {n : ℕ}
    (a : ℝ) (σ : ℂ) (hσ : ‖σ‖≤1) (d : PreferredBranchData) (B : PreferredCoareaBump d) {δB τ : ℝ}
    (rcut : ℝ → ℝ) (hcut : PreferredRightCutoffData d B δB rcut)
    (s : ℂ) (R : ℝ) (j : ℕ)
    (hreg : ∀ x∈preferredRightAngularBox d B.delta δB (n+1),0<preferredAngularDiameter x →
      RegularPoint τ B.p B.m s x)
    (htan : ∀ x∈preferredRightAngularBox d B.delta δB (n+1),0<preferredAngularDiameter x →
      (∑ i,angularField τ B.p B.m s x i)=0) :
    (∫ θ : Fin n → ℝ in angularBox n,preferredAngularDivergence
      (puncturedCurrent σ d B τ R rcut j s)
      (preferredLiftedAngles B.delta (constrainedAtTotal a θ)))=0 := by
  let F : (Fin (n+1) → ℝ) → Fin (n+1) → ℂ := puncturedCurrent σ d B τ R rcut j s
  have hzero : ∀ x a,1/2<B.p (x a) → ∀ i,F x i=0 :=
    fun x a ha i => puncturedCurrent_upper_zero σ d B τ R rcut j s x a ha i
  have htan' : ∀ x,(∀ i,x i∈Ioo (-Real.pi-B.delta) (Real.pi-B.delta)) → (∑ i,F x i)=0 :=
    fun x hx => puncturedCurrent_tangent σ d B rcut hcut s R j htan x hx
  have hχ := constrainedAtTotal_contDiff (n:=n) a
  have hF (i : Fin n) : ContDiff ℝ ∞ (fun θ : Fin n → ℝ =>
      F (preferredLiftedAngles B.delta (constrainedAtTotal a θ)) i.castSucc) := by
    apply contDiff_iff_contDiffAt.mpr
    intro θ
    have hh := (puncturedDensity_and_current_lift_contDiffAt (by omega) σ hσ d B rcut hcut
      s R j hreg (constrainedAtTotal a θ)).2 i.castSucc
    exact hh.comp θ (contDiffAt_const.prodMk hχ.contDiffAt)
  have hpoint (θ : Fin n → ℝ) : (∑ i : Fin n,fderiv ℝ
      (fun x : Fin n → ℝ => F (preferredLiftedAngles B.delta (constrainedAtTotal a x)) i.castSucc)
      θ (Pi.single i 1))=preferredAngularDivergence F
        (preferredLiftedAngles B.delta (constrainedAtTotal a θ)) := by
    apply signed_lifted_intrinsic_divergence_point a d B F hzero htan' θ
    intro i
    have hc := puncturedCurrent_contDiffAt (by omega) σ hσ d B rcut hcut s R j hreg
      (preferredLiftedAngles B.delta (constrainedAtTotal a θ))
      (preferredLiftedAngles_mem_oneSided B.delta (constrainedAtTotal a θ)) i
    exact (hc.comp _ (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  calc
    _ = ∫ θ in angularBox n,∑ i : Fin n,fderiv ℝ
        (fun x : Fin n → ℝ => F (preferredLiftedAngles B.delta (constrainedAtTotal a x)) i.castSucc)
        θ (Pi.single i 1) := integral_congr_ae (Filter.Eventually.of_forall (fun θ => (hpoint θ).symm))
    _ = 0 := signed_lifted_divergence_integral a B.delta F hF

end
end IsingBulk.HT22.Tail
