import IsingBulk.Preferred22.PuncturedDensitySmooth
import IsingBulk.Preferred22.LiftedStokes
import IsingBulk.Preferred22.ActualTangency

/-! The genuine punctured physical current is tangent, smooth, and has
exactly zero ambient divergence integral on the complete constrained torus. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false

theorem preferredPuncturedCurrent_upper_zero {N : ℕ} (d : PreferredBranchData)
    (B : PreferredCoareaBump d) (τ R : ℝ) (rcut : ℝ → ℝ) (j : ℕ)
    (s : ℂ) (θ : Fin N → ℝ) (a : Fin N) (ha : 1/2<B.p (θ a)) (i : Fin N) :
    preferredPuncturedCurrent d B τ R rcut j s θ i=0 := by
  simp only [preferredPuncturedCurrent,
    preferredTransportedDensity_zero_of_upper_particle d B τ rcut j s θ a ha,mul_zero]

/-- Actual ambient smoothness at every lifted point, including the upper
endpoint and all full/partial equality cases after the exact puncture. -/
theorem preferredPuncturedCurrent_contDiffAt {N : ℕ} (hN : 0<N)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {δB τ : ℝ}
    (rcut : ℝ → ℝ) (hcut : PreferredRightCutoffData d B δB rcut)
    (s : ℂ) (R : ℝ) (j : ℕ)
    (hreg : ∀ x∈preferredRightAngularBox d B.delta δB N,0<preferredAngularDiameter x →
      (s,x)∈preferredPhysicalRegularDomain τ B.p B.m)
    (θ : Fin N → ℝ) (hθ : ∀ i,θ i∈Ioc (-Real.pi-B.delta) (Real.pi-B.delta)) (i : Fin N) :
    ContDiffAt ℝ ∞ (fun z : ℂ × (Fin N → ℝ) => preferredPuncturedCurrent d B τ R rcut j z.1 z.2 i) (s,θ) := by
  apply preferredPeriodIntervalFunction_contDiffAt d B _
    (fun t x a ha => preferredPuncturedCurrent_upper_zero d B τ R rcut j t x a ha i) s θ hθ
  intro hθhi
  let P := fun z : ℂ × (Fin N → ℝ) =>
    preferredTransportedDensity .right τ preferredPopulationCutoff B.p B.m rcut j z.1 z.2
  let F := fun z : ℂ × (Fin N → ℝ) => preferredSourceAngularField .right τ B.p B.m z.1 z.2 i*P z
  refine preferredPuncturedFunction_contDiffAt d B δB R F ?_ s θ
    (fun a => ⟨(hθ a).1,hθhi a⟩) ?_
  · intro t x hx hn
    have hp := preferredTransportedDensity_right_support d B τ rcut hcut j t x hx hn
    simp only [F,P,hp,mul_zero]
  · intro x hx hd
    have hp := (preferredTransportedDensity_mixed_regularDomain hN τ preferredPopulationCutoff B.p B.m rcut
      preferredPopulationCutoff_smooth B.smooth B.m_smooth hcut.2.2.1 j (s,x) (hreg x hx hd)).1
    exact ((preferredSourceAngularField_mixed_regularDomain τ B.p B.m B.smooth B.m_smooth i
      (s,x) (hreg x hx hd)).1).mul hp

/-- Tangency is used only on the actual physical right source. Elsewhere
the current vanishes by the original cutoff or by the equality puncture. -/
theorem preferredPuncturedCurrent_tangent {N : ℕ} (d : PreferredBranchData)
    (B : PreferredCoareaBump d) {δB τ : ℝ} (rcut : ℝ → ℝ)
    (hcut : PreferredRightCutoffData d B δB rcut) (s : ℂ) (R : ℝ) (j : ℕ)
    (htan : ∀ x∈preferredRightAngularBox d B.delta δB N,0<preferredAngularDiameter x →
      (∑ i,preferredSourceAngularField .right τ B.p B.m s x i)=0)
    (θ : Fin N → ℝ) (hθ : ∀ i,θ i∈Ioo (-Real.pi-B.delta) (Real.pi-B.delta)) :
    (∑ i,preferredPuncturedCurrent d B τ R rcut j s θ i)=0 := by
  by_cases hd : 0<preferredAngularDiameter θ
  · by_cases hb : θ∈preferredRightAngularBox d B.delta δB N
    · simp only [preferredPuncturedCurrent,←Finset.mul_sum,←Finset.sum_mul,htan θ hb hd,mul_zero,zero_mul]
    · have hp := preferredTransportedDensity_right_support d B τ rcut hcut j s θ
        (fun i => ⟨(hθ i).1,(hθ i).2.le⟩) hb
      simp only [preferredPuncturedCurrent,hp,mul_zero,Finset.sum_const_zero]
  · have he := (preferredEqualityCutoff_zero_germ R θ
      (le_antisymm (le_of_not_gt hd) Metric.diam_nonneg)).self_of_nhds
    simp only [preferredPuncturedCurrent,he,Complex.ofReal_zero,zero_mul,Finset.sum_const_zero]

/-- Exact zero divergence integral of the literal physical punctured
current, including the one-sided lift and the eliminated last particle. -/
theorem preferred_punctured_ambient_divergence_integral {n : ℕ}
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {δB τ : ℝ}
    (rcut : ℝ → ℝ) (hcut : PreferredRightCutoffData d B δB rcut)
    (s : ℂ) (R : ℝ) (j : ℕ)
    (hreg : ∀ x∈preferredRightAngularBox d B.delta δB (n+1),0<preferredAngularDiameter x →
      (s,x)∈preferredPhysicalRegularDomain τ B.p B.m)
    (htan : ∀ x∈preferredRightAngularBox d B.delta δB (n+1),0<preferredAngularDiameter x →
      (∑ i,preferredSourceAngularField .right τ B.p B.m s x i)=0) :
    (∫ θ : Fin n → ℝ in angularBox n,preferredAngularDivergence
      (preferredPuncturedCurrent d B τ R rcut j s)
      (preferredLiftedAngles B.delta (constrainedAngles θ)))=0 := by
  let F : (Fin (n+1) → ℝ) → Fin (n+1) → ℂ := preferredPuncturedCurrent d B τ R rcut j s
  have hzero : ∀ x a,1/2<B.p (x a) → ∀ i,F x i=0 :=
    fun x a ha i => preferredPuncturedCurrent_upper_zero d B τ R rcut j s x a ha i
  have htan' : ∀ x,(∀ i,x i∈Ioo (-Real.pi-B.delta) (Real.pi-B.delta)) → (∑ i,F x i)=0 :=
    fun x hx => preferredPuncturedCurrent_tangent d B rcut hcut s R j htan x hx
  have hχ : ContDiff ℝ ∞ (@constrainedAngles n) := by
    have he : (constrainedAnglesCLM n : (Fin n → ℝ) → (Fin (n+1) → ℝ)) =
        constrainedAngles := funext (constrainedAnglesCLM_apply n)
    rw [←he]
    exact (constrainedAnglesCLM n).contDiff
  have hF (i : Fin n) : ContDiff ℝ ∞ (fun θ : Fin n → ℝ =>
      F (preferredLiftedAngles B.delta (constrainedAngles θ)) i.castSucc) := by
    apply contDiff_iff_contDiffAt.mpr
    intro θ
    have hh := (preferredPuncturedDensity_and_current_lift_contDiffAt (by omega) d B rcut hcut
      s R j hreg (constrainedAngles θ)).2 i.castSucc
    exact hh.comp θ (contDiffAt_const.prodMk hχ.contDiffAt)
  have hpoint (θ : Fin n → ℝ) : (∑ i : Fin n,fderiv ℝ
      (fun x : Fin n → ℝ => F (preferredLiftedAngles B.delta (constrainedAngles x)) i.castSucc)
      θ (Pi.single i 1))=preferredAngularDivergence F
        (preferredLiftedAngles B.delta (constrainedAngles θ)) := by
    apply preferred_lifted_intrinsic_divergence_point d B F hzero htan' θ
    intro i
    have hc := preferredPuncturedCurrent_contDiffAt (by omega) d B rcut hcut s R j hreg
      (preferredLiftedAngles B.delta (constrainedAngles θ))
      (preferredLiftedAngles_mem_oneSided B.delta (constrainedAngles θ)) i
    exact (hc.comp _ (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  calc
    _ = ∫ θ in angularBox n,∑ i : Fin n,fderiv ℝ
        (fun x : Fin n → ℝ => F (preferredLiftedAngles B.delta (constrainedAngles x)) i.castSucc)
        θ (Pi.single i 1) := integral_congr_ae (Filter.Eventually.of_forall (fun θ => (hpoint θ).symm))
    _ = 0 := preferred_lifted_divergence_integral B.delta F hF

end
end IsingBulk.Preferred22
