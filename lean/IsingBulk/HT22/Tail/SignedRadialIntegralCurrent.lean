import IsingBulk.HT22.Tail.PuncturedCurrentGeometry

/-! Actual signed lifted ambient divergence is continuous because it equals
intrinsic divergence of the genuine smooth tangent current. -/
namespace IsingBulk.HT22.Tail
noncomputable section
open IsingBulk.Preferred22 Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false

theorem punctured_ambient_divergence_continuous {n : ℕ}
    (a : ℝ) (σ : ℂ) (hσ : ‖σ‖≤1) (d : PreferredBranchData) (B : PreferredCoareaBump d) {δB τ : ℝ}
    (rcut : ℝ → ℝ) (hcut : PreferredRightCutoffData d B δB rcut)
    (s : ℂ) (R : ℝ) (j : ℕ)
    (hreg : ∀ x∈preferredRightAngularBox d B.delta δB (n+1),0<preferredAngularDiameter x →
      RegularPoint τ B.p B.m s x)
    (htan : ∀ x∈preferredRightAngularBox d B.delta δB (n+1),0<preferredAngularDiameter x →
      (∑ i,angularField τ B.p B.m s x i)=0) :
    Continuous (fun θ : Fin n → ℝ => preferredAngularDivergence
      (puncturedCurrent σ d B τ R rcut j s)
      (preferredLiftedAngles B.delta (constrainedAtTotal a θ))) := by
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
  have he : (fun θ : Fin n → ℝ => preferredAngularDivergence F
      (preferredLiftedAngles B.delta (constrainedAtTotal a θ)))=
      fun θ => ∑ i : Fin n,fderiv ℝ
        (fun x : Fin n → ℝ => F (preferredLiftedAngles B.delta (constrainedAtTotal a x)) i.castSucc)
        θ (Pi.single i 1) := funext (fun θ => (hpoint θ).symm)
  change Continuous (fun θ : Fin n → ℝ => preferredAngularDivergence F
    (preferredLiftedAngles B.delta (constrainedAtTotal a θ)))
  rw [he]
  apply continuous_finsetSum
  intro i _
  exact ((hF i).continuous_fderiv (by simp)).clm_apply continuous_const

end
end IsingBulk.HT22.Tail
