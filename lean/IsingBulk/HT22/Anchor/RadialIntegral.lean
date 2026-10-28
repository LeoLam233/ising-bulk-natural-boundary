import IsingBulk.HT22.Anchor.ZerothIdentity
import IsingBulk.HT22.Tail.SignedRadialIntegral
namespace IsingBulk.HT22.Anchor
noncomputable section
open Set Filter MeasureTheory IsingBulk.Preferred22
open scoped Topology ContDiff BigOperators
set_option backward.isDefEq.respectTransparency false

theorem ambient_divergence {n : ℕ}
    (d : PreferredBranchData) (B : PreferredCoareaBump d) (a : Fin (n+1)) (σ : ℂ) (hσ : ‖σ‖≤1) (c τ δ : ℝ)
    (rcut : ℝ → ℝ) (hr : ContDiff ℝ ∞ rcut) (s : ℂ) (j : ℕ)
    (hpts : ∀ x : Fin (n+1) → ℝ,(∀ i,x i∈Icc (-Real.pi-B.delta) B.delta) →
      PreferredFramePoint τ δ B.p B.m s x ∧ ∀ i,x i∈Ioo (-Real.pi-δ) δ) :
    Continuous (fun θ : Fin n → ℝ => preferredAngularDivergence (current a σ τ B.p B.m rcut j s)
      (preferredLiftedAngles B.delta (constrainedAtTotal c θ))) ∧
    (∫ θ : Fin n → ℝ in angularBox n,preferredAngularDivergence (current a σ τ B.p B.m rcut j s)
      (preferredLiftedAngles B.delta (constrainedAtTotal c θ)))=0 := by
  let F : (Fin (n+1) → ℝ) → Fin (n+1) → ℂ := current a σ τ B.p B.m rcut j s
  have hzero : ∀ x v,1/2<B.p (x v) → ∀ i,F x i=0 :=
    fun x v hv i => current_upper_zero d B a σ τ rcut j s x v hv i
  have htan' : ∀ x,(∀ i,x i∈Ioo (-Real.pi-B.delta) (Real.pi-B.delta)) → (∑ i,F x i)=0 :=
    fun x hx => current_tangent d B a σ τ δ rcut s j (fun x hx => (hpts x hx).1) x hx
  have hχ : ContDiff ℝ ∞ (constrainedAtTotal (n:=n) c) := Tail.constrainedAtTotal_contDiff c
  have hF (i : Fin n) : ContDiff ℝ ∞ (fun θ : Fin n → ℝ =>
      F (preferredLiftedAngles B.delta (constrainedAtTotal c θ)) i.castSucc) := by
    apply contDiff_iff_contDiffAt.mpr
    intro θ
    exact ((density_current_lift_contDiffAt (by omega) d B a σ hσ τ δ rcut hr s j hpts
      (constrainedAtTotal c θ)).2 i.castSucc).comp θ (contDiffAt_const.prodMk hχ.contDiffAt)
  have he : (fun θ : Fin n → ℝ => preferredAngularDivergence F
      (preferredLiftedAngles B.delta (constrainedAtTotal c θ)))=
      fun θ => ∑ i : Fin n,fderiv ℝ
        (fun x : Fin n → ℝ => F (preferredLiftedAngles B.delta (constrainedAtTotal c x)) i.castSucc)
        θ (Pi.single i 1) := by
    funext θ
    symm
    apply Tail.signed_lifted_intrinsic_divergence_point c d B F hzero htan' θ
    intro i
    have hc := (density_current_contDiffAt_period (by omega) d B a σ hσ τ δ rcut hr s j hpts
      (preferredLiftedAngles B.delta (constrainedAtTotal c θ))
      (preferredLiftedAngles_mem_oneSided B.delta (constrainedAtTotal c θ))).2 i
    exact (hc.comp _ (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  constructor
  · change Continuous (fun θ : Fin n → ℝ => preferredAngularDivergence F
      (preferredLiftedAngles B.delta (constrainedAtTotal c θ)))
    rw [he]
    apply continuous_finsetSum
    intro i _
    exact ((hF i).continuous_fderiv (by simp)).clm_apply continuous_const
  · change (∫ θ : Fin n → ℝ in angularBox n,preferredAngularDivergence F
      (preferredLiftedAngles B.delta (constrainedAtTotal c θ)))=0
    rw [he]
    exact Tail.signed_lifted_divergence_integral c B.delta F hF


theorem integral_radial_hasDerivAt {n : ℕ} (negative : Bool)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) (a : Fin (n+1)) {τ δ ε₀ : ℝ}
    (r : ℝ → ℝ) (hr : ContDiff ℝ ∞ r) (j : ℕ)
    (hpts : ∀ ε∈Ioo 0 ε₀,∀ x : Fin (n+1) → ℝ,(∀ i,x i∈Icc (-Real.pi-B.delta) B.delta) →
      PreferredFramePoint τ δ B.p B.m (IsingBulk.Branch.radialParameter d.alpha ε) x ∧
        ∀ i,x i∈Ioo (-Real.pi-δ) δ)
    {ε : ℝ} (hε : ε∈Ioo 0 ε₀) :
    HasDerivAt (fun u => transportedIntegral negative n a B.delta τ preferredPopulationCutoff B.p B.m r j
      (IsingBulk.Branch.radialParameter d.alpha u))
      (Complex.exp ((d.alpha:ℂ)*Complex.I)*transportedIntegral negative n a B.delta τ preferredPopulationCutoff B.p B.m r (j+1)
        (IsingBulk.Branch.radialParameter d.alpha ε)) ε := by
  let σ := Physical.constraintSign negative
  have hσ : ‖σ‖≤1 := by cases negative <;> simp [σ,Physical.constraintSign]
  let H := transportedDensity a σ τ preferredPopulationCutoff B.p B.m r j
  let G := transportedDensity a σ τ preferredPopulationCutoff B.p B.m r (j+1)
  let D := fun s x => preferredAngularDivergence (current a σ τ B.p B.m r j s) x
  let c := Physical.constraintAngle negative
  let s := IsingBulk.Branch.radialParameter d.alpha ε
  have hχ := Tail.constrainedAtTotal_contDiff (n:=n) c
  have hrad : ContDiff ℝ ∞ (IsingBulk.Branch.radialParameter d.alpha) := by
    have hc : ContDiff ℝ ∞ (fun x : ℝ => (x:ℂ)) := Complex.ofRealCLM.contDiff
    exact (hc.comp (contDiff_const.add contDiff_id)).mul contDiff_const
  have hmap : ContDiff ℝ ∞ (fun z : ℝ × (Fin n → ℝ) =>
      (IsingBulk.Branch.radialParameter d.alpha z.1,constrainedAtTotal c z.2)) :=
    (hrad.comp contDiff_fst).prodMk (hχ.comp contDiff_snd)
  have hF : ∀ u∈Ioo 0 ε₀,∀ q : Fin n → ℝ,ContDiffAt ℝ ∞
      (fun z : ℝ × (Fin n → ℝ) => H (IsingBulk.Branch.radialParameter d.alpha z.1)
        (preferredLiftedAngles B.delta (constrainedAtTotal c z.2))) (u,q) := by
    intro u hu q
    exact (density_current_lift_contDiffAt (by omega) d B a σ hσ τ δ r hr _ j (hpts u hu)
      (constrainedAtTotal c q)).1.comp (u,q) hmap.contDiffAt
  have hH : ∀ q : Fin n → ℝ,DifferentiableAt ℂ
      (fun t => H t (preferredLiftedAngles B.delta (constrainedAtTotal c q))) s := by
    intro q
    exact parameter_differentiable_period (by omega) d B a σ hσ τ δ r hr s j (hpts ε hε) _
      (preferredLiftedAngles_mem_oneSided B.delta _)
  have hD := ambient_divergence d B a σ hσ c τ δ r hr s j (hpts ε hε)
  have hG : Continuous (fun q : Fin n → ℝ => G s (preferredLiftedAngles B.delta (constrainedAtTotal c q))) := by
    apply continuous_iff_continuousAt.mpr
    intro q
    exact ((density_current_lift_contDiffAt (by omega) d B a σ hσ τ δ r hr s (j+1)
      (hpts ε hε) (constrainedAtTotal c q)).1.comp q (contDiffAt_const.prodMk hχ.contDiffAt)).continuousAt
  have hrec : ∀ q : Fin n → ℝ,
      deriv (fun t => H t (preferredLiftedAngles B.delta (constrainedAtTotal c q))) s=
        G s (preferredLiftedAngles B.delta (constrainedAtTotal c q))+
        D s (preferredLiftedAngles B.delta (constrainedAtTotal c q))-(0:ℂ) := by
    intro q
    change _=(_-_) + _ - 0
    exact (sub_add_cancel _ _).symm.trans (sub_zero _).symm
  have hh := Tail.signed_radial_integral_recurrence c B.delta d.alpha H G D (fun _ _ => 0) hε hF hH hrec
    (continuous_integrableOn_angularBox hG) (continuous_integrableOn_angularBox hD.1)
    (continuous_integrableOn_angularBox continuous_const) hD.2
  unfold Tail.signedLiftedRadialIntegral at hh
  simpa only [Tail.signedLiftedIntegral,transportedIntegral,H,G,c,σ,Physical.constrainedAngles,constrainedAtTotal,integral_zero,sub_zero] using hh

end
end IsingBulk.HT22.Anchor
