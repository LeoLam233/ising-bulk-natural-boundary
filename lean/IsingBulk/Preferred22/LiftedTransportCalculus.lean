import IsingBulk.Preferred22.TransportSupport
import IsingBulk.Preferred22.ContourLift
import IsingBulk.Preferred22.ContourFinalJets

/-! Local calculus of the literal one-sided angular lift. Its seam is
removed by the actual upper population plateau; no global analytic lift
or analytic real cutoff is introduced. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set Filter
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false

/-- Away from its seam, the literal modulo lift is a translation on a
neighborhood, with exactly the identity derivative. -/
theorem preferredLiftedAngles_eventually_affine {N : ℕ} (δ : ℝ) (θ : Fin N → ℝ)
    (hθ : ∀ i,preferredLiftedAngles δ θ i<Real.pi-δ) :
    ∀ᶠ x : Fin N → ℝ in 𝓝 θ,
      preferredLiftedAngles δ x=fun i => preferredLiftedAngles δ θ i+(x i-θ i) := by
  have hlocal (i : Fin N) : ∀ᶠ x : Fin N → ℝ in 𝓝 θ,
      preferredLiftedAngles δ x i=preferredLiftedAngles δ θ i+(x i-θ i) := by
    let c := preferredLiftedAngles δ θ i
    have hc : c∈Ioo (-Real.pi-δ) (Real.pi-δ) :=
      ⟨(preferredLiftedAngles_mem_oneSided δ θ i).1,hθ i⟩
    have hcont : ContinuousAt (fun x : Fin N → ℝ => c+(x i-θ i)) θ :=
      continuousAt_const.add ((continuous_apply i).continuousAt.sub continuousAt_const)
    have hmem : ∀ᶠ x : Fin N → ℝ in 𝓝 θ,c+(x i-θ i)∈Ioo (-Real.pi-δ) (Real.pi-δ) :=
      hcont.eventually (isOpen_Ioo.mem_nhds (by simpa using hc))
    obtain ⟨_,k,hk⟩ := (toIocMod_eq_iff (by positivity : 0<2*Real.pi)).mp
      (show toIocMod (by positivity : 0<2*Real.pi) (-Real.pi-δ) (θ i)=c from rfl)
    filter_upwards [hmem] with x hx
    apply (toIocMod_eq_iff (by positivity : 0<2*Real.pi)).mpr
    refine ⟨⟨hx.1,by linarith [hx.2]⟩,k,?_⟩
    dsimp only [c] at hk ⊢
    linarith
  filter_upwards [Filter.eventually_all.mpr hlocal] with x hx
  exact funext hx

/-- At any modular seam the genuine upper particle cutoff kills every
transported density on an open neighborhood of the original angles. -/
theorem preferredLiftedAngles_upper_zero_germ {N : ℕ} (d : PreferredBranchData)
    (B : PreferredCoareaBump d) (F : ℂ × (Fin N → ℝ) → ℂ)
    (hzero : ∀ s θ i,1/2<B.p (θ i) → F (s,θ)=0)
    (s : ℂ) (θ : Fin N → ℝ) (i : Fin N)
    (hseam : preferredLiftedAngles B.delta θ i=Real.pi-B.delta) :
    (fun z : ℂ × (Fin N → ℝ) => F (z.1,preferredLiftedAngles B.delta z.2))
      =ᶠ[𝓝 (s,θ)] fun _ => 0 := by
  have hpi : B.p (preferredLiftedAngles B.delta θ i)=1 := by
    rw [hseam]
    apply B.plateau
    constructor
    · linarith [B.delta_alpha,d.alpha_lt,Real.pi_pos]
    · exact le_rfl
  have hpr : B.p (θ i)=1 := by
    simpa only [preferredLiftedAngles,preferred_periodic_lift B.p B.periodic] using hpi
  have hc : ContinuousAt (fun z : ℂ × (Fin N → ℝ) => B.p (z.2 i)) (s,θ) := by
    have hp := B.smooth.continuous
    fun_prop
  have he := (continuousAt_const : ContinuousAt (fun _ : ℂ × (Fin N → ℝ) => (1/2:ℝ)) (s,θ)).eventually_lt hc
    (by rw [hpr]; norm_num)
  filter_upwards [he] with z hz
  apply hzero z.1 _ i
  simpa only [preferredLiftedAngles,preferred_periodic_lift B.p B.periodic] using hz

/-- Smoothness of a literal lifted function is obtained from ordinary
smoothness inside the period interval and the genuine plateau zero germ. -/
theorem preferredLiftedFunction_contDiffAt {N : ℕ} (d : PreferredBranchData)
    (B : PreferredCoareaBump d) (F : ℂ × (Fin N → ℝ) → ℂ)
    (hzero : ∀ s θ i,1/2<B.p (θ i) → F (s,θ)=0)
    (s : ℂ) (θ : Fin N → ℝ)
    (hF : (∀ i,preferredLiftedAngles B.delta θ i<Real.pi-B.delta) →
      ContDiffAt ℝ ∞ F (s,preferredLiftedAngles B.delta θ)) :
    ContDiffAt ℝ ∞ (fun z : ℂ × (Fin N → ℝ) =>
      F (z.1,preferredLiftedAngles B.delta z.2)) (s,θ) := by
  classical
  by_cases hi : ∀ i,preferredLiftedAngles B.delta θ i<Real.pi-B.delta
  · let T := fun z : ℂ × (Fin N → ℝ) =>
      (z.1,fun i => preferredLiftedAngles B.delta θ i+(z.2 i-θ i))
    have hT : ContDiff ℝ ∞ T := by unfold T; fun_prop
    have ht : T (s,θ)=(s,preferredLiftedAngles B.delta θ) := by ext i <;> simp [T]
    have hFt : ContDiffAt ℝ ∞ F (T (s,θ)) := by rw [ht]; exact hF hi
    have hcomp := hFt.comp (s,θ) (hT.contDiffAt)
    have he : (fun z : ℂ × (Fin N → ℝ) => F (z.1,preferredLiftedAngles B.delta z.2))
        =ᶠ[𝓝 (s,θ)] F ∘ T := by
      filter_upwards [continuousAt_snd.tendsto.eventually (preferredLiftedAngles_eventually_affine B.delta θ hi)] with z hz
      simp only [Function.comp_apply,T,hz]
    exact hcomp.congr_of_eventuallyEq he
  · obtain ⟨i,hi⟩ := not_forall.mp hi
    have hs : preferredLiftedAngles B.delta θ i=Real.pi-B.delta :=
      le_antisymm (preferredLiftedAngles_mem_oneSided B.delta θ i).2 (le_of_not_gt hi)
    exact contDiffAt_const.congr_of_eventuallyEq
      (preferredLiftedAngles_upper_zero_germ d B F hzero s θ i hs)

/-- Any upper particle exclusion produces a genuine joint zero germ. -/
theorem preferredUpperParticle_zero_germ {N : ℕ} (d : PreferredBranchData)
    (B : PreferredCoareaBump d) (F : ℂ × (Fin N → ℝ) → ℂ)
    (hzero : ∀ s θ i,1/2<B.p (θ i) → F (s,θ)=0)
    (s : ℂ) (θ : Fin N → ℝ) (i : Fin N) (hi : 1/2<B.p (θ i)) :
    F=ᶠ[𝓝 (s,θ)] fun _ => 0 := by
  have hc : ContinuousAt (fun z : ℂ × (Fin N → ℝ) => B.p (z.2 i)) (s,θ) := by
    have hp := B.smooth.continuous
    fun_prop
  have he := (continuousAt_const : ContinuousAt (fun _ : ℂ × (Fin N → ℝ) => (1/2:ℝ)) (s,θ)).eventually_lt hc hi
  filter_upwards [he] with z hz
  exact hzero z.1 z.2 i hz

/-- Inside the closed period interval, the upper endpoint also has a true
smooth germ, killed by the physical population plateau. -/
theorem preferredPeriodIntervalFunction_contDiffAt {N : ℕ} (d : PreferredBranchData)
    (B : PreferredCoareaBump d) (F : ℂ × (Fin N → ℝ) → ℂ)
    (hzero : ∀ s θ i,1/2<B.p (θ i) → F (s,θ)=0)
    (s : ℂ) (θ : Fin N → ℝ)
    (hθ : ∀ i,θ i∈Ioc (-Real.pi-B.delta) (Real.pi-B.delta))
    (hF : (∀ i,θ i<Real.pi-B.delta) → ContDiffAt ℝ ∞ F (s,θ)) :
    ContDiffAt ℝ ∞ F (s,θ) := by
  classical
  by_cases hi : ∀ i,θ i<Real.pi-B.delta
  · exact hF hi
  · obtain ⟨i,hi⟩ := not_forall.mp hi
    have he : θ i=Real.pi-B.delta := le_antisymm (hθ i).2 (le_of_not_gt hi)
    have hp : 1/2<B.p (θ i) := by
      rw [he,B.plateau _ ⟨by linarith [B.delta_alpha,d.alpha_lt,Real.pi_pos],le_rfl⟩]
      norm_num
    exact contDiffAt_const.congr_of_eventuallyEq
      (preferredUpperParticle_zero_germ d B F hzero s θ i hp)

/-- The exact derivative of a supported scalar function survives the
literal modulo lift, including its seam; there the derivative is zero. -/
theorem preferredLiftedFunction_hasFDerivAt {N : ℕ} (d : PreferredBranchData)
    (B : PreferredCoareaBump d) (f : (Fin N → ℝ) → ℂ)
    (hzero : ∀ θ i,1/2<B.p (θ i) → f θ=0)
    (θ : Fin N → ℝ) (A : (Fin N → ℝ) →L[ℝ] ℂ)
    (hf : HasFDerivAt f A (preferredLiftedAngles B.delta θ)) :
    HasFDerivAt (fun x => f (preferredLiftedAngles B.delta x)) A θ := by
  classical
  by_cases hi : ∀ i,preferredLiftedAngles B.delta θ i<Real.pi-B.delta
  · let T := fun x : Fin N → ℝ => preferredLiftedAngles B.delta θ+(x-θ)
    have hT : HasFDerivAt T (ContinuousLinearMap.id ℝ (Fin N → ℝ)) θ := by
      exact ((hasFDerivAt_id θ).sub_const θ).const_add (preferredLiftedAngles B.delta θ)
    have ht : T θ=preferredLiftedAngles B.delta θ := by simp [T]
    have hcomp : HasFDerivAt (f ∘ T) A θ := by
      have hh : HasFDerivAt f A (T θ) := by rw [ht]; exact hf
      simpa only [ContinuousLinearMap.comp_id] using hh.comp θ hT
    have he : (fun x => f (preferredLiftedAngles B.delta x))=ᶠ[𝓝 θ] f ∘ T := by
      filter_upwards [preferredLiftedAngles_eventually_affine B.delta θ hi] with x hx
      change f (preferredLiftedAngles B.delta x)=f (T x)
      apply congrArg f
      funext i
      exact congrFun hx i
    exact hcomp.congr_of_eventuallyEq he
  · obtain ⟨i,hi⟩ := not_forall.mp hi
    have hs : preferredLiftedAngles B.delta θ i=Real.pi-B.delta :=
      le_antisymm (preferredLiftedAngles_mem_oneSided B.delta θ i).2 (le_of_not_gt hi)
    have hp : 1/2<B.p (preferredLiftedAngles B.delta θ i) := by
      rw [hs,B.plateau _ ⟨by linarith [B.delta_alpha,d.alpha_lt,Real.pi_pos],le_rfl⟩]
      norm_num
    have he : f=ᶠ[𝓝 (preferredLiftedAngles B.delta θ)] fun _ => 0 := by
      have hc : ContinuousAt (fun x : Fin N → ℝ => B.p (x i)) (preferredLiftedAngles B.delta θ) :=
        B.smooth.continuous.continuousAt.comp (continuous_apply i).continuousAt
      filter_upwards [(continuousAt_const : ContinuousAt (fun _ : Fin N → ℝ => (1/2:ℝ)) _).eventually_lt hc hp] with x hx
      exact hzero x i hx
    have hA : A=0 := hf.unique ((hasFDerivAt_const (0:ℂ) _).congr_of_eventuallyEq he)
    rw [hA]
    have heL := preferredLiftedAngles_upper_zero_germ d B (fun z => f z.2)
      (fun _ x a ha => hzero x a ha) 0 θ i hs
    have heL' : (fun x => f (preferredLiftedAngles B.delta x))=ᶠ[𝓝 θ] fun _ => 0 :=
      heL.comp_tendsto ((show Continuous (fun x : Fin N → ℝ => ((0:ℂ),x)) by fun_prop).tendsto θ)
    exact (hasFDerivAt_const (0:ℂ) θ).congr_of_eventuallyEq heL'

end
end IsingBulk.Preferred22
