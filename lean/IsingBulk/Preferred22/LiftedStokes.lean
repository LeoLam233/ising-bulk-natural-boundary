import IsingBulk.Preferred22.PuncturedDensitySmooth
import Mathlib.MeasureTheory.Integral.DivergenceTheorem

/-! Exact periodic boundary cancellation for the literal one-sided lift.
The Bochner divergence theorem is applied to genuine smooth currents. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set MeasureTheory
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false

/-- The constrained modulo lift is exactly periodic in every free angle,
including the compensating change of the eliminated last angle. -/
theorem preferredLiftedAngles_constrained_periodic {n : ℕ} (δ : ℝ)
    (θ : Fin n → ℝ) (i : Fin n) :
    preferredLiftedAngles δ (constrainedAngles (Function.update θ i (θ i+2*Real.pi)))=
      preferredLiftedAngles δ (constrainedAngles θ) := by
  ext j
  refine Fin.lastCases ?_ (fun a => ?_) j
  · simp only [preferredLiftedAngles,constrainedAngles,Fin.snoc_last]
    have hsum : (∑ a,Function.update θ i (θ i+2*Real.pi) a)=(∑ a,θ a)+2*Real.pi := by
      rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
      rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ i) θ]
      ring
    rw [hsum,neg_add]
    exact (toIocMod_periodic (by positivity : 0<2*Real.pi) (-Real.pi-δ)).sub_eq _
  · simp only [preferredLiftedAngles,constrainedAngles,Fin.snoc_castSucc]
    by_cases ha : a=i
    · subst a
      simp only [Function.update_self]
      exact toIocMod_periodic (by positivity : 0<2*Real.pi) (-Real.pi-δ) _
    · rw [Function.update_of_ne ha]

/-- Exact ordinary periodic Stokes on the original angular Haar box. -/
theorem preferred_periodic_divergence_integral {n : ℕ}
    (F : Fin n → (Fin n → ℝ) → ℂ)
    (hF : ∀ i,ContDiff ℝ ∞ (F i))
    (hper : ∀ i θ,F i (Function.update θ i (θ i+2*Real.pi))=F i θ) :
    (∫ θ in angularBox n,∑ i,fderiv ℝ (F i) θ (Pi.single i 1))=0 := by
  cases n with
  | zero => simp
  | succ n =>
    let a : Fin (n+1) → ℝ := fun _ => -Real.pi
    let b : Fin (n+1) → ℝ := fun _ => Real.pi
    have hab : a≤b := fun _ => by dsimp [a,b]; linarith [Real.pi_pos]
    have hc : Continuous (fun θ : Fin (n+1) → ℝ =>
        ∑ i,fderiv ℝ (F i) θ (Pi.single i 1)) := by
      apply continuous_finsetSum
      intro i _
      exact ((hF i).continuous_fderiv (by simp)).clm_apply continuous_const
    have hi := hc.continuousOn.integrableOn_compact (μ := volume) (isCompact_Icc : IsCompact (Icc a b))
    have hh := integral_divergence_of_hasFDerivAt_off_countable' a b hab F
      (fun i θ => fderiv ℝ (F i) θ) ∅ countable_empty
      (fun i => (hF i).continuous.continuousOn)
      (fun θ _ i => ((hF i).differentiable (by simp)).differentiableAt.hasFDerivAt) hi
    have hface (i : Fin (n+1)) (x : Fin n → ℝ) :
        F i (i.insertNth (b i) x)=F i (i.insertNth (a i) x) := by
      have he := hper i (i.insertNth (-Real.pi) x)
      simpa only [Fin.insertNth_apply_same,show -Real.pi+2*Real.pi=Real.pi by ring,
        Fin.update_insertNth,a,b] using he
    simp_rw [hface] at hh
    simp only [sub_self,Finset.sum_const_zero] at hh
    have hbox : angularBox (n+1)=ᵐ[volume] Icc a b := Measure.univ_pi_Ioc_ae_eq_Icc
    rw [setIntegral_congr_set hbox]
    exact hh

/-- Any genuinely smooth current on the literal lifted constrained torus
has zero intrinsic divergence integral. The periodicity is proved here. -/
theorem preferred_lifted_divergence_integral {n : ℕ} (δ : ℝ)
    (F : (Fin (n+1) → ℝ) → Fin (n+1) → ℂ)
    (hF : ∀ i : Fin n,ContDiff ℝ ∞ (fun θ : Fin n → ℝ =>
      F (preferredLiftedAngles δ (constrainedAngles θ)) i.castSucc)) :
    (∫ θ in angularBox n,∑ i : Fin n,
      fderiv ℝ (fun x : Fin n → ℝ => F (preferredLiftedAngles δ (constrainedAngles x)) i.castSucc)
        θ (Pi.single i 1))=0 := by
  apply preferred_periodic_divergence_integral _ hF
  intro i θ
  rw [preferredLiftedAngles_constrained_periodic]

/-- Tangency of a plateau-supported current is a genuine ambient germ,
even when its point is the endpoint of the one-sided period interval. -/
theorem preferred_supported_tangent_germ {N : ℕ} (d : PreferredBranchData)
    (B : PreferredCoareaBump d) (F : (Fin N → ℝ) → Fin N → ℂ)
    (hzero : ∀ x a,1/2<B.p (x a) → ∀ i,F x i=0)
    (htan : ∀ x,(∀ i,x i∈Ioo (-Real.pi-B.delta) (Real.pi-B.delta)) → (∑ i,F x i)=0)
    (θ : Fin N → ℝ) (hθ : ∀ i,θ i∈Ioc (-Real.pi-B.delta) (Real.pi-B.delta)) :
    ∀ᶠ x : Fin N → ℝ in 𝓝 θ,(∑ i,F x i)=0 := by
  classical
  by_cases hi : ∀ i,θ i<Real.pi-B.delta
  · have he : ∀ᶠ x : Fin N → ℝ in 𝓝 θ,∀ i,x i∈Ioo (-Real.pi-B.delta) (Real.pi-B.delta) := by
      apply Filter.eventually_all.mpr
      intro i
      exact (continuous_apply i).continuousAt.eventually (isOpen_Ioo.mem_nhds ⟨(hθ i).1,hi i⟩)
    filter_upwards [he] with x hx
    exact htan x hx
  · obtain ⟨a,ha⟩ := not_forall.mp hi
    have he : θ a=Real.pi-B.delta := le_antisymm (hθ a).2 (le_of_not_gt ha)
    have hp : 1/2<B.p (θ a) := by
      rw [he,B.plateau _ ⟨by linarith [B.delta_alpha,d.alpha_lt,Real.pi_pos],le_rfl⟩]
      norm_num
    have hc : ContinuousAt (fun x : Fin N → ℝ => B.p (x a)) θ :=
      B.smooth.continuous.continuousAt.comp (continuous_apply a).continuousAt
    filter_upwards [(continuousAt_const : ContinuousAt (fun _ : Fin N → ℝ => (1/2:ℝ)) θ).eventually_lt hc hp] with x hx
    exact Finset.sum_eq_zero (fun i _ => hzero x a hx i)

/-- The exact eliminated-coordinate derivative of a free angular basis
vector includes the last particle with coefficient minus one. -/
theorem constrainedAnglesCLM_single {n : ℕ} (i : Fin n) :
    constrainedAnglesCLM n (Pi.single i 1)=
      Pi.single i.castSucc (1:ℝ)-Pi.single (Fin.last n) 1 := by
  ext j
  refine Fin.lastCases ?_ (fun a => ?_) j
  · simp [constrainedAnglesCLM_apply,constrainedAngles]
  · by_cases ha : a=i
    · subst a
      simp [constrainedAnglesCLM_apply,constrainedAngles]
    · have hc : a.castSucc≠i.castSucc := by
        intro h
        exact ha (Fin.ext (congrArg (fun x : Fin (n+1) => x.val) h))
      simp [constrainedAnglesCLM_apply,constrainedAngles,Pi.single_apply,ha,hc]

/-- Intrinsic divergence of the actual lifted tangent current equals its
ambient divergence pointwise, with all last-coordinate contributions. -/
theorem preferred_lifted_intrinsic_divergence_point {n : ℕ} (d : PreferredBranchData)
    (B : PreferredCoareaBump d) (F : (Fin (n+1) → ℝ) → Fin (n+1) → ℂ)
    (hzero : ∀ x a,1/2<B.p (x a) → ∀ i,F x i=0)
    (htan : ∀ x,(∀ i,x i∈Ioo (-Real.pi-B.delta) (Real.pi-B.delta)) → (∑ i,F x i)=0)
    (θ : Fin n → ℝ)
    (hF : ∀ i,DifferentiableAt ℝ (fun x => F x i)
      (preferredLiftedAngles B.delta (constrainedAngles θ))) :
    (∑ i : Fin n,fderiv ℝ
      (fun x : Fin n → ℝ => F (preferredLiftedAngles B.delta (constrainedAngles x)) i.castSucc)
      θ (Pi.single i 1))=
      preferredAngularDivergence F (preferredLiftedAngles B.delta (constrainedAngles θ)) := by
  let x := preferredLiftedAngles B.delta (constrainedAngles θ)
  let A (i : Fin (n+1)) := fderiv ℝ (fun y => F y i) x
  let D : Matrix (Fin (n+1)) (Fin (n+1)) ℂ := fun i j => A i (Pi.single j 1)
  have hi (i : Fin n) : fderiv ℝ
      (fun z : Fin n → ℝ => F (preferredLiftedAngles B.delta (constrainedAngles z)) i.castSucc)
      θ (Pi.single i 1)=D i.castSucc i.castSucc-D i.castSucc (Fin.last n) := by
    have hl := preferredLiftedFunction_hasFDerivAt d B (fun y => F y i.castSucc)
      (fun y a ha => hzero y a ha i.castSucc) (constrainedAngles θ) (A i.castSucc) (hF i.castSucc).hasFDerivAt
    have hL : HasFDerivAt constrainedAngles (constrainedAnglesCLM n) θ := by
      have he : (constrainedAnglesCLM n : (Fin n → ℝ) → (Fin (n+1) → ℝ))=constrainedAngles :=
        funext (constrainedAnglesCLM_apply n)
      rw [←he]
      exact (constrainedAnglesCLM n).hasFDerivAt
    have hh := hl.comp θ hL
    have he := congrArg (fun L : (Fin n → ℝ) →L[ℝ] ℂ => L (Pi.single i 1)) hh.fderiv
    simpa only [Function.comp_def,ContinuousLinearMap.comp_apply,
      constrainedAnglesCLM_single,map_sub,A,D] using he
  have hd (i j : Fin (n+1)) : HasDerivAt (fun u : ℝ => F (Function.update x j u) i) (D i j) (x j) := by
    exact (hF i).hasFDerivAt.comp_hasDerivAt_of_eq (x j) (hasDerivAt_update x j (x j))
      (by simp only [Function.update_eq_self,x])
  have ht := preferred_supported_tangent_germ d B F hzero htan x
    (preferredLiftedAngles_mem_oneSided B.delta (constrainedAngles θ))
  rw [show (∑ i : Fin n,fderiv ℝ
      (fun z : Fin n → ℝ => F (preferredLiftedAngles B.delta (constrainedAngles z)) i.castSucc)
      θ (Pi.single i 1))=∑ i : Fin n,(D i.castSucc i.castSucc-D i.castSucc (Fin.last n)) by
        apply Finset.sum_congr rfl; intro i _; exact hi i]
  rw [preferred_actual_intrinsic_divergence F x D ht hd]
  unfold preferredAngularDivergence
  apply Finset.sum_congr rfl
  intro i _
  exact (hd i i).deriv.symm

end
end IsingBulk.Preferred22
