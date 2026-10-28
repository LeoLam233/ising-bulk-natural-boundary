import IsingBulk.Preferred22.LiftedStokes
import IsingBulk.HT22.Geometry.SignedShellCover

/-! Generic signed-total constrained Stokes. The affine shift is retained;
its derivative is the same eliminated-coordinate map and its measure is
unchanged. No old transported density is used. -/
namespace IsingBulk.HT22.Tail
noncomputable section
open IsingBulk.Preferred22 Set MeasureTheory
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false

theorem constrainedAtTotal_hasFDerivAt {n : ℕ} (c : ℝ) (θ : Fin n → ℝ) :
    HasFDerivAt (constrainedAtTotal c) (constrainedAnglesCLM n) θ := by
  have he : (constrainedAtTotal c : (Fin n → ℝ) → (Fin (n+1) → ℝ))=
      fun x => constrainedAnglesCLM n x+Pi.single (Fin.last n) c := by
    funext x i
    refine Fin.lastCases ?_ (fun a => ?_) i
    · simp [constrainedAtTotal,constrainedAnglesCLM_apply,constrainedAngles]; ring
    · simp [constrainedAtTotal,constrainedAnglesCLM_apply,constrainedAngles]
  rw [he]
  exact (constrainedAnglesCLM n).hasFDerivAt.add_const _

theorem constrainedAtTotal_contDiff {n : ℕ} (c : ℝ) :
    ContDiff ℝ ∞ (constrainedAtTotal (n:=n) c) := by
  have he : (constrainedAtTotal c : (Fin n → ℝ) → (Fin (n+1) → ℝ))=
      fun x => constrainedAnglesCLM n x+Pi.single (Fin.last n) c := by
    funext x i
    refine Fin.lastCases ?_ (fun a => ?_) i
    · simp [constrainedAtTotal,constrainedAnglesCLM_apply,constrainedAngles]; ring
    · simp [constrainedAtTotal,constrainedAnglesCLM_apply,constrainedAngles]
  rw [he]
  exact (constrainedAnglesCLM n).contDiff.add contDiff_const

theorem signedLiftedAngles_constrained_periodic {n : ℕ} (c δ : ℝ)
    (θ : Fin n → ℝ) (i : Fin n) :
    preferredLiftedAngles δ (constrainedAtTotal c (Function.update θ i (θ i+2*Real.pi)))=
      preferredLiftedAngles δ (constrainedAtTotal c θ) := by
  ext j
  refine Fin.lastCases ?_ (fun a => ?_) j
  · simp only [preferredLiftedAngles,constrainedAtTotal,Fin.snoc_last]
    have hsum : (∑ a,Function.update θ i (θ i+2*Real.pi) a)=(∑ a,θ a)+2*Real.pi := by
      rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
      rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ i) θ]
      ring
    rw [hsum,sub_add_eq_sub_sub]
    exact (toIocMod_periodic (by positivity : 0<2*Real.pi) (-Real.pi-δ)).sub_eq _
  · simp only [preferredLiftedAngles,constrainedAtTotal,Fin.snoc_castSucc]
    by_cases ha : a=i
    · subst a
      simp only [Function.update_self]
      exact toIocMod_periodic (by positivity : 0<2*Real.pi) (-Real.pi-δ) _
    · rw [Function.update_of_ne ha]


theorem signed_lifted_divergence_integral {n : ℕ} (c δ : ℝ)
    (F : (Fin (n+1) → ℝ) → Fin (n+1) → ℂ)
    (hF : ∀ i : Fin n,ContDiff ℝ ∞ (fun θ : Fin n → ℝ =>
      F (preferredLiftedAngles δ (constrainedAtTotal c θ)) i.castSucc)) :
    (∫ θ in angularBox n,∑ i : Fin n,
      fderiv ℝ (fun x : Fin n → ℝ => F (preferredLiftedAngles δ (constrainedAtTotal c x)) i.castSucc)
        θ (Pi.single i 1))=0 := by
  apply preferred_periodic_divergence_integral _ hF
  intro i θ
  rw [signedLiftedAngles_constrained_periodic]


theorem signed_lifted_intrinsic_divergence_point {n : ℕ} (c : ℝ) (d : PreferredBranchData)
    (B : PreferredCoareaBump d) (F : (Fin (n+1) → ℝ) → Fin (n+1) → ℂ)
    (hzero : ∀ x a,1/2<B.p (x a) → ∀ i,F x i=0)
    (htan : ∀ x,(∀ i,x i∈Ioo (-Real.pi-B.delta) (Real.pi-B.delta)) → (∑ i,F x i)=0)
    (θ : Fin n → ℝ)
    (hF : ∀ i,DifferentiableAt ℝ (fun x => F x i)
      (preferredLiftedAngles B.delta (constrainedAtTotal c θ))) :
    (∑ i : Fin n,fderiv ℝ
      (fun x : Fin n → ℝ => F (preferredLiftedAngles B.delta (constrainedAtTotal c x)) i.castSucc)
      θ (Pi.single i 1))=
      preferredAngularDivergence F (preferredLiftedAngles B.delta (constrainedAtTotal c θ)) := by
  let x := preferredLiftedAngles B.delta (constrainedAtTotal c θ)
  let A (i : Fin (n+1)) := fderiv ℝ (fun y => F y i) x
  let D : Matrix (Fin (n+1)) (Fin (n+1)) ℂ := fun i j => A i (Pi.single j 1)
  have hi (i : Fin n) : fderiv ℝ
      (fun z : Fin n → ℝ => F (preferredLiftedAngles B.delta (constrainedAtTotal c z)) i.castSucc)
      θ (Pi.single i 1)=D i.castSucc i.castSucc-D i.castSucc (Fin.last n) := by
    have hl := preferredLiftedFunction_hasFDerivAt d B (fun y => F y i.castSucc)
      (fun y a ha => hzero y a ha i.castSucc) (constrainedAtTotal c θ) (A i.castSucc) (hF i.castSucc).hasFDerivAt
    have hL := constrainedAtTotal_hasFDerivAt c θ
    have hh := hl.comp θ hL
    have he := congrArg (fun L : (Fin n → ℝ) →L[ℝ] ℂ => L (Pi.single i 1)) hh.fderiv
    simpa only [Function.comp_def,ContinuousLinearMap.comp_apply,
      constrainedAnglesCLM_single,map_sub,A,D] using he
  have hd (i j : Fin (n+1)) : HasDerivAt (fun u : ℝ => F (Function.update x j u) i) (D i j) (x j) := by
    exact (hF i).hasFDerivAt.comp_hasDerivAt_of_eq (x j) (hasDerivAt_update x j (x j))
      (by simp only [Function.update_eq_self,x])
  have ht := preferred_supported_tangent_germ d B F hzero htan x
    (preferredLiftedAngles_mem_oneSided B.delta (constrainedAtTotal c θ))
  rw [show (∑ i : Fin n,fderiv ℝ
      (fun z : Fin n → ℝ => F (preferredLiftedAngles B.delta (constrainedAtTotal c z)) i.castSucc)
      θ (Pi.single i 1))=∑ i : Fin n,(D i.castSucc i.castSucc-D i.castSucc (Fin.last n)) by
        apply Finset.sum_congr rfl; intro i _; exact hi i]
  rw [preferred_actual_intrinsic_divergence F x D ht hd]
  unfold preferredAngularDivergence
  apply Finset.sum_congr rfl
  intro i _
  exact (hd i i).deriv.symm

end
end IsingBulk.HT22.Tail
