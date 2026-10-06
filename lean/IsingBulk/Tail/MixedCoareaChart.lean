import IsingBulk.Tail.MixedCoarea
import IsingBulk.Tail.CoareaRectangleKernel

/-! The literal two-angle phase chart: its derivative, determinant and
multiplicity are derived from the source contour rather than certified. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set Filter MeasureTheory
open scoped Topology BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def mixedPairEmbedding {N : ℕ} (j q : Fin N) : (ℝ × ℝ) →L[ℝ] (Fin N → ℝ) :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (Pi.single q 1)+
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (Pi.single j 1)

def mixedPairAngles {N : ℕ} (θ : Fin N → ℝ) (j q : Fin N) (p : ℝ × ℝ) : Fin N → ℝ :=
  Function.update (Function.update θ j p.2) q p.1

theorem mixedPairAngles_affine {N : ℕ} (θ : Fin N → ℝ) (j q : Fin N) (hjq : j≠q) :
    mixedPairAngles θ j q = fun p => mixedPairAngles θ j q 0+mixedPairEmbedding j q p := by
  funext p i
  by_cases hiq : i=q
  · subst i
    simp [mixedPairAngles,mixedPairEmbedding,Ne.symm hjq]
  · by_cases hij : i=j
    · subst i
      simp [mixedPairAngles,mixedPairEmbedding,hjq]
    · simp [mixedPairAngles,mixedPairEmbedding,hiq,hij]

theorem mixedPairAngles_hasFDerivAt {N : ℕ} (θ : Fin N → ℝ) (j q : Fin N) (hjq : j≠q) (p : ℝ × ℝ) :
    HasFDerivAt (mixedPairAngles θ j q) (mixedPairEmbedding j q) p := by
  rw [mixedPairAngles_affine θ j q hjq]
  exact (mixedPairEmbedding j q).hasFDerivAt.const_add _

theorem mixedPairEmbedding_sum {N : ℕ} (j q : Fin N) (v : ℝ × ℝ) :
    ∑ i,mixedPairEmbedding j q v i=v.1+v.2 := by
  simp [mixedPairEmbedding,Pi.single_apply,Finset.sum_add_distrib]

theorem mixedPairAngles_sum {N : ℕ} (θ : Fin N → ℝ) (j q : Fin N) (hjq : j≠q) (p : ℝ × ℝ) :
    ∑ i,mixedPairAngles θ j q p i=(∑ i,Function.update (Function.update θ j 0) q 0 i)+p.1+p.2 := by
  conv_lhs => rw [mixedPairAngles_affine θ j q hjq]
  simp only [Pi.add_apply,Finset.sum_add_distrib]
  rw [mixedPairEmbedding_sum]
  simp [mixedPairAngles,add_assoc]

def mixedPairPhase {N : ℕ} (f : SelectorFunctions) (r τ lam : ℝ) (s : ℂ)
    (θ : Fin N → ℝ) (j q : Fin N) (p : ℝ × ℝ) : ℝ × ℝ :=
  (∑ i,mixedPairAngles θ j q p i,(mixedContourPhaseSum f r τ lam s (mixedPairAngles θ j q p)).re)

def mixedPairPhaseDerivative {N : ℕ} (f : SelectorFunctions) (r τ lam : ℝ) (s : ℂ)
    (θ : Fin N → ℝ) (j q : Fin N) (p : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  ((ContinuousLinearMap.fst ℝ ℝ ℝ)+(ContinuousLinearMap.snd ℝ ℝ ℝ)).prod
    ((Complex.reCLM.comp (fderiv ℝ (mixedContourPhaseSum f r τ lam s) (mixedPairAngles θ j q p))).comp
      (mixedPairEmbedding j q))

theorem mixedPairPhase_hasFDerivAt {N : ℕ} (f : SelectorFunctions) {r : ℝ} (hr : 0<r)
    (τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ) (j q : Fin N) (hjq : j≠q) (p : ℝ × ℝ)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m)
    (hW : ∀ i,0<(sourceW s (deformedPoint f r τ lam (mixedPairAngles θ j q p) i)).im) :
    HasFDerivAt (mixedPairPhase f r τ lam s θ j q) (mixedPairPhaseDerivative f r τ lam s θ j q p) p := by
  have hF : HasFDerivAt (fun t : ℝ × ℝ => ∑ i,mixedPairAngles θ j q t i)
      ((ContinuousLinearMap.fst ℝ ℝ ℝ)+(ContinuousLinearMap.snd ℝ ℝ ℝ)) p := by
    simp_rw [mixedPairAngles_sum θ j q hjq]
    exact ((hasFDerivAt_fst (p := p)).const_add _).add (hasFDerivAt_snd (p := p))
  have hd := mixedContourPhaseSum_spatial_differentiable f hr τ lam s (mixedPairAngles θ j q p) hp hm hW
  have hG := (Complex.reCLM.hasFDerivAt.comp _ hd.hasFDerivAt).comp p
    (mixedPairAngles_hasFDerivAt θ j q hjq p)
  exact hF.prodMk hG

theorem mixedPairPhaseDerivative_det {N : ℕ} (f : SelectorFunctions) {r : ℝ} (hr : 0<r)
    (τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ) (j q : Fin N) (p : ℝ × ℝ)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m)
    (hplateau : ∀ k,k=j ∨ k=q → deriv f.p (mixedPairAngles θ j q p k)=0 ∧
      deriv f.m (mixedPairAngles θ j q p k)=0)
    (hW : ∀ i,0<(sourceW s (deformedPoint f r τ lam (mixedPairAngles θ j q p) i)).im) :
    (mixedPairPhaseDerivative f r τ lam s θ j q p).det =
      (mixedSourceSlope s (deformedPoint f r τ lam (mixedPairAngles θ j q p) j)-
        mixedSourceSlope s (deformedPoint f r τ lam (mixedPairAngles θ j q p) q)).re := by
  let x := mixedPairAngles θ j q p
  have hd := mixedContourPhaseSum_spatial_differentiable f hr τ lam s x hp hm hW
  have hcol (k : Fin N) (hk : k=j ∨ k=q) :
      fderiv ℝ (mixedContourPhaseSum f r τ lam s) x (Pi.single k 1)=
        mixedSourceSlope s (deformedPoint f r τ lam x k) := by
    rw [← coordDeriv_eq_fderiv _ _ hd k]
    exact mixedContourPhaseSum_plateau_coordinate f hr τ lam s x k
      (fun i => hp.differentiable (by simp) _) (fun i => hm.differentiable (by simp) _)
      (hplateau k hk).1 (hplateau k hk).2 hW
  rw [Complex.sub_re]
  apply det_sum_slope_map
  intro v
  apply Prod.ext
  · rfl
  · change (fderiv ℝ (mixedContourPhaseSum f r τ lam s) x
      (v.1 • Pi.single q 1+v.2 • Pi.single j 1)).re = _
    rw [map_add,map_smul,map_smul,hcol q (Or.inr rfl),hcol j (Or.inl rfl)]
    simp [mul_comm,x]

theorem mixedPairSection_convex {S : Set (ℝ × ℝ)} (hS : Convex ℝ S) (T : ℝ) :
    Convex ℝ {u : ℝ | (T-u,u)∈S} := by
  intro x hx y hy a b ha hb hab
  have hh := hS hx hy ha hb hab
  change (T-(a*x+b*y),a*x+b*y)∈S
  convert hh using 1
  apply Prod.ext
  · change T-(a*x+b*y)=a*(T-x)+b*(T-y)
    nlinarith [congrArg (fun t : ℝ => t*T) hab]
  · rfl

theorem mixedPairPhase_injOn {N : ℕ} (f : SelectorFunctions) {r : ℝ} (hr : 0<r)
    (τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ) (j q : Fin N) (hjq : j≠q)
    {S : Set (ℝ × ℝ)} (hS : Convex ℝ S)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m)
    (hplateau : ∀ p∈S,∀ k,k=j ∨ k=q → deriv f.p (mixedPairAngles θ j q p k)=0 ∧
      deriv f.m (mixedPairAngles θ j q p k)=0)
    (hW : ∀ p∈S,∀ i,0<(sourceW s (deformedPoint f r τ lam (mixedPairAngles θ j q p) i)).im)
    (hb : ∀ p∈S,mixedSourceSlope s (deformedPoint f r τ lam (mixedPairAngles θ j q p) j)≠0)
    (hcone : ∀ p∈S,(2/3:ℝ)*‖mixedSourceSlope s (deformedPoint f r τ lam (mixedPairAngles θ j q p) j)‖≤
      (mixedSourceSlope s (deformedPoint f r τ lam (mixedPairAngles θ j q p) j)).re)
    (hsep : ∀ p∈S,‖mixedSourceSlope s (deformedPoint f r τ lam (mixedPairAngles θ j q p) q)/
      mixedSourceSlope s (deformedPoint f r τ lam (mixedPairAngles θ j q p) j)‖≤(1/4:ℝ)) :
    InjOn (mixedPairPhase f r τ lam s θ j q) S := by
  have hmono (T : ℝ) : StrictMonoOn (mixedSlicePhase f r τ lam s θ j q T)
      {u : ℝ | (T-u,u)∈S} := by
    have hd (u : ℝ) (hu : (T-u,u)∈S) := mixedSlicePhase_hasDerivAt f hr τ lam s θ j q hjq T u hp hm
      (hplateau (T-u,u) hu) (hW (T-u,u) hu)
    apply strictMonoOn_of_deriv_pos (mixedPairSection_convex hS T)
    · exact fun u hu => (hd u hu).continuousAt.continuousWithinAt
    · intro u hu
      have hu' := interior_subset hu
      rw [(hd u hu').deriv]
      exact (mixed_jacobian_margin (hb (T-u,u) hu') (hcone (T-u,u) hu') (hsep (T-u,u) hu')).2
  intro x hx y hy he
  have hF : x.1+x.2=y.1+y.2 := by
    have hh := congrArg Prod.fst he
    change (∑ i,mixedPairAngles θ j q x i)=(∑ i,mixedPairAngles θ j q y i) at hh
    rw [mixedPairAngles_sum θ j q hjq x,mixedPairAngles_sum θ j q hjq y] at hh
    linarith
  let T := x.1+x.2
  have hxT : (T-x.2,x.2)=x := by
    apply Prod.ext
    · dsimp [T]
      ring
    · rfl
  have hyT : (T-y.2,y.2)=y := by
    apply Prod.ext
    · dsimp [T]
      linarith
    · rfl
  have hx' : x.2∈{u : ℝ | (T-u,u)∈S} := by change (T-x.2,x.2)∈S; rw [hxT]; exact hx
  have hy' : y.2∈{u : ℝ | (T-u,u)∈S} := by change (T-y.2,y.2)∈S; rw [hyT]; exact hy
  have hG : mixedSlicePhase f r τ lam s θ j q T x.2=mixedSlicePhase f r τ lam s θ j q T y.2 := by
    change (mixedPairPhase f r τ lam s θ j q (T-x.2,x.2)).2=(mixedPairPhase f r τ lam s θ j q (T-y.2,y.2)).2
    rw [hxT,hyT,he]
  have he₂ := (hmono T).injOn hx' hy' hG
  apply Prod.ext
  · linarith
  · exact he₂

theorem mixedContourSlope_continuousAt {N : ℕ} (f : SelectorFunctions) {r : ℝ} (hr : 0<r)
    (τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ) (i : Fin N)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m)
    (hW : 0<(sourceW s (deformedPoint f r τ lam θ i)).im) :
    ContinuousAt (fun x => mixedSourceSlope s (deformedPoint f r τ lam x i)) θ := by
  have hy : ContinuousAt (fun x : Fin N → ℝ => deformedPoint f r τ lam x i) θ := by
    have hp' := hp.continuous
    have hm' := hm.continuous
    unfold deformedPoint retractionShift occupancy
    fun_prop
  have hphi := (mixedContourPhase_spatial_differentiable f hr τ lam s θ i hp hm hW).continuousAt
  have hsin := Complex.continuous_sin.continuousAt.comp hphi
  exact (continuousAt_const.mul (hy.sub (hy.inv₀ (deformedPoint_nonzero f hr.ne' τ lam θ i)))).div
    (continuousAt_const.mul hsin) (mul_ne_zero (by norm_num) (mixedSourcePhase_sin_ne hW))

/-- Actual injective two-phase integration on any convex source angular
cell. Both phase lengths and translated period counts are included. -/
theorem mixed_actual_two_phase_coarea {N : ℕ} (f : SelectorFunctions) {r : ℝ} (hr : 0<r)
    (τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ) (j q : Fin N) (hjq : j≠q)
    {S : Set (ℝ × ℝ)} (hSm : MeasurableSet S) (hSc : Convex ℝ S)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m)
    (hbox : ∀ p∈S,mixedPairAngles θ j q p∈angleBox N)
    (hplateau : ∀ p∈S,∀ k,k=j ∨ k=q → deriv f.p (mixedPairAngles θ j q p k)=0 ∧
      deriv f.m (mixedPairAngles θ j q p k)=0)
    (hW : ∀ p∈S,∀ i,0<(sourceW s (deformedPoint f r τ lam (mixedPairAngles θ j q p) i)).im)
    (hb : ∀ p∈S,mixedSourceSlope s (deformedPoint f r τ lam (mixedPairAngles θ j q p) j)≠0)
    (hcone : ∀ p∈S,(2/3:ℝ)*‖mixedSourceSlope s (deformedPoint f r τ lam (mixedPairAngles θ j q p) j)‖≤
      (mixedSourceSlope s (deformedPoint f r τ lam (mixedPairAngles θ j q p) j)).re)
    (hsep : ∀ p∈S,‖mixedSourceSlope s (deformedPoint f r τ lam (mixedPairAngles θ j q p) q)/
      mixedSourceSlope s (deformedPoint f r τ lam (mixedPairAngles θ j q p) j)‖≤(1/4:ℝ))
    {aY aZ : ℝ} (haY : 0<aY) (haY1 : aY≤1) (haZ : 0<aZ) (haZ1 : aZ≤1) :
    IntegrableOn (fun p => ‖mixedSourceSlope s (deformedPoint f r τ lam (mixedPairAngles θ j q p) j)‖*
      twoPhaseKernel aY aZ (mixedPairPhase f r τ lam s θ j q p)) S ∧
    (∫ p in S, ‖mixedSourceSlope s (deformedPoint f r τ lam (mixedPairAngles θ j q p) j)‖*
      twoPhaseKernel aY aZ (mixedPairPhase f r τ lam s θ j q p)) ≤
      (12/5:ℝ)*((N:ℝ)*simpleKernelConstant*(1+|Real.log aY|))*
        ((N:ℝ)*simpleKernelConstant*(1+|Real.log aZ|)) := by
  let R := Icc (0:ℝ) ((N:ℝ)*(2*Real.pi)) ×ˢ Icc (0:ℝ) ((N:ℝ)*Real.pi)
  have himage : mixedPairPhase f r τ lam s θ j q '' S ⊆ R := by
    rintro _ ⟨p,hpS,rfl⟩
    refine ⟨⟨?_,?_⟩,mixedPhaseSum_bounds f r τ lam s _ (hW p hpS)⟩
    · change 0≤∑ i,mixedPairAngles θ j q p i
      exact Finset.sum_nonneg (fun i _ => (hbox p hpS).1 i)
    · have hh := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => (hbox p hpS).2 i)
      simpa only [mixedPairPhase,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using hh
  have hk := two_simple_kernel_rectangle (x₀ := 0) (x₁ := (N:ℝ)*(2*Real.pi))
    (y₀ := 0) (y₁ := (N:ℝ)*Real.pi) haY haY1 haZ haZ1 N N
    (by positivity) (by positivity) (by ring_nf; rfl) (by nlinarith [Real.pi_pos,(Nat.cast_nonneg N : (0:ℝ)≤N)])
  have ha : ContinuousOn (fun p => ‖mixedSourceSlope s (deformedPoint f r τ lam (mixedPairAngles θ j q p) j)‖) S := by
    intro p hpS
    exact ((mixedContourSlope_continuousAt f hr τ lam s _ j hp hm (hW p hpS j)).comp
      (mixedPairAngles_hasFDerivAt θ j q hjq p).continuousAt).norm.continuousWithinAt
  have hratio (p : ℝ × ℝ) (hpS : p∈S) :
      ‖mixedSourceSlope s (deformedPoint f r τ lam (mixedPairAngles θ j q p) j)‖ ≤
        (12/5:ℝ)*|(mixedPairPhaseDerivative f r τ lam s θ j q p).det| := by
    rw [mixedPairPhaseDerivative_det f hr τ lam s θ j q p hp hm (hplateau p hpS) (hW p hpS)]
    have hh := (mixed_jacobian_margin (hb p hpS) (hcone p hpS) (hsep p hpS)).1
    have hAbs := le_abs_self ((mixedSourceSlope s (deformedPoint f r τ lam (mixedPairAngles θ j q p) j)-
        mixedSourceSlope s (deformedPoint f r τ lam (mixedPairAngles θ j q p) q)).re)
    nlinarith
  have hmain := injective_weighted_coarea_le hSm (mixedPairPhase f r τ lam s θ j q)
    (mixedPairPhaseDerivative f r τ lam s θ j q)
    (fun p hpS => (mixedPairPhase_hasFDerivAt f hr τ lam s θ j q hjq p hp hm (hW p hpS)).hasFDerivWithinAt)
    (mixedPairPhase_injOn f hr τ lam s θ j q hjq hSc hp hm hplateau hW hb hcone hsep)
    himage _ _ ha (twoPhaseKernel_continuous haY haZ) (twoPhaseKernel_nonneg aY aZ) hk.1
    (by norm_num : (0:ℝ)≤12/5) (fun _ _ => norm_nonneg _) hratio
  refine ⟨hmain.1,hmain.2.trans ?_⟩
  have hh := mul_le_mul_of_nonneg_left hk.2 (by norm_num : (0:ℝ)≤12/5)
  simpa only [mul_assoc,R] using hh

end
end IsingBulk.Tail
