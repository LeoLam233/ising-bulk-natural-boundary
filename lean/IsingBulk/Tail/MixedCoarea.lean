import IsingBulk.Tail.MixedFrozenPhase
import IsingBulk.Tail.SimpleKernelBounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Calculus.MeanValue

/-! The actual mixed two-phase slice derivative and its real Jacobian.
One-dimensional substitution is applied only to the final absolute kernel. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set Filter MeasureTheory
open scoped Topology BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false

theorem mixed_jacobian_margin {bj bq : ℂ} (hb : bj≠0)
    (hcone : (2/3:ℝ)*‖bj‖≤bj.re) (hsep : ‖bq/bj‖≤(1/4:ℝ)) :
    (5/12:ℝ)*‖bj‖≤(bj-bq).re ∧ 0<(bj-bq).re := by
  have hbj : 0<‖bj‖ := norm_pos_iff.mpr hb
  rw [norm_div] at hsep
  have hq := (div_le_iff₀ hbj).mp hsep
  have hqr := (le_abs_self bq.re).trans (Complex.abs_re_le_norm bq)
  simp only [Complex.sub_re]
  constructor <;> nlinarith

def mixedSlice {N : ℕ} (θ : Fin N → ℝ) (j q : Fin N) (T u : ℝ) : Fin N → ℝ :=
  Function.update (Function.update θ j u) q (T-u)

theorem mixedSlice_hasDerivAt {N : ℕ} (θ : Fin N → ℝ) (j q : Fin N) (hjq : j≠q) (T u : ℝ) :
    HasDerivAt (mixedSlice θ j q T) (Pi.single j 1-Pi.single q 1) u := by
  apply hasDerivAt_pi.mpr
  intro i
  by_cases hiq : i=q
  · subst i
    simpa [mixedSlice,Pi.single_apply,hjq,Ne.symm hjq] using (hasDerivAt_id u).const_sub T
  · by_cases hij : i=j
    · subst i
      simp only [mixedSlice,Function.update_of_ne hiq,Function.update_self,Pi.sub_apply,
        Pi.single_eq_same,Pi.single_eq_of_ne hiq,sub_zero]
      convert hasDerivAt_id u using 1
      rfl
    · simpa [mixedSlice,Function.update_of_ne hiq,Function.update_of_ne hij,Pi.single_apply,hiq,hij] using
        hasDerivAt_const u (θ i)

theorem mixedContourPhase_spatial_differentiable {N : ℕ} (f : SelectorFunctions) {r : ℝ} (hr : 0<r)
    (τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ) (i : Fin N)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m)
    (hW : 0<(sourceW s (deformedPoint f r τ lam θ i)).im) :
    DifferentiableAt ℝ (fun x => mixedContourPhase f r τ lam s x i) θ := by
  have hp' := hp.differentiable (by simp)
  have hm' := hm.differentiable (by simp)
  have hy : DifferentiableAt ℝ (fun x : Fin N → ℝ => deformedPoint f r τ lam x i) θ := by
    unfold deformedPoint retractionShift occupancy
    fun_prop
  have hsum := hy.add (hy.inv (deformedPoint_nonzero f hr.ne' τ lam θ i))
  have hquot : DifferentiableAt ℝ (fun x : Fin N → ℝ =>
      (deformedPoint f r τ lam x i+(deformedPoint f r τ lam x i)⁻¹)/(2:ℂ)) θ := by
    convert hsum.fun_mul (differentiableAt_const ((2:ℂ)⁻¹)) using 1
    funext x
    simp only [div_eq_mul_inv,Pi.add_apply,Pi.inv_apply]
  have hWder : DifferentiableAt ℝ (fun x : Fin N → ℝ => sourceW s (deformedPoint f r τ lam x i)) θ :=
    (differentiableAt_const (sourceS s)).sub hquot
  change DifferentiableAt ℝ (fun x => lowerArccos (sourceW s (deformedPoint f r τ lam x i))) θ
  exact ((lowerArccos_analytic_upper hW).differentiableAt.restrictScalars ℝ).comp
    (f := fun x : Fin N → ℝ => sourceW s (deformedPoint f r τ lam x i)) θ hWder

theorem mixedContourPhaseSum_spatial_differentiable {N : ℕ} (f : SelectorFunctions) {r : ℝ} (hr : 0<r)
    (τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m)
    (hW : ∀ i,0<(sourceW s (deformedPoint f r τ lam θ i)).im) :
    DifferentiableAt ℝ (mixedContourPhaseSum f r τ lam s) θ :=
  DifferentiableAt.fun_sum (fun i _ => mixedContourPhase_spatial_differentiable f hr τ lam s θ i hp hm (hW i))

def mixedSlicePhase {N : ℕ} (f : SelectorFunctions) (r τ lam : ℝ) (s : ℂ)
    (θ : Fin N → ℝ) (j q : Fin N) (T u : ℝ) : ℝ :=
  (mixedContourPhaseSum f r τ lam s (mixedSlice θ j q T u)).re

theorem mixedSlicePhase_hasDerivAt {N : ℕ} (f : SelectorFunctions) {r : ℝ} (hr : 0<r)
    (τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ) (j q : Fin N) (hjq : j≠q) (T u : ℝ)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m)
    (hplateau : ∀ k,k=j ∨ k=q → deriv f.p (mixedSlice θ j q T u k)=0 ∧
      deriv f.m (mixedSlice θ j q T u k)=0)
    (hW : ∀ i,0<(sourceW s (deformedPoint f r τ lam (mixedSlice θ j q T u) i)).im) :
    HasDerivAt (mixedSlicePhase f r τ lam s θ j q T)
      ((mixedSourceSlope s (deformedPoint f r τ lam (mixedSlice θ j q T u) j)-
        mixedSourceSlope s (deformedPoint f r τ lam (mixedSlice θ j q T u) q)).re) u := by
  let x := mixedSlice θ j q T u
  have hdiff := mixedContourPhaseSum_spatial_differentiable f hr τ lam s x hp hm hW
  have hd := hdiff.hasFDerivAt.comp_hasDerivAt u (mixedSlice_hasDerivAt θ j q hjq T u)
  have he : fderiv ℝ (mixedContourPhaseSum f r τ lam s) x (Pi.single j 1-Pi.single q 1) =
      mixedSourceSlope s (deformedPoint f r τ lam x j)-mixedSourceSlope s (deformedPoint f r τ lam x q) := by
    rw [map_sub,← coordDeriv_eq_fderiv _ _ hdiff j,← coordDeriv_eq_fderiv _ _ hdiff q]
    rw [mixedContourPhaseSum_plateau_coordinate f hr τ lam s x j
      (fun k => hp.differentiable (by simp) _) (fun k => hm.differentiable (by simp) _)
      (hplateau j (Or.inl rfl)).1 (hplateau j (Or.inl rfl)).2 hW,
      mixedContourPhaseSum_plateau_coordinate f hr τ lam s x q
      (fun k => hp.differentiable (by simp) _) (fun k => hm.differentiable (by simp) _)
      (hplateau q (Or.inr rfl)).1 (hplateau q (Or.inr rfl)).2 hW]
  rw [he] at hd
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt u hd

/-- Genuine one-dimensional coarea on a fixed first-phase slice. The
Jacobian inequality absorbs the selected branch measure exactly once. -/
theorem mixed_slice_kernel_integral {a b κ : ℝ} (hab : a≤b) (hκ : 0<κ)
    (G G' w K : ℝ → ℝ) (hG : ∀ u∈Icc a b,HasDerivAt G (G' u) u)
    (hG' : ContinuousOn G' (Icc a b)) (hw : ContinuousOn w (Icc a b))
    (hK : Continuous K) (hK0 : ∀ t,0≤K t)
    (hjac : ∀ u∈Icc a b,κ*w u≤G' u) :
    (∫ u in a..b,w u*K (G u)) ≤ κ⁻¹*(∫ t in G a..G b,K t) := by
  have hGc : ContinuousOn G (Icc a b) := fun u hu => (hG u hu).continuousAt.continuousWithinAt
  have hKc := hK.comp_continuousOn hGc
  have hiw : IntervalIntegrable (fun u => w u*K (G u)) volume a b :=
    (hw.mul hKc).intervalIntegrable_of_Icc hab
  have hig : IntervalIntegrable (fun u => κ⁻¹*(K (G u)*G' u)) volume a b :=
    ((hKc.mul hG').const_mul _).intervalIntegrable_of_Icc hab
  have hbound : (∫ u in a..b,w u*K (G u)) ≤ ∫ u in a..b,κ⁻¹*(K (G u)*G' u) := by
    apply intervalIntegral.integral_mono_on hab hiw hig
    intro u hu
    have hh := mul_le_mul_of_nonneg_right (hjac u hu) (hK0 (G u))
    have hh' := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hκ.le)
    calc
      _ = κ⁻¹*((κ*w u)*K (G u)) := by field_simp
      _ ≤ κ⁻¹*(G' u*K (G u)) := hh'
      _ = _ := by ring
  apply hbound.trans_eq
  rw [intervalIntegral.integral_const_mul]
  congr 1
  simpa only [Function.comp_def] using intervalIntegral.integral_comp_mul_deriv
    (fun u hu => hG u (by simpa [uIcc_of_le hab] using hu))
    (by simpa [uIcc_of_le hab] using hG') hK

theorem mixedSourcePhase_upper_bounds {s y : ℂ} (hW : 0<(sourceW s y).im) :
    0<(mixedSourcePhase s y).re ∧ (mixedSourcePhase s y).re<Real.pi ∧
      (mixedSourcePhase s y).im<0 := by
  have hi := inverseCosineRoot_upper_im hW
  have hn := inverseCosineRoot_upper_norm hW
  have ha0 : 0<Complex.arg (inverseCosineRoot (sourceW s y)) := by
    have hnon := Complex.arg_nonneg_iff.mpr hi.le
    have hne : Complex.arg (inverseCosineRoot (sourceW s y))≠0 := by
      intro he
      have hz := (Complex.arg_eq_zero_iff.mp he).2
      linarith
    exact lt_of_le_of_ne hnon hne.symm
  have ha1 := Complex.arg_lt_pi_iff.mpr (Or.inr hi.ne')
  have hlog := Real.log_pos hn
  simpa [mixedSourcePhase,lowerArccos,Complex.mul_re,Complex.mul_im,Complex.log_re,Complex.log_im] using
    And.intro ha0 (And.intro ha1 (neg_neg_of_pos hlog))

theorem mixedPhaseSum_bounds {N : ℕ} (f : SelectorFunctions) (r τ lam : ℝ) (s : ℂ)
    (θ : Fin N → ℝ) (hW : ∀ i,0<(sourceW s (deformedPoint f r τ lam θ i)).im) :
    0≤(mixedContourPhaseSum f r τ lam s θ).re ∧
      (mixedContourPhaseSum f r τ lam s θ).re≤(N:ℝ)*Real.pi := by
  simp only [mixedContourPhaseSum,Complex.re_sum]
  constructor
  · exact Finset.sum_nonneg (fun i _ => (mixedSourcePhase_upper_bounds (hW i)).1.le)
  · have hh := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => (mixedSourcePhase_upper_bounds (hW i)).2.1.le)
    simpa [mixedContourPhase] using hh

/-- Multiplicity one on each actual fixed first-phase slice follows from
the branch cone and the separated compact slope. It is not a coarea premise. -/
theorem mixedSlicePhase_strictMonoOn {N : ℕ} (f : SelectorFunctions) {r : ℝ} (hr : 0<r)
    (τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ) (j q : Fin N) (hjq : j≠q) (T a b : ℝ)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m)
    (hplateau : ∀ u∈Icc a b,∀ k,k=j ∨ k=q → deriv f.p (mixedSlice θ j q T u k)=0 ∧
      deriv f.m (mixedSlice θ j q T u k)=0)
    (hW : ∀ u∈Icc a b,∀ i,0<(sourceW s (deformedPoint f r τ lam (mixedSlice θ j q T u) i)).im)
    (hb : ∀ u∈Icc a b,mixedSourceSlope s (deformedPoint f r τ lam (mixedSlice θ j q T u) j)≠0)
    (hcone : ∀ u∈Icc a b,(2/3:ℝ)*‖mixedSourceSlope s (deformedPoint f r τ lam (mixedSlice θ j q T u) j)‖≤
      (mixedSourceSlope s (deformedPoint f r τ lam (mixedSlice θ j q T u) j)).re)
    (hsep : ∀ u∈Icc a b,‖mixedSourceSlope s (deformedPoint f r τ lam (mixedSlice θ j q T u) q)/
      mixedSourceSlope s (deformedPoint f r τ lam (mixedSlice θ j q T u) j)‖≤(1/4:ℝ)) :
    StrictMonoOn (mixedSlicePhase f r τ lam s θ j q T) (Icc a b) := by
  have hd (u : ℝ) (hu : u∈Icc a b) := mixedSlicePhase_hasDerivAt f hr τ lam s θ j q hjq T u hp hm
    (hplateau u hu) (hW u hu)
  apply strictMonoOn_of_deriv_pos (convex_Icc a b)
  · exact fun u hu => (hd u hu).continuousAt.continuousWithinAt
  · intro u hu
    have hu' := interior_subset hu
    rw [(hd u hu').deriv]
    exact (mixed_jacobian_margin (hb u hu') (hcone u hu') (hsep u hu')).2

/-- Explicit unwrapped image length and period count after the one-dimensional
Jacobian has been consumed. The factor N is retained. -/
theorem mixed_slice_simple_kernel_integral {a b κ A : ℝ} (hab : a≤b) (hκ : 0<κ)
    (hA : 0<A) (hA1 : A≤1) (N : ℕ)
    (G G' w : ℝ → ℝ) (hG : ∀ u∈Icc a b,HasDerivAt G (G' u) u)
    (hG' : ContinuousOn G' (Icc a b)) (hw : ContinuousOn w (Icc a b))
    (hjac : ∀ u∈Icc a b,κ*w u≤G' u)
    (hGa : 0≤G a) (hGab : G a≤G b) (hGb : G b≤(N:ℝ)*Real.pi) :
    (∫ u in a..b,w u*(phaseDenominator (Real.exp (-A)) (G u))⁻¹) ≤
      κ⁻¹*((N:ℝ)*simpleKernelConstant*(1+|Real.log A|)) := by
  apply (mixed_slice_kernel_integral hab hκ G G' w _ hG hG' hw
    (simple_kernel_continuous hA) (fun t => inv_nonneg.mpr (norm_nonneg _)) hjac).trans
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hκ.le)
  apply simple_kernel_interval_integral hA hA1 N hGab
  nlinarith [Real.pi_pos,(Nat.cast_nonneg N : (0:ℝ)≤N)]

end
end IsingBulk.Tail
