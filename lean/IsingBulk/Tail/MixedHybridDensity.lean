import IsingBulk.Tail.MixedResidualTransport
import IsingBulk.Tail.MixedCoarea

/-! Actual mixed derivatives for the hybrid volume factor. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set Filter
open scoped Topology BigOperators ContDiff

theorem mixed_real_sin {F : ℝ → ℂ} {z : ℂ} {x : ℝ} (h : HasDerivAt F z x) :
    HasDerivAt (fun u => Complex.sin (F u)) (Complex.cos (F x)*z) x := by
  convert ((Complex.hasDerivAt_sin (F x)).hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt x h using 1 <;>
    first | rfl | simp [mul_comm]

def mixedSourceMixed (s y : ℂ) : ℂ :=
  (Complex.I*(y-y⁻¹)/2)*(1-(s^2)⁻¹)*Complex.cos (mixedSourcePhase s y)/
    (Complex.sin (mixedSourcePhase s y))^3

def mixedSourceSpatialSlope (s y : ℂ) : ℂ :=
  (-(y+y⁻¹)/2*Complex.sin (mixedSourcePhase s y)-
    (Complex.I*(y-y⁻¹)/2)*(Complex.cos (mixedSourcePhase s y)*mixedSourceSlope s y))/
    (Complex.sin (mixedSourcePhase s y))^2

theorem mixedSourceSlope_parameter {s y : ℂ} (hs : s≠0) (hW : 0<(sourceW s y).im) :
    HasDerivAt (fun t => mixedSourceSlope t y) (mixedSourceMixed s y) s := by
  have hn := mixedSourcePhase_sin_ne hW
  have hh := (hasDerivAt_const s (Complex.I*(y-y⁻¹)/2)).div
    (mixedSourcePhase_parameter hs hW).csin hn
  convert hh using 1
  · funext t
    simp only [mixedSourceSlope,Pi.div_apply]
    ring
  · unfold mixedSourceMixed mixedSourceTau
    field_simp
    ring

theorem mixedSourceTau_active_coordinate {N : ℕ} (f : SelectorFunctions) {r : ℝ} (hr : 0<r)
    (τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ) (k i : Fin N)
    (hp : ∀ j,DifferentiableAt ℝ f.p (θ j)) (hm : ∀ j,DifferentiableAt ℝ f.m (θ j))
    (hpk : deriv f.p (θ k)=0) (hmk : deriv f.m (θ k)=0)
    (hW : 0<(sourceW s (deformedPoint f r τ lam θ i)).im) :
    HasDerivAt (fun u => mixedSourceTau s (deformedPoint f r τ lam (Function.update θ k u) i))
      (if i=k then mixedSourceMixed s (deformedPoint f r τ lam θ i) else 0) (θ k) := by
  have hn := mixedSourcePhase_sin_ne hW
  have hφ := mixedContourPhase_coordinate f hr τ lam s θ k i hp hm hW
  have hcol : angularJacobian f τ lam θ i k = if i=k then Complex.I else 0 :=
    retractionJacobian_named_column lam τ _ _ _ _ k hpk hmk i
  rw [hcol] at hφ
  have hh := (hasDerivAt_const (θ k) (-(1-(s^2)⁻¹))).div (mixed_real_sin hφ) (by simpa [mixedContourPhase] using hn)
  convert hh using 1
  · rfl
  · by_cases hik : i=k
    · simp only [hik,ite_true,Function.update_eq_self]
      unfold mixedSourceMixed mixedContourPhase
      field_simp
      ring
    · simp [hik]

/-- Parameter and own-angle derivatives commute on the actual coupled
contour whenever that active column is a true plateau. -/
theorem mixed_source_mixed_commute {N : ℕ} (f : SelectorFunctions) {r : ℝ} (hr : 0<r)
    (τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ) (i : Fin N) (hs : s≠0)
    (hp : ∀ j,DifferentiableAt ℝ f.p (θ j)) (hm : ∀ j,DifferentiableAt ℝ f.m (θ j))
    (hpi : deriv f.p (θ i)=0) (hmi : deriv f.m (θ i)=0)
    (hW : 0<(sourceW s (deformedPoint f r τ lam θ i)).im) :
    deriv (fun t => mixedSourceSlope t (deformedPoint f r τ lam θ i)) s =
      coordDeriv (fun x => mixedSourceTau s (deformedPoint f r τ lam x i)) θ i := by
  rw [(mixedSourceSlope_parameter hs hW).deriv,coordDeriv,
    (mixedSourceTau_active_coordinate f hr τ lam s θ i i hp hm hpi hmi hW).deriv]
  simp

theorem mixedSourceSlope_active_coordinate {N : ℕ} (f : SelectorFunctions) {r : ℝ} (hr : 0<r)
    (τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ) (k i : Fin N)
    (hp : ∀ j,DifferentiableAt ℝ f.p (θ j)) (hm : ∀ j,DifferentiableAt ℝ f.m (θ j))
    (hpk : deriv f.p (θ k)=0) (hmk : deriv f.m (θ k)=0)
    (hW : 0<(sourceW s (deformedPoint f r τ lam θ i)).im) :
    HasDerivAt (fun u => mixedSourceSlope s (deformedPoint f r τ lam (Function.update θ k u) i))
      (if i=k then mixedSourceSpatialSlope s (deformedPoint f r τ lam θ i) else 0) (θ k) := by
  let y := deformedPoint f r τ lam θ i
  have hy := mixed_deformedPoint_coordinate f hr τ lam θ k i hp hm
  have hn : y≠0 := deformedPoint_nonzero f hr.ne' τ lam θ i
  have hcol : angularJacobian f τ lam θ i k = if i=k then Complex.I else 0 :=
    retractionJacobian_named_column lam τ _ _ _ _ k hpk hmk i
  rw [hcol] at hy
  have hφ := mixedContourPhase_coordinate f hr τ lam s θ k i hp hm hW
  rw [hcol] at hφ
  have hnum := (((hy.sub (hy.inv (by simpa [y] using hn))).const_mul Complex.I).div_const 2)
  have hh := hnum.div (mixed_real_sin hφ) (by simpa [mixedContourPhase] using mixedSourcePhase_sin_ne hW)
  convert hh using 1
  · funext u
    simp only [mixedSourceSlope,mixedContourPhase,Pi.div_apply,Pi.sub_apply,Pi.inv_apply]
    ring
  · by_cases hik : i=k
    · simp only [hik,ite_true,Function.update_eq_self,Pi.sub_apply,Pi.inv_apply]
      unfold mixedSourceSpatialSlope mixedSourceSlope mixedContourPhase
      dsimp [y] at hn
      field_simp
      simp only [Complex.I_sq]
      ring
    · simp [hik]

def mixedHybridVolume {N : ℕ} (J : Finset (Fin N)) (f : SelectorFunctions)
    (r τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ) : ℂ :=
  ∏ i∈J,mixedSourceSlope s (deformedPoint f r τ lam θ i)

theorem mixedHybridVolume_parameter {N : ℕ} (J : Finset (Fin N)) (f : SelectorFunctions)
    (r τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ) (hs : s≠0)
    (hW : ∀ i∈J,0<(sourceW s (deformedPoint f r τ lam θ i)).im) :
    HasDerivAt (fun t => mixedHybridVolume J f r τ lam t θ)
      (∑ i∈J,(∏ k∈J.erase i,mixedSourceSlope s (deformedPoint f r τ lam θ k))*
        mixedSourceMixed s (deformedPoint f r τ lam θ i)) s := by
  convert HasDerivAt.fun_finsetProd (u := J)
    (fun i hi => mixedSourceSlope_parameter hs (hW i hi)) using 1
  rfl

theorem mixedHybridVolume_active_coordinate {N : ℕ} (J : Finset (Fin N)) (f : SelectorFunctions)
    {r : ℝ} (hr : 0<r) (τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ) (k : Fin N)
    (hp : ∀ i,DifferentiableAt ℝ f.p (θ i)) (hm : ∀ i,DifferentiableAt ℝ f.m (θ i))
    (hpk : deriv f.p (θ k)=0) (hmk : deriv f.m (θ k)=0)
    (hW : ∀ i∈J,0<(sourceW s (deformedPoint f r τ lam θ i)).im) :
    HasDerivAt (fun u => mixedHybridVolume J f r τ lam s (Function.update θ k u))
      (if k∈J then (∏ i∈J.erase k,mixedSourceSlope s (deformedPoint f r τ lam θ i))*
        mixedSourceSpatialSlope s (deformedPoint f r τ lam θ k) else 0) (θ k) := by
  have hh := HasDerivAt.fun_finsetProd (u := J) (fun i hi =>
    mixedSourceSlope_active_coordinate f hr τ lam s θ k i hp hm hpk hmk (hW i hi))
  convert hh using 1
  · rfl
  · simp only [Function.update_eq_self,smul_eq_mul,mul_ite,mul_zero,Finset.sum_ite_eq']

theorem mixedHybridVolume_transport {N : ℕ} (J : Finset (Fin N)) (j q : Fin N)
    (f : SelectorFunctions) {r : ℝ} (hr : 0<r) (τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ)
    (hj : j∈J) (hs : s≠0)
    (hp : ∀ k,DifferentiableAt ℝ f.p (θ k)) (hm : ∀ k,DifferentiableAt ℝ f.m (θ k))
    (hplateau : ∀ k,k∈J ∨ k=q → deriv f.p (θ k)=0 ∧ deriv f.m (θ k)=0)
    (hW : ∀ i∈J,0<(sourceW s (deformedPoint f r τ lam θ i)).im) :
    mixedCoordinateTransport (mixedContourVelocity J j q f r τ lam)
      (mixedHybridVolume J f r τ lam) s θ =
      ∑ i∈J,(∏ k∈J.erase i,mixedSourceSlope s (deformedPoint f r τ lam θ k))*
        (mixedSourceMixed s (deformedPoint f r τ lam θ i)-
          mixedContourVelocity J j q f r τ lam s θ i*mixedSourceSpatialSlope s (deformedPoint f r τ lam θ i)) := by
  have he (k : Fin N) : mixedContourVelocity J j q f r τ lam s θ k*
      coordDeriv (mixedHybridVolume J f r τ lam s) θ k =
      if k∈J then mixedContourVelocity J j q f r τ lam s θ k*
        ((∏ i∈J.erase k,mixedSourceSlope s (deformedPoint f r τ lam θ i))*
          mixedSourceSpatialSlope s (deformedPoint f r τ lam θ k)) else 0 := by
    by_cases hk : k∈J ∨ k=q
    · rw [coordDeriv,(mixedHybridVolume_active_coordinate J f hr τ lam s θ k hp hm
        (hplateau k hk).1 (hplateau k hk).2 hW).deriv]
      split_ifs <;> simp
    · rw [mixedContourVelocity_zero J j q k f r τ lam s θ hj
        (fun h => hk (Or.inl h)) (fun h => hk (Or.inr h))]
      simp
  unfold mixedCoordinateTransport
  rw [(mixedHybridVolume_parameter J f r τ lam s θ hs hW).deriv]
  simp_rw [he]
  simp only [Finset.sum_ite_mem,Finset.univ_inter]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- An explicit hybrid branch residual, before any analytic-coordinate
extension is chosen. -/
def mixedBranchResidual {N : ℕ} (J : Finset (Fin N)) (j q : Fin N)
    (f : SelectorFunctions) (r τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ) (i : Fin N) : ℂ :=
  mixedSourceTau s (deformedPoint f r τ lam θ i)-
    mixedSourceSlope s (deformedPoint f r τ lam θ i)*mixedContourVelocity J j q f r τ lam s θ i

theorem mixedBranchResidual_own_derivative {N : ℕ} (J : Finset (Fin N)) (j q i : Fin N)
    (f : SelectorFunctions) {r : ℝ} (hr : 0<r) (τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ)
    (hp : ∀ k,DifferentiableAt ℝ f.p (θ k)) (hm : ∀ k,DifferentiableAt ℝ f.m (θ k))
    (hpi : deriv f.p (θ i)=0) (hmi : deriv f.m (θ i)=0)
    (hW : 0<(sourceW s (deformedPoint f r τ lam θ i)).im)
    (hV : DifferentiableAt ℝ (fun u => mixedContourVelocity J j q f r τ lam s (Function.update θ i u) i) (θ i)) :
    coordDeriv (fun x => mixedBranchResidual J j q f r τ lam s x i) θ i =
      mixedSourceMixed s (deformedPoint f r τ lam θ i)-
      mixedSourceSpatialSlope s (deformedPoint f r τ lam θ i)*mixedContourVelocity J j q f r τ lam s θ i-
      mixedSourceSlope s (deformedPoint f r τ lam θ i)*
        coordDeriv (fun x => mixedContourVelocity J j q f r τ lam s x i) θ i := by
  have hτ := mixedSourceTau_active_coordinate f hr τ lam s θ i i hp hm hpi hmi hW
  have hb := mixedSourceSlope_active_coordinate f hr τ lam s θ i i hp hm hpi hmi hW
  have hh := (hτ.sub (hb.mul hV.hasDerivAt)).deriv
  convert hh using 1
  · rfl
  · simp only [ite_true,Function.update_eq_self,coordDeriv,sub_add_eq_sub_sub]

/-- The actual volume-factor identity underlying the mixed pullback Lie
formula. The compact part carries minus the angular divergence. -/
theorem mixedHybridVolume_density_transport {N : ℕ} (J : Finset (Fin N)) (j q : Fin N)
    (f : SelectorFunctions) {r : ℝ} (hr : 0<r) (τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ)
    (hj : j∈J) (hs : s≠0)
    (hp : ∀ k,DifferentiableAt ℝ f.p (θ k)) (hm : ∀ k,DifferentiableAt ℝ f.m (θ k))
    (hplateau : ∀ k,k∈J ∨ k=q → deriv f.p (θ k)=0 ∧ deriv f.m (θ k)=0)
    (hW : ∀ i∈J,0<(sourceW s (deformedPoint f r τ lam θ i)).im)
    (hb : ∀ i∈J,mixedSourceSlope s (deformedPoint f r τ lam θ i)≠0)
    (hV : ∀ i∈J,DifferentiableAt ℝ
      (fun u => mixedContourVelocity J j q f r τ lam s (Function.update θ i u) i) (θ i)) :
    mixedCoordinateTransport (mixedContourVelocity J j q f r τ lam)
      (mixedHybridVolume J f r τ lam) s θ-
      mixedHybridVolume J f r τ lam s θ*
        (∑ i,coordDeriv (fun x => mixedContourVelocity J j q f r τ lam s x i) θ i) =
    mixedHybridVolume J f r τ lam s θ*
      ((∑ i∈J,coordDeriv (fun x => mixedBranchResidual J j q f r τ lam s x i) θ i/
          mixedSourceSlope s (deformedPoint f r τ lam θ i))-
       ∑ i∈Finset.univ.filter (fun i => i∉J),
          coordDeriv (fun x => mixedContourVelocity J j q f r τ lam s x i) θ i) := by
  let b := fun i => mixedSourceSlope s (deformedPoint f r τ lam θ i)
  let v := fun i => mixedContourVelocity J j q f r τ lam s θ i
  let dv := fun i => coordDeriv (fun x => mixedContourVelocity J j q f r τ lam s x i) θ i
  let E := mixedHybridVolume J f r τ lam s θ
  have hprod (i : Fin N) (hi : i∈J) : E=(∏ k∈J.erase i,b k)*b i :=
    (Finset.prod_erase_mul _ _ hi).symm
  have hterm (i : Fin N) (hi : i∈J) : E*
      (coordDeriv (fun x => mixedBranchResidual J j q f r τ lam s x i) θ i/b i) =
      (∏ k∈J.erase i,b k)*(mixedSourceMixed s (deformedPoint f r τ lam θ i)-
        v i*mixedSourceSpatialSlope s (deformedPoint f r τ lam θ i))-E*dv i := by
    rw [mixedBranchResidual_own_derivative J j q i f hr τ lam s θ hp hm
      (hplateau i (Or.inl hi)).1 (hplateau i (Or.inl hi)).2 (hW i hi) (hV i hi),hprod i hi]
    have hn : b i≠0 := hb i hi
    dsimp [v,dv,b]
    dsimp [b] at hn
    field_simp
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => i∈J) dv
  simp only [Finset.filter_mem_eq_inter,Finset.univ_inter] at hsplit
  rw [mixedHybridVolume_transport J j q f hr τ lam s θ hj hs hp hm hplateau hW]
  change (∑ i∈J,(∏ k∈J.erase i,b k)*(mixedSourceMixed s (deformedPoint f r τ lam θ i)-
    v i*mixedSourceSpatialSlope s (deformedPoint f r τ lam θ i)))-E*(∑ i,dv i)=
    E*((∑ i∈J,coordDeriv (fun x => mixedBranchResidual J j q f r τ lam s x i) θ i/b i)-
      ∑ i∈Finset.univ.filter (fun i => i∉J),dv i)
  have hsum := Finset.sum_congr rfl hterm
  rw [← Finset.mul_sum,Finset.sum_sub_distrib,← Finset.mul_sum] at hsum
  linear_combination -hsum + E*hsplit

theorem mixedHybridVolume_spatial_differentiable {N : ℕ} (J : Finset (Fin N)) (f : SelectorFunctions)
    {r : ℝ} (hr : 0<r) (τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m)
    (hW : ∀ i∈J,0<(sourceW s (deformedPoint f r τ lam θ i)).im) :
    DifferentiableAt ℝ (mixedHybridVolume J f r τ lam s) θ := by
  have hfactor (i : Fin N) (hi : i∈J) : DifferentiableAt ℝ
      (fun x => mixedSourceSlope s (deformedPoint f r τ lam x i)) θ := by
    have hp' := hp.differentiable (by simp)
    have hm' := hm.differentiable (by simp)
    have hy : DifferentiableAt ℝ (fun x : Fin N → ℝ => deformedPoint f r τ lam x i) θ := by
      unfold deformedPoint retractionShift occupancy
      fun_prop
    have hnum := (hy.sub (hy.inv (deformedPoint_nonzero f hr.ne' τ lam θ i))).const_mul Complex.I
    have hphase := mixedContourPhase_spatial_differentiable f hr τ lam s θ i hp hm (hW i hi)
    have hsin := ((Complex.differentiable_sin (mixedContourPhase f r τ lam s θ i)).restrictScalars ℝ).comp
      θ hphase
    have hden := hsin.inv (mixedSourcePhase_sin_ne (hW i hi))
    convert (hnum.fun_mul hden).fun_mul (differentiableAt_const ((2:ℂ)⁻¹)) using 1
    funext x
    simp only [mixedSourceSlope,mixedContourPhase,Function.comp_apply,Pi.sub_apply,Pi.inv_apply]
    ring
  exact (HasFDerivAt.finsetProd (u := J) (fun i hi => (hfactor i hi).hasFDerivAt)).differentiableAt

theorem mixedHybridMap_spatial_differentiable {N : ℕ} (J : Finset (Fin N)) (f : SelectorFunctions)
    {r : ℝ} (hr : 0<r) (τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m)
    (hW : ∀ i∈J,0<(sourceW s (deformedPoint f r τ lam θ i)).im) :
    DifferentiableAt ℝ (mixedHybridMap J f r τ lam s) θ := by
  apply differentiableAt_pi.mpr
  intro i
  by_cases hi : i∈J
  · simpa only [mixedHybridMap,hi,ite_true] using
      mixedContourPhase_spatial_differentiable f hr τ lam s θ i hp hm (hW i hi)
  · simp only [mixedHybridMap,hi,ite_false]
    fun_prop

def mixedHybridDivergence {N : ℕ} (J : Finset (Fin N)) (j q : Fin N)
    (f : SelectorFunctions) (r τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ) : ℂ :=
  (∑ i∈J,coordDeriv (fun x => mixedBranchResidual J j q f r τ lam s x i) θ i/
      mixedSourceSlope s (deformedPoint f r τ lam θ i))-
    ∑ i∈Finset.univ.filter (fun i => i∉J),
      coordDeriv (fun x => mixedContourVelocity J j q f r τ lam s x i) θ i

theorem mixedHybridVolume_lie {n : ℕ} (J : Finset (Fin (n+1))) (j q : Fin (n+1))
    (f : SelectorFunctions) {r : ℝ} (hr : 0<r) (τ lam : ℝ) (s : ℂ) (θ : Fin (n+1) → ℝ)
    (hj : j∈J) (hs : s≠0) (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m)
    (hplateau : ∀ k,k∈J ∨ k=q → deriv f.p (θ k)=0 ∧ deriv f.m (θ k)=0)
    (hW : ∀ i∈J,0<(sourceW s (deformedPoint f r τ lam θ i)).im)
    (hb : ∀ i∈J,mixedSourceSlope s (deformedPoint f r τ lam θ i)≠0)
    (hV : ∀ i,DifferentiableAt ℝ (fun x => mixedContourVelocity J j q f r τ lam s x i) θ) :
    IsingBulk.Lie.lieStep (mixedContourVelocity J j q f r τ lam)
      (mixedHybridVolume J f r τ lam) s θ =
    mixedHybridVolume J f r τ lam s θ*mixedHybridDivergence J j q f r τ lam s θ := by
  have hvol := mixedHybridVolume_spatial_differentiable J f hr τ lam s θ hp hm hW
  rw [IsingBulk.Lie.lieStep_eq_transport_sub _ _ s θ hV hvol,
    ← mixedCoordinateTransport_eq_lie _ _ s θ hvol]
  have hdiv : IsingBulk.Lie.divergence (mixedContourVelocity J j q f r τ lam s) θ =
      ∑ i,coordDeriv (fun x => mixedContourVelocity J j q f r τ lam s x i) θ i := by
    unfold IsingBulk.Lie.divergence
    apply Finset.sum_congr rfl
    intro i _
    exact (coordDeriv_eq_fderiv _ θ (hV i) i).symm
  rw [hdiv,mul_comm (∑ i,_) _]
  apply mixedHybridVolume_density_transport J j q f hr τ lam s θ hj hs
    (fun k => hp.differentiable (by simp) _) (fun k => hm.differentiable (by simp) _)
    hplateau hW hb
  intro i _
  have hh := (hV i).hasFDerivAt.comp_hasDerivAt_of_eq (θ i)
    (hasDerivAt_update θ i (θ i)) (by simp)
  convert hh.differentiableAt using 1
  rfl

/-- Actual top-density pullback for the coupled mixed chart. No volume or
transport identity is assumed, and F lives in the regular hybrid variables. -/
theorem mixedHybridPullback_lie {n : ℕ} (J : Finset (Fin (n+1))) (j q : Fin (n+1))
    (f : SelectorFunctions) {r : ℝ} (hr : 0<r) (τ lam : ℝ) (s : ℂ) (θ : Fin (n+1) → ℝ)
    (F : ℂ → (Fin (n+1) → ℂ) → ℂ)
    (hj : j∈J) (hs : s≠0) (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m)
    (hplateau : ∀ k,k∈J ∨ k=q → deriv f.p (θ k)=0 ∧ deriv f.m (θ k)=0)
    (hW : ∀ i∈J,0<(sourceW s (deformedPoint f r τ lam θ i)).im)
    (hb : ∀ i∈J,mixedSourceSlope s (deformedPoint f r τ lam θ i)≠0)
    (hV : ∀ i,DifferentiableAt ℝ (fun x => mixedContourVelocity J j q f r τ lam s x i) θ)
    (hF : DifferentiableAt ℂ (fun z : ℂ × (Fin (n+1) → ℂ) => F z.1 z.2)
      (s,mixedHybridMap J f r τ lam s θ)) :
    IsingBulk.Lie.lieStep (mixedContourVelocity J j q f r τ lam)
      (fun t x => mixedHybridVolume J f r τ lam t x*F t (mixedHybridMap J f r τ lam t x)) s θ =
    mixedHybridVolume J f r τ lam s θ*
      (fderiv ℂ (fun z : ℂ × (Fin (n+1) → ℂ) => F z.1 z.2)
        (s,mixedHybridMap J f r τ lam s θ)
        (1,fun i => mixedCoordinateTransport (mixedContourVelocity J j q f r τ lam)
          (fun t x => mixedHybridMap J f r τ lam t x i) s θ)+
        mixedHybridDivergence J j q f r τ lam s θ*F s (mixedHybridMap J f r τ lam s θ)) := by
  let A := fun t x => F t (mixedHybridMap J f r τ lam t x)
  have hAs : DifferentiableAt ℂ (fun t => A t θ) s := by
    convert (hF.hasFDerivAt.comp_hasDerivAt s
      ((hasDerivAt_id s).prodMk (mixedHybridMap_parameter J f r τ lam s θ hs hW))).differentiableAt using 1
    rfl
  have hAx : DifferentiableAt ℝ (A s) θ := by
    convert ((hF.restrictScalars ℝ).comp θ ((differentiableAt_const s).prodMk
      (mixedHybridMap_spatial_differentiable J f hr τ lam s θ hp hm hW))) using 1
    rfl
  have hvol := mixedHybridVolume_spatial_differentiable J f hr τ lam s θ hp hm hW
  have he : (fun t x => mixedHybridVolume J f r τ lam t x*F t (mixedHybridMap J f r τ lam t x)) =
      fun t x => A t x*mixedHybridVolume J f r τ lam t x := by
    funext t x
    exact mul_comm _ _
  rw [he,IsingBulk.Lie.lieStep_product_rule _ _ _ s θ hAs
    (mixedHybridVolume_parameter J f r τ lam s θ hs hW).differentiableAt hAx hvol hV,
    mixedHybridVolume_lie J j q f hr τ lam s θ hj hs hp hm hplateau hW hb hV,
    ← mixedCoordinateTransport_eq_lie _ _ s θ hAx]
  rw [mixedHybrid_transport_chain J f hr τ lam s θ _ F hs
    (fun k => hp.differentiable (by simp) _) (fun k => hm.differentiable (by simp) _) hW hF]
  dsimp [A]
  ring

end
end IsingBulk.Tail
