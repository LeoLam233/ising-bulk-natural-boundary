import IsingBulk.Tail.GlobalGeometry
import IsingBulk.Tail.SelectorIntegration
import IsingBulk.First.MeanRegularPhase
import IsingBulk.First.GlobalRootChartBridge
import IsingBulk.Analysis.LieTransport

/-! Literal mixed-sector phases and the full coupled contour differential.
Only true plateau columns become diagonal; occupancy is not frozen globally. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set Filter
open scoped Topology BigOperators ContDiff
set_option maxHeartbeats 1000000

theorem lowerArccos_analytic_upper {W : ℂ} (hW : 0<W.im) : AnalyticAt ℂ lowerArccos W :=
  lowerArccos_analytic_regular W (upper_sqrt_argument_slit hW)
    (Or.inr (inverseCosineRoot_upper_im hW).ne')

def mixedSourcePhase (s y : ℂ) : ℂ := lowerArccos (sourceW s y)
def mixedSourceTau (s y : ℂ) : ℂ := -(1-(s^2)⁻¹)/Complex.sin (mixedSourcePhase s y)
def mixedSourceSlope (s y : ℂ) : ℂ := Complex.I*(y-y⁻¹)/(2*Complex.sin (mixedSourcePhase s y))
def mixedSourceA (s y : ℂ) : ℂ := (1-(s^2)⁻¹)/(-Complex.I*(y-y⁻¹)/2)

theorem mixedSourcePhase_parameter {s y : ℂ} (hs : s≠0) (hW : 0<(sourceW s y).im) :
    HasDerivAt (fun t => mixedSourcePhase t y) (mixedSourceTau s y) s := by
  have hS : HasDerivAt (fun t : ℂ => sourceW t y) (1-(s^2)⁻¹) s := by
    exact ((hasDerivAt_id s).add (hasDerivAt_inv hs)).sub_const _
  have hp := (lowerArccos_hasDerivAt_regular _ (lowerArccos_analytic_upper hW)).comp s hS
  convert hp using 1
  · rfl
  · unfold mixedSourceTau mixedSourcePhase
    ring

theorem mixedSourcePhase_sin_ne {s y : ℂ} (hW : 0<(sourceW s y).im) :
    Complex.sin (mixedSourcePhase s y)≠0 := by
  have h := (lowerArccos_hasDerivAt_regular _ (lowerArccos_analytic_upper hW)).ccos
  have hc : (fun z => Complex.cos (lowerArccos z))=id := funext cos_lowerArccos
  rw [hc] at h
  have he := h.unique (hasDerivAt_id (sourceW s y))
  intro hz
  change Complex.sin (lowerArccos (sourceW s y))=0 at hz
  simp [hz] at he

theorem mixedSourceSlope_mul_A {s y : ℂ} (hy : y-y⁻¹≠0) :
    mixedSourceSlope s y*mixedSourceA s y=mixedSourceTau s y := by
  unfold mixedSourceSlope mixedSourceA mixedSourceTau
  generalize Complex.sin (mixedSourcePhase s y)=t
  generalize 1-(s^2)⁻¹=a
  generalize y-y⁻¹=b at hy ⊢
  by_cases ht : t=0
  · simp [ht]
  · field_simp [hy,ht]

def mixedContourPhase {N : ℕ} (f : SelectorFunctions) (r τ lam : ℝ)
    (s : ℂ) (θ : Fin N → ℝ) (i : Fin N) : ℂ := mixedSourcePhase s (deformedPoint f r τ lam θ i)

theorem mixed_deformedPoint_coordinate {N : ℕ} (f : SelectorFunctions) {r : ℝ} (hr : 0<r)
    (τ lam : ℝ) (θ : Fin N → ℝ) (k i : Fin N)
    (hp : ∀ j,DifferentiableAt ℝ f.p (θ j)) (hm : ∀ j,DifferentiableAt ℝ f.m (θ j)) :
    HasDerivAt (fun u => deformedPoint f r τ lam (Function.update θ k u) i)
      (deformedPoint f r τ lam θ i*angularJacobian f τ lam θ i k) (θ k) := by
  have hd := (logContour_coordinate_deriv f r τ lam θ k i hp hm).cexp
  simp_rw [← deformedPoint_exp_log f hr τ lam] at hd
  simpa only [Function.update_eq_self] using hd

theorem mixedContourPhase_coordinate {N : ℕ} (f : SelectorFunctions) {r : ℝ} (hr : 0<r)
    (τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ) (k i : Fin N)
    (hp : ∀ j,DifferentiableAt ℝ f.p (θ j)) (hm : ∀ j,DifferentiableAt ℝ f.m (θ j))
    (hW : 0<(sourceW s (deformedPoint f r τ lam θ i)).im) :
    HasDerivAt (fun u => mixedContourPhase f r τ lam s (Function.update θ k u) i)
      (((deformedPoint f r τ lam θ i)-(deformedPoint f r τ lam θ i)⁻¹)/
        (2*Complex.sin (mixedContourPhase f r τ lam s θ i))*angularJacobian f τ lam θ i k) (θ k) := by
  let y := deformedPoint f r τ lam θ i
  let M := angularJacobian f τ lam θ i k
  have hy := mixed_deformedPoint_coordinate f hr τ lam θ k i hp hm
  have hy0 : y≠0 := deformedPoint_nonzero f hr.ne' τ lam θ i
  have hyi := hy.inv (by simpa only [Function.update_eq_self] using hy0)
  have hWder := (hasDerivAt_const (θ k) (sourceS s)).sub ((hy.add hyi).div_const 2)
  have hpder := ((lowerArccos_hasDerivAt_regular _ (lowerArccos_analytic_upper hW)).hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt_of_eq (θ k) hWder (by simp [sourceW])
  convert hpder using 1
  · funext u
    rfl
  · dsimp only [mixedContourPhase,mixedSourcePhase]
    simp only [Function.update_eq_self]
    change (y-y⁻¹)/(2*Complex.sin (lowerArccos (sourceW s y)))*M =
      (0-(y*M+ -(y*M)/y^2)/2)*(-1/Complex.sin (lowerArccos (sourceW s y)))
    field_simp
    ring

theorem mixedContourPhase_plateau_coordinate {N : ℕ} (f : SelectorFunctions) {r : ℝ} (hr : 0<r)
    (τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ) (k i : Fin N)
    (hp : ∀ j,DifferentiableAt ℝ f.p (θ j)) (hm : ∀ j,DifferentiableAt ℝ f.m (θ j))
    (hpk : deriv f.p (θ k)=0) (hmk : deriv f.m (θ k)=0)
    (hW : 0<(sourceW s (deformedPoint f r τ lam θ i)).im) :
    coordDeriv (fun x => mixedContourPhase f r τ lam s x i) θ k =
      if i=k then mixedSourceSlope s (deformedPoint f r τ lam θ i) else 0 := by
  rw [coordDeriv,(mixedContourPhase_coordinate f hr τ lam s θ k i hp hm hW).deriv]
  rw [show angularJacobian f τ lam θ i k = if i=k then Complex.I else 0 from
    retractionJacobian_named_column lam τ _ _ _ _ k hpk hmk i]
  by_cases hik : i=k
  · simp only [hik,ite_true,mixedSourceSlope,mixedContourPhase]
    ring
  · simp [hik]

def mixedContourPhaseSum {N : ℕ} (f : SelectorFunctions) (r τ lam : ℝ)
    (s : ℂ) (θ : Fin N → ℝ) : ℂ := ∑ i,mixedContourPhase f r τ lam s θ i

def mixedContourVelocity {N : ℕ} (J : Finset (Fin N)) (j q : Fin N)
    (f : SelectorFunctions) (r τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ) : Fin N → ℂ :=
  let y := deformedPoint f r τ lam θ
  let a := fun i => mixedSourceA s (y i)
  let b := fun i => mixedSourceSlope s (y i)
  let D := ∑ i ∈ Finset.univ.filter (fun i => i∉J),mixedSourceTau s (y i)
  mixedVelocity J a j q ((D+b q*(∑ i∈J,a i))/(b j-b q))

def mixedCoordinateTransport {N : ℕ} (V : ℂ → (Fin N → ℝ) → Fin N → ℂ)
    (A : ℂ → (Fin N → ℝ) → ℂ) (s : ℂ) (θ : Fin N → ℝ) : ℂ :=
  deriv (fun t => A t θ) s-∑ i,V s θ i*coordDeriv (A s) θ i

theorem mixedCoordinateTransport_eq_lie {n : ℕ}
    (V : ℂ → (Fin (n+1) → ℝ) → Fin (n+1) → ℂ) (A : ℂ → (Fin (n+1) → ℝ) → ℂ)
    (s : ℂ) (θ : Fin (n+1) → ℝ) (hA : DifferentiableAt ℝ (A s) θ) :
    mixedCoordinateTransport V A s θ=IsingBulk.Lie.transport V A s θ := by
  simp only [mixedCoordinateTransport,IsingBulk.Lie.transport,coordDeriv_eq_fderiv _ _ hA]

theorem mixedContourPhaseSum_parameter {N : ℕ} (f : SelectorFunctions) (r τ lam : ℝ)
    (s : ℂ) (θ : Fin N → ℝ) (hs : s≠0)
    (hW : ∀ i,0<(sourceW s (deformedPoint f r τ lam θ i)).im) :
    HasDerivAt (fun t => mixedContourPhaseSum f r τ lam t θ)
      (∑ i,mixedSourceTau s (deformedPoint f r τ lam θ i)) s :=
  HasDerivAt.fun_sum (fun i _ => mixedSourcePhase_parameter hs (hW i))

theorem mixedContourPhaseSum_plateau_coordinate {N : ℕ} (f : SelectorFunctions) {r : ℝ} (hr : 0<r)
    (τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ) (k : Fin N)
    (hp : ∀ j,DifferentiableAt ℝ f.p (θ j)) (hm : ∀ j,DifferentiableAt ℝ f.m (θ j))
    (hpk : deriv f.p (θ k)=0) (hmk : deriv f.m (θ k)=0)
    (hW : ∀ i,0<(sourceW s (deformedPoint f r τ lam θ i)).im) :
    coordDeriv (mixedContourPhaseSum f r τ lam s) θ k =
      mixedSourceSlope s (deformedPoint f r τ lam θ k) := by
  unfold coordDeriv mixedContourPhaseSum
  rw [deriv_fun_sum (fun i _ => (mixedContourPhase_coordinate f hr τ lam s θ k i hp hm (hW i)).differentiableAt)]
  change (∑ i,coordDeriv (fun x => mixedContourPhase f r τ lam s x i) θ k)=_
  simp_rw [mixedContourPhase_plateau_coordinate f hr τ lam s θ k _ hp hm hpk hmk (hW _)]
  simp

theorem mixedContourVelocity_zero {N : ℕ} (J : Finset (Fin N)) (j q k : Fin N)
    (f : SelectorFunctions) (r τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ)
    (hj : j∈J) (hk : k∉J) (hkq : k≠q) : mixedContourVelocity J j q f r τ lam s θ k=0 := by
  have hkj : k≠j := by intro he; subst k; exact hk hj
  simp [mixedContourVelocity,mixedVelocity,hk,hkj,hkq]

theorem mixed_phase_sum_frozen {N : ℕ} (J : Finset (Fin N)) (j q : Fin N)
    (f : SelectorFunctions) {r : ℝ} (hr : 0<r) (τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ)
    (hj : j∈J) (hs : s≠0)
    (hp : ∀ k,DifferentiableAt ℝ f.p (θ k)) (hm : ∀ k,DifferentiableAt ℝ f.m (θ k))
    (hplateau : ∀ k,k∈J ∨ k=q → deriv f.p (θ k)=0 ∧ deriv f.m (θ k)=0)
    (hW : ∀ i,0<(sourceW s (deformedPoint f r τ lam θ i)).im)
    (hg : ∀ i∈J,deformedPoint f r τ lam θ i-(deformedPoint f r τ lam θ i)⁻¹≠0)
    (hsep : mixedSourceSlope s (deformedPoint f r τ lam θ j)-mixedSourceSlope s (deformedPoint f r τ lam θ q)≠0) :
    mixedCoordinateTransport (mixedContourVelocity J j q f r τ lam)
      (mixedContourPhaseSum f r τ lam) s θ=0 := by
  let y := deformedPoint f r τ lam θ
  let a := fun i => mixedSourceA s (y i)
  let b := fun i => mixedSourceSlope s (y i)
  let D := ∑ i ∈ Finset.univ.filter (fun i => i∉J),mixedSourceTau s (y i)
  have hcoord (k : Fin N) : mixedContourVelocity J j q f r τ lam s θ k*
      coordDeriv (mixedContourPhaseSum f r τ lam s) θ k =
      b k*mixedContourVelocity J j q f r τ lam s θ k := by
    by_cases hk : k∈J ∨ k=q
    · rw [mixedContourPhaseSum_plateau_coordinate f hr τ lam s θ k hp hm
        (hplateau k hk).1 (hplateau k hk).2 hW]
      exact mul_comm _ _
    · rw [mixedContourVelocity_zero J j q k f r τ lam s θ hj
        (fun h => hk (Or.inl h)) (fun h => hk (Or.inr h))]
      simp
  unfold mixedCoordinateTransport
  rw [(mixedContourPhaseSum_parameter f r τ lam s θ hs hW).deriv]
  simp_rw [hcoord]
  change (∑ i,mixedSourceTau s (y i))-
    (∑ i,b i*mixedVelocity J a j q ((D+b q*(∑ i∈J,a i))/(b j-b q)) i)=0
  rw [mixedVelocity_freezes_second J a b j q D hsep]
  have hJa : (∑ i∈J,b i*a i)=(∑ i∈J,mixedSourceTau s (y i)) :=
    Finset.sum_congr rfl (fun i hi => mixedSourceSlope_mul_A (hg i hi))
  rw [hJa]
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => i∈J)
    (fun i => mixedSourceTau s (y i))
  simp only [Finset.filter_mem_eq_inter,Finset.univ_inter] at hsplit
  dsimp [D]
  linear_combination -hsplit

theorem mixedCoordinateTransport_exp {N : ℕ}
    (V : ℂ → (Fin N → ℝ) → Fin N → ℂ) (A : ℂ → (Fin N → ℝ) → ℂ)
    (c s : ℂ) (θ : Fin N → ℝ)
    (hAs : DifferentiableAt ℂ (fun t => A t θ) s)
    (hAx : ∀ i,DifferentiableAt ℝ (fun u => A s (Function.update θ i u)) (θ i)) :
    mixedCoordinateTransport V (fun t x => Complex.exp (c*A t x)) s θ =
      Complex.exp (c*A s θ)*c*mixedCoordinateTransport V A s θ := by
  have hs := ((hAs.hasDerivAt).const_mul c).cexp
  have hx (i : Fin N) := ((hAx i).hasDerivAt.const_mul c).cexp
  simp only [Function.update_eq_self] at hx
  unfold mixedCoordinateTransport
  rw [hs.deriv]
  simp only [coordDeriv]
  simp_rw [(hx _).deriv]
  rw [show (∑ i,V s θ i*(Complex.exp (c*A s θ)*(c*deriv (fun u => A s (Function.update θ i u)) (θ i)))) =
    (Complex.exp (c*A s θ)*c)*(∑ i,V s θ i*deriv (fun u => A s (Function.update θ i u)) (θ i)) by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring]
  ring

def mixedContourLogSum {N : ℕ} (f : SelectorFunctions) (r τ lam : ℝ) (θ : Fin N → ℝ) : ℂ :=
  ∑ i,logContour f r τ lam θ i

theorem mixed_log_sum_frozen {N : ℕ} (J : Finset (Fin N)) (j q : Fin N)
    (f : SelectorFunctions) (r τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ) (hj : j∈J)
    (hp : ∀ k,DifferentiableAt ℝ f.p (θ k)) (hm : ∀ k,DifferentiableAt ℝ f.m (θ k))
    (hplateau : ∀ k,k∈J ∨ k=q → deriv f.p (θ k)=0 ∧ deriv f.m (θ k)=0) :
    mixedCoordinateTransport (mixedContourVelocity J j q f r τ lam)
      (fun _ x => mixedContourLogSum f r τ lam x) s θ=0 := by
  have hcoord (k : Fin N) : mixedContourVelocity J j q f r τ lam s θ k*
      coordDeriv (mixedContourLogSum f r τ lam) θ k =
      mixedContourVelocity J j q f r τ lam s θ k*Complex.I := by
    by_cases hk : k∈J ∨ k=q
    · have hd := HasDerivAt.fun_sum (fun i (_ : i∈Finset.univ) => logContour_coordinate_deriv f r τ lam θ k i hp hm)
      have hc : coordDeriv (mixedContourLogSum f r τ lam) θ k=Complex.I := by
        unfold coordDeriv mixedContourLogSum
        rw [hd.deriv]
        have hcol (i : Fin N) : angularJacobian f τ lam θ i k=if i=k then Complex.I else 0 :=
          retractionJacobian_named_column lam τ _ _ _ _ k (hplateau k hk).1 (hplateau k hk).2 i
        simp_rw [hcol]
        simp
      rw [hc]
    · rw [mixedContourVelocity_zero J j q k f r τ lam s θ hj
        (fun h => hk (Or.inl h)) (fun h => hk (Or.inr h))]
      simp
  unfold mixedCoordinateTransport
  rw [deriv_const]
  simp_rw [hcoord]
  rw [← Finset.sum_mul]
  have hs : ∑ i,mixedContourVelocity J j q f r τ lam s θ i=0 := mixedVelocity_sum _ _ _ _ _
  rw [hs]
  ring

theorem mixed_actual_Y_exp {N : ℕ} (f : SelectorFunctions) {r : ℝ} (hr : 0<r)
    (τ lam : ℝ) (θ : Fin N → ℝ) :
    coordinateProduct (deformedPoint f r τ lam θ)=Complex.exp (mixedContourLogSum f r τ lam θ) := by
  simp only [mixedContourLogSum,Complex.exp_sum,coordinateProduct]
  exact Finset.prod_congr rfl (fun i _ => deformedPoint_exp_log f hr τ lam θ i)

theorem mixed_actual_Z_exp {N : ℕ} (f : SelectorFunctions) (r τ lam : ℝ)
    (s : ℂ) (θ : Fin N → ℝ) :
    coordinateProduct (fun i => globalRoot s (deformedPoint f r τ lam θ i)) =
      Complex.exp (-Complex.I*mixedContourPhaseSum f r τ lam s θ) := by
  simp only [mixedContourPhaseSum,Finset.mul_sum,Complex.exp_sum,coordinateProduct,
    mixedContourPhase,mixedSourcePhase,globalRoot_eq_exp_lowerArccos]

theorem mixed_actual_Y_frozen {N : ℕ} (J : Finset (Fin N)) (j q : Fin N)
    (f : SelectorFunctions) {r : ℝ} (hr : 0<r) (τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ) (hj : j∈J)
    (hp : ∀ k,DifferentiableAt ℝ f.p (θ k)) (hm : ∀ k,DifferentiableAt ℝ f.m (θ k))
    (hplateau : ∀ k,k∈J ∨ k=q → deriv f.p (θ k)=0 ∧ deriv f.m (θ k)=0) :
    mixedCoordinateTransport (mixedContourVelocity J j q f r τ lam)
      (fun _ x => coordinateProduct (deformedPoint f r τ lam x)) s θ=0 := by
  simp_rw [mixed_actual_Y_exp f hr τ lam]
  have he := mixedCoordinateTransport_exp (mixedContourVelocity J j q f r τ lam)
    (fun _ x => mixedContourLogSum f r τ lam x) 1 s θ (differentiableAt_const _) (fun k =>
      (HasDerivAt.fun_sum (fun i (_ : i∈Finset.univ) => logContour_coordinate_deriv f r τ lam θ k i hp hm)).differentiableAt)
  simpa only [one_mul,mixed_log_sum_frozen J j q f r τ lam s θ hj hp hm hplateau,mul_zero] using he

theorem mixed_actual_Z_frozen {N : ℕ} (J : Finset (Fin N)) (j q : Fin N)
    (f : SelectorFunctions) {r : ℝ} (hr : 0<r) (τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ)
    (hj : j∈J) (hs : s≠0)
    (hp : ∀ k,DifferentiableAt ℝ f.p (θ k)) (hm : ∀ k,DifferentiableAt ℝ f.m (θ k))
    (hplateau : ∀ k,k∈J ∨ k=q → deriv f.p (θ k)=0 ∧ deriv f.m (θ k)=0)
    (hW : ∀ i,0<(sourceW s (deformedPoint f r τ lam θ i)).im)
    (hg : ∀ i∈J,deformedPoint f r τ lam θ i-(deformedPoint f r τ lam θ i)⁻¹≠0)
    (hsep : mixedSourceSlope s (deformedPoint f r τ lam θ j)-mixedSourceSlope s (deformedPoint f r τ lam θ q)≠0) :
    mixedCoordinateTransport (mixedContourVelocity J j q f r τ lam)
      (fun t x => coordinateProduct (fun i => globalRoot t (deformedPoint f r τ lam x i))) s θ=0 := by
  simp_rw [mixed_actual_Z_exp]
  rw [mixedCoordinateTransport_exp _ _ _ _ _
    (mixedContourPhaseSum_parameter f r τ lam s θ hs hW).differentiableAt
    (fun k => (HasDerivAt.fun_sum (fun i (_ : i∈Finset.univ) =>
      mixedContourPhase_coordinate f hr τ lam s θ k i hp hm (hW i))).differentiableAt)]
  rw [mixed_phase_sum_frozen J j q f hr τ lam s θ hj hs hp hm hplateau hW hg hsep,mul_zero]

theorem mixed_bump_sum_transport_zero {N : ℕ} (J : Finset (Fin N)) (j q : Fin N)
    (f : SelectorFunctions) (r τ lam : ℝ) (θ : Fin N → ℝ) (hj : j∈J)
    (g : ℝ → ℝ) (hg : ∀ i,DifferentiableAt ℝ g (θ i))
    (hplateau : ∀ i,i∈J ∨ i=q → deriv g (θ i)=0) (s : ℂ) :
    mixedCoordinateTransport (mixedContourVelocity J j q f r τ lam)
      (fun _ x => (occupancy (fun i => g (x i)):ℂ)) s θ=0 := by
  have hc (i : Fin N) : coordDeriv (fun x : Fin N → ℝ => (occupancy (fun k => g (x k)):ℂ)) θ i =
      ((deriv g (θ i):ℝ):ℂ) := by
    have h := (Complex.ofRealCLM.hasFDerivAt).comp_hasDerivAt (θ i)
      (hasDerivAt_occupancy_update g θ i (hg i))
    exact h.deriv
  unfold mixedCoordinateTransport
  rw [deriv_const]
  simp_rw [hc]
  have hz : ∑ i,mixedContourVelocity J j q f r τ lam s θ i*((deriv g (θ i):ℝ):ℂ)=0 := by
    rw [show (∑ i,mixedContourVelocity J j q f r τ lam s θ i*((deriv g (θ i):ℝ):ℂ)) =
      ∑ i,((deriv g (θ i):ℝ):ℂ)*mixedContourVelocity J j q f r τ lam s θ i by
        apply Finset.sum_congr rfl; intros; ring]
    apply mixedVelocity_preserves_plateau _ _ _ _ _ _ hj
    · intro i hi
      simp [hplateau i (Or.inl hi)]
    · simp [hplateau q (Or.inr rfl)]
  rw [hz]
  ring

/-- The plateau identity is an identity of parameter functions. Its entire
parameter jet vanishes even though the velocity coefficients vary with s. -/
theorem mixed_bump_sum_parameter_jets_zero {N : ℕ} (J : Finset (Fin N)) (j q : Fin N)
    (f : SelectorFunctions) (r τ lam : ℝ) (θ : Fin N → ℝ) (hj : j∈J)
    (g : ℝ → ℝ) (hg : ∀ i,DifferentiableAt ℝ g (θ i))
    (hplateau : ∀ i,i∈J ∨ i=q → deriv g (θ i)=0) (k : ℕ) (s : ℂ) :
    iteratedDeriv k (fun t => mixedCoordinateTransport (mixedContourVelocity J j q f r τ lam)
      (fun _ x => (occupancy (fun i => g (x i)):ℂ)) t θ) s=0 := by
  have he : (fun t => mixedCoordinateTransport (mixedContourVelocity J j q f r τ lam)
      (fun _ x => (occupancy (fun i => g (x i)):ℂ)) t θ)=fun _ => (0:ℂ) :=
    funext (mixed_bump_sum_transport_zero J j q f r τ lam θ hj g hg hplateau)
  rw [he]
  simp

def mixedZeroSelector : SelectorFunctions := ⟨fun _ => 0,fun _ => 0,fun _ => 0⟩

theorem mixed_deformed_zero_independent {N : ℕ} (f g : SelectorFunctions) (r τ : ℝ) (θ : Fin N → ℝ) :
    deformedPoint f r τ 0 θ=deformedPoint g r τ 0 θ := by
  funext i
  simp [deformedPoint]

theorem mixed_velocity_zero_independent {N : ℕ} (J : Finset (Fin N)) (j q : Fin N)
    (f g : SelectorFunctions) (r τ : ℝ) :
    mixedContourVelocity J j q f r τ 0=mixedContourVelocity J j q g r τ 0 := by
  funext s θ
  unfold mixedContourVelocity
  rw [mixed_deformed_zero_independent f g r τ θ]

/-- Original K has no deformation, so no plateau condition is needed on
its compact anchor or on any bump derivative. -/
theorem mixed_original_Y_frozen {N : ℕ} (J : Finset (Fin N)) (j q : Fin N)
    (f : SelectorFunctions) {r : ℝ} (hr : 0<r) (τ : ℝ) (s : ℂ) (θ : Fin N → ℝ) (hj : j∈J) :
    mixedCoordinateTransport (mixedContourVelocity J j q f r τ 0)
      (fun _ x => coordinateProduct (deformedPoint f r τ 0 x)) s θ=0 := by
  rw [mixed_velocity_zero_independent J j q f mixedZeroSelector r τ]
  simp_rw [mixed_deformed_zero_independent f mixedZeroSelector r τ]
  exact mixed_actual_Y_frozen J j q mixedZeroSelector hr τ 0 s θ hj
    (fun _ => differentiableAt_const _) (fun _ => differentiableAt_const _)
    (fun _ _ => by simp [mixedZeroSelector])

theorem mixed_original_Z_frozen {N : ℕ} (J : Finset (Fin N)) (j q : Fin N)
    (f : SelectorFunctions) {r : ℝ} (hr : 0<r) (τ : ℝ) (s : ℂ) (θ : Fin N → ℝ)
    (hj : j∈J) (hs : s≠0)
    (hW : ∀ i,0<(sourceW s (deformedPoint f r τ 0 θ i)).im)
    (hg : ∀ i∈J,deformedPoint f r τ 0 θ i-(deformedPoint f r τ 0 θ i)⁻¹≠0)
    (hsep : mixedSourceSlope s (deformedPoint f r τ 0 θ j)-mixedSourceSlope s (deformedPoint f r τ 0 θ q)≠0) :
    mixedCoordinateTransport (mixedContourVelocity J j q f r τ 0)
      (fun t x => coordinateProduct (fun i => globalRoot t (deformedPoint f r τ 0 x i))) s θ=0 := by
  rw [mixed_velocity_zero_independent J j q f mixedZeroSelector r τ]
  simp_rw [mixed_deformed_zero_independent f mixedZeroSelector r τ] at hW hg hsep ⊢
  exact mixed_actual_Z_frozen J j q mixedZeroSelector hr τ 0 s θ hj hs
    (fun _ => differentiableAt_const _) (fun _ => differentiableAt_const _)
    (fun _ _ => by simp [mixedZeroSelector]) hW hg hsep

end
end IsingBulk.Tail
