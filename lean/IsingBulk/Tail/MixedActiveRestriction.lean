import IsingBulk.Tail.MixedFrozenPhase
import IsingBulk.Tail.SelectedFDiskSupport
import IsingBulk.Tail.ConstructedCurrentSupport

/-! Restriction to the active angles is exact at every Lie stage. Smooth
spectator bumps are parameters of the analytic chart, not holomorphic data. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set Filter
open scoped BigOperators Topology
set_option backward.isDefEq.respectTransparency false

def mixedFreeze {N : ℕ} (S : Finset (Fin N)) (background x : Fin N → ℝ) : Fin N → ℝ :=
  fun i => if i∈S then x i else background i

theorem mixedFreeze_continuous {N : ℕ} (S : Finset (Fin N)) (background : Fin N → ℝ) :
    Continuous (mixedFreeze S background) := by
  apply continuous_pi
  intro i
  by_cases hi : i∈S
  · simpa only [mixedFreeze,hi,ite_true] using continuous_apply i
  · simp only [mixedFreeze,hi,ite_false]
    exact continuous_const

@[simp] theorem mixedFreeze_self {N : ℕ} (S : Finset (Fin N)) (x : Fin N → ℝ) : mixedFreeze S x x=x := by
  ext i
  simp [mixedFreeze]

@[simp] theorem mixedFreeze_idempotent {N : ℕ} (S : Finset (Fin N)) (background x : Fin N → ℝ) :
    mixedFreeze S background (mixedFreeze S background x)=mixedFreeze S background x := by
  ext i
  by_cases hi : i∈S <;> simp [mixedFreeze,hi]

theorem mixedFreeze_update_active {N : ℕ} (S : Finset (Fin N)) (background x : Fin N → ℝ)
    (i : Fin N) (hi : i∈S) (u : ℝ) :
    mixedFreeze S background (Function.update x i u)=Function.update (mixedFreeze S background x) i u := by
  ext k
  by_cases hk : k=i
  · subst k; simp [mixedFreeze,hi]
  · simp [mixedFreeze,hk]

theorem mixedFreeze_update_inactive {N : ℕ} (S : Finset (Fin N)) (background x : Fin N → ℝ)
    (i : Fin N) (hi : i∉S) (u : ℝ) :
    mixedFreeze S background (Function.update x i u)=mixedFreeze S background x := by
  ext k
  by_cases hk : k=i
  · subst k; simp [mixedFreeze,hi]
  · simp [mixedFreeze,hk]

theorem coordDeriv_mixedFreeze {N : ℕ} (S : Finset (Fin N)) (background x : Fin N → ℝ)
    (F : (Fin N → ℝ) → ℂ) (i : Fin N) :
    coordDeriv (fun y => F (mixedFreeze S background y)) x i=
      if i∈S then coordDeriv F (mixedFreeze S background x) i else 0 := by
  unfold coordDeriv
  by_cases hi : i∈S
  · simp only [hi,ite_true,mixedFreeze_update_active S background x i hi]
    congr 1
    simp [mixedFreeze,hi]
  · simp only [hi,ite_false,mixedFreeze_update_inactive S background x i hi]
    exact deriv_const _ _

def mixedCoordinateLie {N : ℕ} (V : ℂ → (Fin N → ℝ) → Fin N → ℂ)
    (A : ℂ → (Fin N → ℝ) → ℂ) (s : ℂ) (x : Fin N → ℝ) : ℂ :=
  deriv (fun t => A t x) s-∑ i,coordDeriv (fun y => V s y i*A s y) x i

theorem mixedCoordinateLie_eq_lie {n : ℕ}
    (V : ℂ → (Fin (n+1) → ℝ) → Fin (n+1) → ℂ)
    (A : ℂ → (Fin (n+1) → ℝ) → ℂ) (s : ℂ) (x : Fin (n+1) → ℝ)
    (h : ∀ i,DifferentiableAt ℝ (fun y => V s y i*A s y) x) :
    mixedCoordinateLie V A s x=IsingBulk.Lie.lieStep V A s x := by
  unfold mixedCoordinateLie IsingBulk.Lie.lieStep IsingBulk.Lie.divergence
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact coordDeriv_eq_fderiv _ x (h i) i

theorem mixedCoordinateLie_freeze {N : ℕ} (S : Finset (Fin N)) (background : Fin N → ℝ)
    (V : ℂ → (Fin N → ℝ) → Fin N → ℂ) (A : ℂ → (Fin N → ℝ) → ℂ)
    (hV : ∀ i,i∉S → ∀ s x,V s x i=0) (s : ℂ) (x : Fin N → ℝ) :
    mixedCoordinateLie (fun t y => V t (mixedFreeze S background y))
      (fun t y => A t (mixedFreeze S background y)) s x=
    mixedCoordinateLie V A s (mixedFreeze S background x) := by
  unfold mixedCoordinateLie
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  change coordDeriv (fun y => (fun z => V s z i*A s z) (mixedFreeze S background y)) x i=_
  rw [coordDeriv_mixedFreeze S background x (fun z => V s z i*A s z) i]
  by_cases hi : i∈S
  · simp [hi]
  · simp only [hi,ite_false]
    have he : (fun z => V s z i*A s z)=fun _ => (0:ℂ) := by
      funext z
      simp [hV i hi]
    rw [he,coordDeriv]
    simp

/-- Restriction commutes with every temperature-dependent field iterate,
not merely the first frozen-phase calculation. -/
theorem mixedCoordinateLie_iterate_freeze {N : ℕ} (S : Finset (Fin N)) (background : Fin N → ℝ)
    (V : ℂ → (Fin N → ℝ) → Fin N → ℂ) (A : ℂ → (Fin N → ℝ) → ℂ)
    (hV : ∀ i,i∉S → ∀ s x,V s x i=0) (k : ℕ) :
    (mixedCoordinateLie (fun t y => V t (mixedFreeze S background y)))^[k]
      (fun t y => A t (mixedFreeze S background y))=
    fun t y => ((mixedCoordinateLie V)^[k] A) t (mixedFreeze S background y) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply',ih]
    funext s x
    rw [mixedCoordinateLie_freeze S background V _ hV,Function.iterate_succ_apply']

theorem mixed_velocity_active_support {N : ℕ} (J : Finset (Fin N)) (j q : Fin N)
    (f : SelectorFunctions) (r τ lam : ℝ) (hj : j∈J) :
    ∀ i,i∉insert q J → ∀ s x,mixedContourVelocity J j q f r τ lam s x i=0 := by
  intro i hi s x
  exact mixedContourVelocity_zero J j q i f r τ lam s x hj
    (fun h => hi (Finset.mem_insert_of_mem h))
    (fun h => hi (by simp [h]))

theorem mixedFreeze_data {N : ℕ} (S : Finset (Fin N)) (background x : Fin N → ℝ)
    (g : ℝ → ℝ) (hg : ∀ i∈S,g (x i)=g (background i)) :
    (fun i => g (mixedFreeze S background x i))=fun i => g (background i) := by
  funext i
  by_cases hi : i∈S
  · simpa [mixedFreeze,hi] using hg i hi
  · simp [mixedFreeze,hi]

theorem mixedFreeze_contour_identity {N : ℕ} (S : Finset (Fin N)) (background x : Fin N → ℝ)
    (f : SelectorFunctions) (r τ lam : ℝ)
    (hp : ∀ i∈S,f.p (x i)=f.p (background i))
    (hm : ∀ i∈S,f.m (x i)=f.m (background i)) (i : Fin N) :
    deformedPoint f r τ lam (mixedFreeze S background x) i =
      deformedPoint f r τ lam background i*
        Complex.exp (Complex.I*((mixedFreeze S background x i:ℂ)-(background i:ℂ))) := by
  have ep := mixedFreeze_data S background x f.p hp
  have em := mixedFreeze_data S background x f.m hm
  unfold deformedPoint
  rw [ep,em,mul_assoc,← Complex.exp_add]
  congr 2
  ring

theorem mixedFreeze_jacobian_identity {N : ℕ} (S : Finset (Fin N)) (background x : Fin N → ℝ)
    (f : SelectorFunctions) (τ lam : ℝ)
    (hp : ∀ i∈S,f.p (x i)=f.p (background i))
    (hm : ∀ i∈S,f.m (x i)=f.m (background i))
    (hp' : ∀ i∈S,deriv f.p (x i)=deriv f.p (background i))
    (hm' : ∀ i∈S,deriv f.m (x i)=deriv f.m (background i)) :
    angularJacobian f τ lam (mixedFreeze S background x)=angularJacobian f τ lam background := by
  unfold angularJacobian
  rw [mixedFreeze_data S background x f.p hp,mixedFreeze_data S background x f.m hm,
    mixedFreeze_data S background x (deriv f.p) hp',mixedFreeze_data S background x (deriv f.m) hm']

theorem mixed_plateau_data_eventually {N : ℕ} (S : Finset (Fin N)) (background : Fin N → ℝ)
    (g : ℝ → ℝ) (hg : ∀ i∈S,g =ᶠ[𝓝 (background i)] fun _ => g (background i)) :
    ∀ᶠ x in 𝓝 background,∀ i∈S,g (x i)=g (background i) ∧
      deriv g (x i)=deriv g (background i) := by
  apply (Filter.eventually_all_finset S).mpr
  intro i hi
  have hd : deriv g =ᶠ[𝓝 (background i)] fun _ => deriv g (background i) := by
    have he := (hg i hi).deriv
    have hz := (hg i hi).deriv_eq
    filter_upwards [he] with x hx
    rw [hz]
    simpa only [deriv_const] using hx
  exact ((continuous_apply i).continuousAt.tendsto.eventually ((hg i hi).and hd))

/-- All spectator-dependent occupancy and every matrix entry are retained;
they are constant only on the proved active plateau germ. -/
theorem mixed_active_contour_germ {N : ℕ} (S : Finset (Fin N)) (background : Fin N → ℝ)
    (f : SelectorFunctions) (r τ lam : ℝ)
    (hp : ∀ i∈S,f.p =ᶠ[𝓝 (background i)] fun _ => f.p (background i))
    (hm : ∀ i∈S,f.m =ᶠ[𝓝 (background i)] fun _ => f.m (background i)) :
    ∀ᶠ x in 𝓝 background,
      angularJacobian f τ lam (mixedFreeze S background x)=angularJacobian f τ lam background ∧
      ∀ i,deformedPoint f r τ lam (mixedFreeze S background x) i=
        deformedPoint f r τ lam background i*
          Complex.exp (Complex.I*((mixedFreeze S background x i:ℂ)-(background i:ℂ))) := by
  filter_upwards [mixed_plateau_data_eventually S background f.p hp,
    mixed_plateau_data_eventually S background f.m hm] with x hxp hxm
  exact ⟨mixedFreeze_jacobian_identity S background x f τ lam
    (fun i hi => (hxp i hi).1) (fun i hi => (hxm i hi).1)
    (fun i hi => (hxp i hi).2) (fun i hi => (hxm i hi).2),
    mixedFreeze_contour_identity S background x f r τ lam
      (fun i hi => (hxp i hi).1) (fun i hi => (hxm i hi).1)⟩

theorem constructed_branch_plateau_germ {b η α θ : ℝ}
    (hb : 0<Real.sin b) (hη : 0<η) (hηsmall : η≤Real.sin b/4) (hα : 0<α)
    (hcore : lowerChord b θ<η^2) :
    (constructedSelector b η α).p =ᶠ[𝓝 θ] (fun _ => 0) ∧
    (constructedSelector b η α).m =ᶠ[𝓝 θ] (fun _ => 1) := by
  have hc : ContinuousAt (lowerChord b) θ := by unfold lowerChord; fun_prop
  have he := hc.eventually (Iio_mem_nhds hcore)
  constructor
  · filter_upwards [he] with t ht
    exact (constructed_lower_core_plateau hb hη hηsmall hα ht.le).2
  · filter_upwards [he] with t ht
    exact (constructed_lower_core_plateau hb hη hηsmall hα ht.le).1

theorem constructed_upper_plateau_germ {b η α θ : ℝ}
    (hb : 0<Real.sin b) (hη : 0<η) (hηsmall : η≤Real.sin b/4) (hα : 0<α)
    (hsin : α≤Real.sin θ) :
    (constructedSelector b η α).p =ᶠ[𝓝 θ] (fun _ => 1) ∧
    (constructedSelector b η α).m =ᶠ[𝓝 θ] (fun _ => 0) := by
  have he : ∀ᶠ t in 𝓝 θ,3*α/4<Real.sin t :=
    Real.continuous_sin.continuousAt.eventually (Ioi_mem_nhds (by linarith))
  constructor
  · filter_upwards [he] with t ht
    exact thresholdStep_one (by linarith) ht.le
  · filter_upwards [he] with t ht
    exact lowerM_zero_of_nonneg_sine b η t hb hη hηsmall (by linarith)

theorem constructed_current_named_plateau_germ {N : ℕ} (b η α : ℝ)
    (hb : 0<Real.sin b) (hη : 0<η) (hηsmall : η≤Real.sin b/4) (hα : 0<α)
    (q : Fin N) {θ : Fin N → ℝ}
    (hθ : θ∈tsupport (namedSelectorDerivative (constructedSelector b η α) q)) :
    (constructedSelector b η α).p =ᶠ[𝓝 (θ q)] (fun _ => 1) ∧
    (constructedSelector b η α).m =ᶠ[𝓝 (θ q)] (fun _ => 0) :=
  constructed_upper_plateau_germ hb hη hηsmall hα
    (constructed_current_support_geometry b η α hb hη hηsmall hα q hθ).2.2.1

theorem mixedCoordinateLie_congr_germ {N : ℕ}
    (V W : ℂ → (Fin N → ℝ) → Fin N → ℂ) (A B : ℂ → (Fin N → ℝ) → ℂ)
    (s : ℂ) (x : Fin N → ℝ)
    (hV : Function.uncurry V =ᶠ[𝓝 (s,x)] Function.uncurry W)
    (hA : Function.uncurry A =ᶠ[𝓝 (s,x)] Function.uncurry B) :
    mixedCoordinateLie V A s x=mixedCoordinateLie W B s x := by
  have hp : (fun t => A t x)=ᶠ[𝓝 s] (fun t => B t x) :=
    hA.comp_tendsto (continuousAt_id.prodMk continuousAt_const).tendsto
  unfold mixedCoordinateLie
  rw [hp.deriv_eq]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have hf : (fun p : ℂ × (Fin N → ℝ) => V p.1 p.2 i*A p.1 p.2)=ᶠ[𝓝 (s,x)]
      (fun p => W p.1 p.2 i*B p.1 p.2) := by
    filter_upwards [hV,hA] with p hv ha
    simp only [Function.uncurry] at hv ha
    rw [hv,ha]
  have ht : Filter.Tendsto (fun u : ℝ => (s,Function.update x i u)) (𝓝 (x i)) (𝓝 (s,x)) := by
    simpa only [Function.update_eq_self] using
      (continuousAt_const.prodMk (hasDerivAt_update x i (x i)).continuousAt).tendsto
  exact (hf.comp_tendsto ht).deriv_eq

theorem mixedCoordinateLie_eventuallyEq {N : ℕ}
    (V W : ℂ → (Fin N → ℝ) → Fin N → ℂ) (A B : ℂ → (Fin N → ℝ) → ℂ)
    (s : ℂ) (x : Fin N → ℝ)
    (hV : Function.uncurry V =ᶠ[𝓝 (s,x)] Function.uncurry W)
    (hA : Function.uncurry A =ᶠ[𝓝 (s,x)] Function.uncurry B) :
    Function.uncurry (mixedCoordinateLie V A)=ᶠ[𝓝 (s,x)]
      Function.uncurry (mixedCoordinateLie W B) := by
  filter_upwards [hV.eventuallyEq_nhds,hA.eventuallyEq_nhds] with p hv ha
  exact mixedCoordinateLie_congr_germ V W A B p.1 p.2 hv ha

theorem mixedCoordinateLie_iterate_eventuallyEq {N : ℕ}
    (V W : ℂ → (Fin N → ℝ) → Fin N → ℂ) (A B : ℂ → (Fin N → ℝ) → ℂ)
    (s : ℂ) (x : Fin N → ℝ)
    (hV : Function.uncurry V =ᶠ[𝓝 (s,x)] Function.uncurry W)
    (hA : Function.uncurry A =ᶠ[𝓝 (s,x)] Function.uncurry B) (k : ℕ) :
    Function.uncurry ((mixedCoordinateLie V)^[k] A)=ᶠ[𝓝 (s,x)]
      Function.uncurry ((mixedCoordinateLie W)^[k] B) := by
  induction k with
  | zero => exact hA
  | succ k ih =>
    simpa only [Function.iterate_succ_apply'] using
      mixedCoordinateLie_eventuallyEq V W _ _ s x hV ih

/-- Arbitrary changes away from the active slice do not affect any finite
Lie iterate at its center. Both fields may vary with temperature. -/
theorem mixedCoordinateLie_iterate_active_germ {N : ℕ} (S : Finset (Fin N))
    (V W : ℂ → (Fin N → ℝ) → Fin N → ℂ) (A B : ℂ → (Fin N → ℝ) → ℂ)
    (s : ℂ) (x : Fin N → ℝ)
    (hsV : ∀ i,i∉S → ∀ t y,V t y i=0) (hsW : ∀ i,i∉S → ∀ t y,W t y i=0)
    (hV : (fun p : ℂ × (Fin N → ℝ) => V p.1 (mixedFreeze S x p.2))=ᶠ[𝓝 (s,x)]
      (fun p => W p.1 (mixedFreeze S x p.2)))
    (hA : (fun p : ℂ × (Fin N → ℝ) => A p.1 (mixedFreeze S x p.2))=ᶠ[𝓝 (s,x)]
      (fun p => B p.1 (mixedFreeze S x p.2))) (k : ℕ) :
    ((mixedCoordinateLie V)^[k] A) s x=((mixedCoordinateLie W)^[k] B) s x := by
  have he := (mixedCoordinateLie_iterate_eventuallyEq
    (fun t y => V t (mixedFreeze S x y)) (fun t y => W t (mixedFreeze S x y))
    (fun t y => A t (mixedFreeze S x y)) (fun t y => B t (mixedFreeze S x y)) s x hV hA k).eq_of_nhds
  simpa only [Function.uncurry,mixedCoordinateLie_iterate_freeze S x V A hsV k,
    mixedCoordinateLie_iterate_freeze S x W B hsW k,mixedFreeze_self] using he

end
end IsingBulk.Tail
