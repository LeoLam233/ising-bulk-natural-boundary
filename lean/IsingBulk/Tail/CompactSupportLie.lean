import IsingBulk.Analysis.LieIntegration
import IsingBulk.First.CompactParameterIntegral
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.FDeriv.Const

/-! Compactly supported real Lie transport: zero divergence is proved by
integration by parts, and complex parameter differentiation is derived on
a fixed compact support before iteration. No flux or integral identity is
assumed. Source chart regularity is an explicit downstream obligation. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Lie MeasureTheory Set Filter Function
open scoped Topology ContDiff BigOperators

 theorem compact_fderiv_integral_zero {n : ℕ} (f : AngularSpace n → ℂ)
    (hf : ContDiff ℝ 1 f) (hs : HasCompactSupport f) (v : AngularSpace n) :
    (∫ x, fderiv ℝ f x v)=0 := by
  have hd : Continuous (fun x => fderiv ℝ f x v) :=
    (hf.continuous_fderiv_apply (by norm_num)).comp (continuous_id.prodMk continuous_const)
  have hi : Integrable (fun x => fderiv ℝ f x v) :=
    hd.integrable_of_hasCompactSupport (hs.fderiv_apply ℝ v)
  have hfi : Integrable f := hf.continuous.integrable_of_hasCompactSupport hs
  have hh := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := volume) (v := v) (f := fun _ : AngularSpace n => (1:ℂ)) (g := f)
    (by simp)
    (by simpa using hi) (by simpa using hfi)
    (fun x _ => differentiableAt_const _) (fun x _ => hf.differentiable (by norm_num) x)
  simpa using hh

 theorem compact_divergence_integrable_zero {n : ℕ}
    (F : AngularSpace n → Fin (n+1) → ℂ)
    (hF : ∀ i, ContDiff ℝ 1 (fun x => F x i))
    (hc : ∀ i, HasCompactSupport (fun x => F x i)) :
    Integrable (divergence F) ∧ (∫ x, divergence F x)=0 := by
  have hi (i : Fin (n+1)) : Integrable (fun x =>
      fderiv ℝ (fun y => F y i) x (Pi.single i 1)) :=
    (((hF i).continuous_fderiv_apply (by norm_num)).comp
      (continuous_id.prodMk continuous_const)).integrable_of_hasCompactSupport
        ((hc i).fderiv_apply ℝ (Pi.single i 1))
  constructor
  · exact integrable_finsetSum _ (fun i _ => hi i)
  · simp only [IsingBulk.Lie.divergence]
    rw [integral_finsetSum _ (fun i _ => hi i)]
    simp only [compact_fderiv_integral_zero _ (hF _) (hc _),Finset.sum_const_zero]

 theorem parameter_derivative_support {X : Type*} (A : ℂ → X → ℂ)
    {U : Set ℂ} (hU : IsOpen U) {K : Set X}
    (hsupp : ∀ s ∈ U, support (A s) ⊆ K) {s : ℂ} (hs : s ∈ U) :
    support (fun x => deriv (fun t => A t x) s) ⊆ K := by
  intro x hx
  by_contra hxK
  have heq : (fun t => A t x) =ᶠ[𝓝 s] (fun _ => 0) := by
    filter_upwards [hU.mem_nhds hs] with t ht
    by_contra hn
    exact hxK (hsupp t ht hn)
  have hz := heq.deriv_eq
  exact (show deriv (fun t => A t x) s ≠ 0 from hx) (by simpa only [deriv_const] using hz)

 theorem integral_eq_compact_support {n : ℕ} {K : Set (AngularSpace n)}
    (_hK : IsCompact K) (f : AngularSpace n → ℂ) (hf : support f ⊆ K) :
    (∫ x, f x) = ∫ x in K, f x := by
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun x hx => notMem_support.mp (fun h => hx (hf h)))).symm

 theorem compact_support_lie_step {n : ℕ} {K : Set (AngularSpace n)} (hK : IsCompact K)
    {U : Set ℂ} (hU : IsOpen U)
    (V : ℂ → AngularSpace n → Fin (n+1) → ℂ) (A : ℂ → AngularSpace n → ℂ)
    (hsupp : ∀ s ∈ U, support (A s) ⊆ K)
    (hc : ContinuousOn (fun p : ℂ × AngularSpace n => A p.1 p.2) (U ×ˢ K))
    (hdc : ContinuousOn (fun p : ℂ × AngularSpace n => deriv (fun t => A t p.2) p.1) (U ×ˢ K))
    (hd : ∀ s ∈ U, ∀ x ∈ K, DifferentiableAt ℂ (fun t => A t x) s)
    (hflux : ∀ s ∈ U, ∀ i, ContDiff ℝ 1 (fun x => V s x i*A s x))
    {s : ℂ} (hs : s ∈ U) :
    HasDerivAt (fun t => ∫ x, A t x) (∫ x, lieStep V A s x) s := by
  have hder := IsingBulk.First.hasDerivAt_compact_integral (μ := volume) hK (hU.mem_nhds hs)
    A (fun s x => deriv (fun t => A t x) s) hc hdc
    (fun t ht x hx => (hd t ht x hx).hasDerivAt)
  have hparam := parameter_derivative_support A hU hsupp hs
  have hderInt : Integrable (fun x => deriv (fun t => A t x) s) := by
    have hcont : ContinuousOn (fun x => deriv (fun t => A t x) s) K :=
      hdc.comp (continuous_const.prodMk continuous_id).continuousOn (fun x hx => ⟨hs,hx⟩)
    have hi : IntegrableOn (fun x => deriv (fun t => A t x) s) K :=
      hcont.integrableOn_compact hK
    exact (integrableOn_iff_integrable_of_support_subset hparam).mp hi
  have hfluxSupport (i : Fin (n+1)) : HasCompactSupport (fun x => V s x i*A s x) := by
    apply hK.of_isClosed_subset isClosed_closure
    apply closure_minimal _ hK.isClosed
    intro x hx
    exact hsupp s hs ((mul_ne_zero_iff.mp hx).2)
  obtain ⟨hdivi,hdivzero⟩ := compact_divergence_integrable_zero
    (fun x i => V s x i*A s x) (hflux s hs) hfluxSupport
  have heq : (fun t => ∫ x, A t x) =ᶠ[𝓝 s] (fun t => ∫ x in K, A t x) := by
    filter_upwards [hU.mem_nhds hs] with t ht
    exact integral_eq_compact_support hK _ (hsupp t ht)
  have hvalue : (∫ x, lieStep V A s x) = ∫ x in K, deriv (fun t => A t x) s := by
    simp only [IsingBulk.Lie.lieStep]
    rw [integral_sub hderInt hdivi,hdivzero,sub_zero]
    exact integral_eq_compact_support hK _ hparam
  rw [hvalue]
  exact hder.congr_of_eventuallyEq heq


 theorem compact_support_iterate_lieStep_integral_on {n : ℕ}
    {K : Set (AngularSpace n)} (hK : IsCompact K) {U : Set ℂ} (hU : IsOpen U)
    (V : ℂ → AngularSpace n → Fin (n+1) → ℂ) (A : ℂ → AngularSpace n → ℂ) (j : ℕ)
    (hsupp : ∀ k < j, ∀ s ∈ U, support (((lieStep V)^[k] A) s) ⊆ K)
    (hc : ∀ k < j, ContinuousOn
      (fun p : ℂ × AngularSpace n => ((lieStep V)^[k] A) p.1 p.2) (U ×ˢ K))
    (hdc : ∀ k < j, ContinuousOn (fun p : ℂ × AngularSpace n =>
      deriv (fun t => ((lieStep V)^[k] A) t p.2) p.1) (U ×ˢ K))
    (hd : ∀ k < j, ∀ s ∈ U, ∀ x ∈ K,
      DifferentiableAt ℂ (fun t => ((lieStep V)^[k] A) t x) s)
    (hflux : ∀ k < j, ∀ s ∈ U, ∀ i,
      ContDiff ℝ 1 (fun x => V s x i*((lieStep V)^[k] A) s x)) :
    EqOn (fun s => ∫ x, ((lieStep V)^[j] A) s x)
      (deriv^[j] (fun s => ∫ x, A s x)) U := by
  induction j with
  | zero => intro s hs; rfl
  | succ j ih =>
    have hprev := ih (fun k hk => hsupp k (by omega))
      (fun k hk => hc k (by omega)) (fun k hk => hdc k (by omega))
      (fun k hk => hd k (by omega)) (fun k hk => hflux k (by omega))
    intro s hs
    rw [Function.iterate_succ_apply',Function.iterate_succ_apply']
    calc
      _ = deriv (fun t => ∫ x, ((lieStep V)^[j] A) t x) s :=
        (compact_support_lie_step hK hU V _ (hsupp j (by omega))
          (hc j (by omega)) (hdc j (by omega)) (hd j (by omega))
          (hflux j (by omega)) hs).deriv.symm
      _ = _ := (hprev.eventuallyEq_of_mem (hU.mem_nhds hs)).deriv_eq



/-- Only the fixed cutoff's closed support needs chart regularity. Singular
or discontinuous totalized formulas outside that support cause no issue. -/
theorem weighted_contDiff_of_tsupport {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (w : E → ℝ) (F : E → ℂ) (hw : ContDiff ℝ ∞ w)
    (hF : ∀ x ∈ tsupport w, ContDiffAt ℝ ∞ F x) :
    ContDiff ℝ ∞ (fun x => (w x:ℂ)*F x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport w
  · exact (Complex.ofRealCLM.contDiff.contDiffAt.comp x hw.contDiffAt).mul (hF x hx)
  · have hz := notMem_tsupport_iff_eventuallyEq.mp hx
    have he : (fun y => (w y:ℂ)*F y) =ᶠ[𝓝 x] (fun _ => (0:ℂ)) := by
      filter_upwards [hz] with y hy
      simp [hy]
    exact contDiffAt_const.congr_of_eventuallyEq he

theorem weighted_tsupport_subset {E : Type*} [TopologicalSpace E]
    (w : E → ℝ) (F : E → ℂ) :
    tsupport (fun x => (w x:ℂ)*F x) ⊆ tsupport w := by
  apply closure_mono
  intro x hx
  have hw := (mul_ne_zero_iff.mp hx).1
  exact fun hz => hw (by simp [hz])


end
end IsingBulk.Tail
