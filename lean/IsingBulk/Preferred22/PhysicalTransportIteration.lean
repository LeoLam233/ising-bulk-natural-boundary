import IsingBulk.Preferred22.PhysicalTransport
import IsingBulk.Preferred22.PhysicalDensityDomain
import IsingBulk.Preferred22.PhysicalDensityShell

/-! Exact all-order identification of the literal physical descendants.
The analytic regularity input concerns the actual recursively defined
physical functions; no coefficient estimate or tail envelope is assumed. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

/-- The unchanged physical resolvent never vanishes on the actual upper
physical branch. Both numerator and denominator follow from |Z|<1. -/
theorem preferredSourceResolvent_ne_zero {N : ℕ} (hN : 0<N)
    (τ : ℝ) (p m : ℝ → ℝ) (s : ℂ) (θ : Fin N → ℝ)
    (hW : ∀ i, 0<(temperatureTrace s-Complex.cos (deformedAngles τ p m θ i)).im) :
    preferredSourceResolvent τ p m s θ≠0 := by
  have hZ := preferredSourceProductPhase_norm_lt_one hN τ p m s θ hW
  have hn : 1+preferredSourceProductPhase τ p m s θ≠0 := by
    intro he
    have hz : preferredSourceProductPhase τ p m s θ=(-1:ℂ) := by linear_combination he
    rw [hz,norm_neg,norm_one] at hZ
    exact (lt_irrefl 1) hZ
  have hd : 1-preferredSourceProductPhase τ p m s θ≠0 := by
    intro he
    have hz : preferredSourceProductPhase τ p m s θ=1 := (sub_eq_zero.mp he).symm
    rw [hz,norm_one] at hZ
    exact (lt_irrefl 1) hZ
  exact div_ne_zero hn hd

theorem preferredCoordinateJacobian_ne_zero {N : ℕ} (τ δ : ℝ) (p m : ℝ → ℝ)
    (hp : Differentiable ℝ p) (hm : Differentiable ℝ m) (s : ℂ) (θ : Fin N → ℝ)
    (hδ : 0<δ) (hδπ : δ<Real.pi/2) (hS : 0<(temperatureTrace s).re)
    (hSδ : (temperatureTrace s).re<2*Real.cos δ)
    (hθ : ∀ i, θ i∈Set.Icc (-Real.pi-δ) δ)
    (hW : ∀ i, 0<(temperatureTrace s-Complex.cos (deformedAngles τ p m θ i)).im)
    (hM : (preferredContourMatrix τ p m θ).det≠0) :
    preferredCoordinateJacobian τ p m s θ≠0 := by
  rw [← preferredSourceJacobian_det τ δ p m hp hm s θ hδ hδπ hS hSδ hθ hW]
  exact preferredSourceJacobian_det_ne_zero τ δ p m hp hm s θ hδ hδπ hS hSδ hθ hW hM

/-- Literal physical transport respects an open-domain equality of actual
source densities. This uses true complex and real derivative germs. -/
theorem preferredTransportStep_congr_open {N : ℕ}
    (V : ℂ → (Fin N → ℝ) → Fin N → ℂ)
    (A G : ℂ → (Fin N → ℝ) → ℂ) (Ω : Set (ℂ × (Fin N → ℝ)))
    (hΩ : IsOpen Ω) (hEq : ∀ z∈Ω, A z.1 z.2=G z.1 z.2)
    (s : ℂ) (θ : Fin N → ℝ) (hz : (s,θ)∈Ω) :
    preferredTransportStep V A s θ=preferredTransportStep V G s θ := by
  have he : (fun z : ℂ × (Fin N → ℝ) => A z.1 z.2)=ᶠ[𝓝 (s,θ)] (fun z => G z.1 z.2) := by
    filter_upwards [hΩ.mem_nhds hz] with z hz
    exact hEq z hz
  have hs : deriv (fun t : ℂ => A t θ) s=deriv (fun t : ℂ => G t θ) s :=
    (he.comp_tendsto ((show Continuous (fun t : ℂ => (t,θ)) by fun_prop).tendsto s)).deriv_eq
  have hx (i : Fin N) :
      deriv (fun x : ℝ => V s (Function.update θ i x) i*A s (Function.update θ i x)) (θ i)=
      deriv (fun x : ℝ => V s (Function.update θ i x) i*G s (Function.update θ i x)) (θ i) := by
    have hh : Continuous (fun x : ℝ => (s,Function.update θ i x)) := by fun_prop
    have ht : Filter.Tendsto (fun x : ℝ => (s,Function.update θ i x)) (𝓝 (θ i)) (𝓝 (s,θ)) := by
      simpa only [Function.update_eq_self] using hh.tendsto (θ i)
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [he.comp_tendsto ht] with x hx
    exact congrArg (fun z : ℂ => V s (Function.update θ i x) i*z) hx
  unfold preferredTransportStep preferredAngularDivergence
  rw [hs]
  simp_rw [hx]

/-- All-order physical/regular identification, from actual physical mixed
regularity on an open source domain. The induction derives regular-scalar
differentiability by division by the nonzero actual JH factor. It does not
assume differentiability separately for generated regular descendants. -/
theorem preferredTransportedDensity_factorization_of_mixed {N : ℕ} (hN : 0<N)
    (τ δ : ℝ) (η p m r : ℝ → ℝ) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (hδ : 0<δ) (hδπ : δ<Real.pi/2)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hreg : ∀ z∈Ω, PreferredSourceRegime τ δ p m z)
    (D : Set ℂ) (c : ℝ) (hc : 0<c) (hD : Convex ℝ D)
    (hU : ∀ z∈Ω, ∀ q∈D, AnalyticAt ℂ (fun x : ℂ × ℂ => preferredMovingInverse x.1 x.2) (z.1,q))
    (hcurv : ∀ z∈Ω, ∀ q∈D, c≤(deriv (preferredSourceUQ z.1) q).re)
    (hq : ∀ z∈Ω, ∀ i, preferredSourceCoordinate τ p m z.1 z.2 i∈D)
    (hR : ∀ z∈Ω, collectiveDenominator (fun i => preferredMovingInverse z.1
      (preferredSourceCoordinate τ p m z.1 z.2 i))≠0)
    (hM : ∀ z∈Ω, (preferredContourMatrix τ p m z.2).det≠0)
    (hP : ∀ j, PreferredMixedSmoothOn
      (fun z => preferredTransportedDensity .right τ η p m r j z.1 z.2) Ω) :
    ∀ j, ∀ z∈Ω, preferredTransportedDensity .right τ η p m r j z.1 z.2=
      preferredCoordinateJacobian τ p m z.1 z.2*preferredSourceResolvent τ p m z.1 z.2*
        preferredRegularTransportedScalar τ η p m r j z.1 z.2 := by
  have hp' := hp.differentiable (by simp)
  have hm' := hm.differentiable (by simp)
  have hnonzero (z : ℂ × (Fin N → ℝ)) (hz : z∈Ω) :
      preferredCoordinateJacobian τ p m z.1 z.2*preferredSourceResolvent τ p m z.1 z.2≠0 := by
    obtain ⟨hzS,_,hzSδ,hzθ,hzW⟩ := hreg z hz
    exact mul_ne_zero
      (preferredCoordinateJacobian_ne_zero τ δ p m hp' hm' z.1 z.2 hδ hδπ hzS hzSδ
        (fun i => ⟨(hzθ i).1.le,(hzθ i).2.le⟩) hzW (hM z hz))
      (preferredSourceResolvent_ne_zero hN τ p m z.1 z.2 hzW)
  intro j
  induction j with
  | zero =>
    intro z hz
    obtain ⟨hzS,_,hzSδ,hzθ,hzW⟩ := hreg z hz
    exact preferredPhysicalSeed_factorized τ δ η p m r z.1 z.2 hδ hδπ hzS hzSδ
      (fun i => ⟨(hzθ i).1.le,(hzθ i).2.le⟩) hzW
  | succ j ih =>
    rintro ⟨s,θ⟩ hz
    obtain ⟨hS,hSi,hSδ,hθo,hW⟩ := hreg (s,θ) hz
    have hθ (i : Fin N) : θ i∈Set.Icc (-Real.pi-δ) δ := ⟨(hθo i).1.le,(hθo i).2.le⟩
    have hv (i : Fin N) : preferredSourceUQ s (preferredSourceCoordinate τ p m s θ i)≠0 := by
      have hwre : (deformedAngles τ p m θ i).re=θ i := by simp [deformedAngles,Complex.mul_re]
      exact (preferred_global_one_sided_q_regular s (deformedAngles τ p m θ i) δ hδ hδπ hS hSδ
        (by rw [hwre]; exact (hθ i).1) (by rw [hwre]; exact (hθ i).2) (hW i)).2
    have hJa := preferredCoordinateJacobian_parameter_analyticAt τ p m s θ hSi hW
      (fun i => hU (s,θ) hz _ (hq (s,θ) hz i)) hv
    have hHa := preferredSourceResolvent_parameter_analyticAt hN τ p m s θ hSi hW
    have hJc := preferredCoordinateJacobian_contDiffAt τ p m hp hm s θ hSi hW
      (fun i => hU (s,θ) hz _ (hq (s,θ) hz i)) hv
    have hHc := preferredSourceResolvent_contDiffAt hN τ p m hp hm s θ hSi hW
    let Q := fun z : ℂ × (Fin N → ℝ) => preferredTransportedDensity .right τ η p m r j z.1 z.2 /
      (preferredCoordinateJacobian τ p m z.1 z.2*preferredSourceResolvent τ p m z.1 z.2)
    have hQc : ContDiffAt ℝ ∞ Q (s,θ) := by
      simp only [Q,div_eq_mul_inv]
      convert! ((hP j (s,θ) hz).1).mul ((hJc.mul hHc).inv (hnonzero (s,θ) hz)) using 1
    have hQa : DifferentiableAt ℂ (fun t => Q (t,θ)) s :=
      ((hP j (s,θ) hz).2).div (hJa.differentiableAt.mul hHa.differentiableAt) (hnonzero (s,θ) hz)
    have he : (fun z : ℂ × (Fin N → ℝ) => preferredRegularTransportedScalar τ η p m r j z.1 z.2)
        =ᶠ[𝓝 (s,θ)] Q := by
      filter_upwards [hΩ.mem_nhds hz] with z hzz
      apply (eq_div_iff (hnonzero z hzz)).mpr
      calc
        _ = preferredCoordinateJacobian τ p m z.1 z.2*preferredSourceResolvent τ p m z.1 z.2*
          preferredRegularTransportedScalar τ η p m r j z.1 z.2 := by ring
        _ = _ := (ih z hzz).symm
    have hGs : DifferentiableAt ℂ (fun t => preferredRegularTransportedScalar τ η p m r j t θ) s :=
      hQa.congr_of_eventuallyEq
        (he.comp_tendsto ((show Continuous (fun t : ℂ => (t,θ)) by fun_prop).tendsto s))
    have hGθ (i : Fin N) : DifferentiableAt ℝ
        (fun x => preferredRegularTransportedScalar τ η p m r j s (Function.update θ i x)) (θ i) := by
      have hmap : Continuous (fun x : ℝ => (s,Function.update θ i x)) := by fun_prop
      have ht : Filter.Tendsto (fun x : ℝ => (s,Function.update θ i x)) (𝓝 (θ i)) (𝓝 (s,θ)) := by
        simpa only [Function.update_eq_self] using hmap.tendsto (θ i)
      have hd := (hQc.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq (θ i)
        ((hasDerivAt_const (θ i) s).prodMk (hasDerivAt_update θ i (θ i)))
        (by simp only [Function.update_eq_self])
      exact hd.differentiableAt.congr_of_eventuallyEq (he.comp_tendsto ht)
    change preferredTransportStep (preferredSourceAngularField .right τ p m)
      (preferredTransportedDensity .right τ η p m r j) s θ=_
    rw [preferredTransportStep_congr_open (preferredSourceAngularField .right τ p m)
      (preferredTransportedDensity .right τ η p m r j)
      (fun t x => preferredCoordinateJacobian τ p m t x*preferredSourceResolvent τ p m t x*
        preferredRegularTransportedScalar τ η p m r j t x) Ω hΩ ih s θ hz]
    exact preferred_physical_transport_factorization hN τ δ p m hp hm s θ hδ hδπ
      ⟨hS,hSi,hSδ,hθo,hW⟩ D c hc hD (hU (s,θ) hz) (hcurv (s,θ) hz) (hq (s,θ) hz)
      (hR (s,θ) hz) (hM (s,θ) hz) _ hGs hGθ


/-- Exact all-order physical factorization with physical descendant
regularity fully discharged. Only the literal source geometry and smooth
real cutoff data remain as inputs. -/
theorem preferredTransportedDensity_factorization {N : ℕ} (hN : 0<N)
    (τ δ : ℝ) (η p m r : ℝ → ℝ) (hη : ContDiff ℝ ∞ η) (hp : ContDiff ℝ ∞ p)
    (hm : ContDiff ℝ ∞ m) (hr : ContDiff ℝ ∞ r)
    (hδ : 0<δ) (hδπ : δ<Real.pi/2)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hreg : ∀ z∈Ω, PreferredSourceRegime τ δ p m z)
    (D : Set ℂ) (c : ℝ) (hc : 0<c) (hD : Convex ℝ D)
    (hU : ∀ z∈Ω, ∀ q∈D, AnalyticAt ℂ (fun x : ℂ × ℂ => preferredMovingInverse x.1 x.2) (z.1,q))
    (hcurv : ∀ z∈Ω, ∀ q∈D, c≤(deriv (preferredSourceUQ z.1) q).re)
    (hq : ∀ z∈Ω, ∀ i, preferredSourceCoordinate τ p m z.1 z.2 i∈D)
    (hR : ∀ z∈Ω, collectiveDenominator (fun i => preferredMovingInverse z.1
      (preferredSourceCoordinate τ p m z.1 z.2 i))≠0)
    (hM : ∀ z∈Ω, (preferredContourMatrix τ p m z.2).det≠0) :
    ∀ j, ∀ z∈Ω, preferredTransportedDensity .right τ η p m r j z.1 z.2=
      preferredCoordinateJacobian τ p m z.1 z.2*preferredSourceResolvent τ p m z.1 z.2*
        preferredRegularTransportedScalar τ η p m r j z.1 z.2 := by
  apply preferredTransportedDensity_factorization_of_mixed hN τ δ η p m r hp hm hδ hδπ
    Ω hΩ hreg D c hc hD hU hcurv hq hR hM
  intro j z hz
  obtain ⟨_,hSi,_,_,hW⟩ := hreg z hz
  exact preferredTransportedDensity_regular_at_of_curvature hN τ η p m r hη hp hm hr
    z.1 z.2 hSi hW D c hc hD (hU z hz) (hcurv z hz) (hq z hz) (hR z hz) (hM z hz) j

/-- A genuine open coordinate transport domain in a proved common inverse
tube. Full-equality collisions are explicitly excluded by the actual R. -/
def preferredTransportDomain {N : ℕ} (τ δ : ℝ) (p m : ℝ → ℝ)
    (s₀ : ℂ) (ρ : ℝ) (D : Set ℂ) : Set (ℂ × (Fin N → ℝ)) :=
  {z | PreferredSourceRegime τ δ p m z ∧ ‖z.1-s₀‖<ρ ∧
    (∀ i, preferredSourceCoordinate τ p m z.1 z.2 i∈interior D) ∧
    collectiveDenominator (fun i => preferredMovingInverse z.1
      (preferredSourceCoordinate τ p m z.1 z.2 i))≠0 ∧
    (preferredContourMatrix τ p m z.2).det≠0}

theorem preferredTransportDomain_isOpen {N : ℕ} (τ δ : ℝ) (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m) (s₀ : ℂ) (ρ : ℝ) (D : Set ℂ)
    (hU : ∀ s, ‖s-s₀‖<ρ → ∀ q∈D,
      AnalyticAt ℂ (fun x : ℂ × ℂ => preferredMovingInverse x.1 x.2) (s,q)) :
    IsOpen (preferredTransportDomain (N := N) τ δ p m s₀ ρ D) := by
  apply isOpen_iff_mem_nhds.mpr
  intro z hz
  obtain ⟨hreg,hs,hq,hR,hM⟩ := hz
  have hχ := (preferredSourceCoordinate_contDiffAt τ p m hp hm z.1 z.2 hreg.2.1 hreg.2.2.2.2).continuousAt
  have hqev : ∀ᶠ x : ℂ × (Fin N → ℝ) in 𝓝 z,
      ∀ i, preferredSourceCoordinate τ p m x.1 x.2 i∈interior D := by
    apply Filter.eventually_all.mpr
    intro i
    exact (continuousAt_pi.mp hχ i).tendsto.eventually (isOpen_interior.mem_nhds (hq i))
  have hUi (i : Fin N) : ContinuousAt (fun x : ℂ × (Fin N → ℝ) =>
      preferredMovingInverse x.1 (preferredSourceCoordinate τ p m x.1 x.2 i)) z :=
    ContinuousAt.comp (f := fun x : ℂ × (Fin N → ℝ) =>
      (x.1,preferredSourceCoordinate τ p m x.1 x.2 i))
      (g := fun x : ℂ × ℂ => preferredMovingInverse x.1 x.2)
      (hU z.1 hs _ (interior_subset (hq i))).continuousAt
      (continuousAt_fst.prodMk (continuousAt_pi.mp hχ i))
  have hRc : ContinuousAt (fun x : ℂ × (Fin N → ℝ) => collectiveDenominator
      (fun i => preferredMovingInverse x.1 (preferredSourceCoordinate τ p m x.1 x.2 i))) z := by
    unfold collectiveDenominator
    fun_prop
  have hMc : ContinuousAt (fun x : ℂ × (Fin N → ℝ) => (preferredContourMatrix τ p m x.2).det) z :=
    ((preferredContourMatrix_contDiff τ p m hp hm).continuous.matrix_det.comp continuous_snd).continuousAt
  have hsc : ContinuousAt (fun x : ℂ × (Fin N → ℝ) => ‖x.1-s₀‖) z := by fun_prop
  filter_upwards [(preferredSourceRegime_isOpen τ δ p m hp.continuous hm.continuous).mem_nhds hreg,
    hsc.eventually_lt continuousAt_const hs,hqev,hRc.eventually_ne hR,hMc.eventually_ne hM]
    with x hxreg hxs hxq hxR hxM
  exact ⟨hxreg,hxs,hxq,hxR,hxM⟩

/-- Closed one-sided angular endpoints lie in a slightly larger genuine
open chart, because the actual trace inequality has a strict margin. -/
theorem preferred_source_regime_enlarge {N : ℕ} (τ δ : ℝ) (p m : ℝ → ℝ)
    (s : ℂ) (θ : Fin N → ℝ) (hδ : 0<δ) (hδπ : δ<Real.pi/2)
    (hS : 0<(temperatureTrace s).re) (hSi : 0<(temperatureTrace s).im)
    (hSδ : (temperatureTrace s).re<2*Real.cos δ)
    (hθ : ∀ i, θ i∈Set.Icc (-Real.pi-δ) δ)
    (hW : ∀ i, 0<(temperatureTrace s-Complex.cos (deformedAngles τ p m θ i)).im) :
    ∃ δ', 0<δ' ∧ δ'<Real.pi/2 ∧ PreferredSourceRegime τ δ' p m (s,θ) := by
  have hcos : ContinuousAt (fun x : ℝ => 2*Real.cos x) δ := by fun_prop
  have hlt : ∀ᶠ x : ℝ in 𝓝 δ, x<Real.pi/2 := Iio_mem_nhds hδπ
  have he : ∀ᶠ x : ℝ in 𝓝 δ, x<Real.pi/2 ∧ (temperatureTrace s).re<2*Real.cos x :=
    hlt.and (continuousAt_const.eventually_lt hcos hSδ)
  obtain ⟨δ',hgt,hπ',hS'⟩ : ∃ δ', δ<δ' ∧ δ'<Real.pi/2 ∧
      (temperatureTrace s).re<2*Real.cos δ' := Filter.Eventually.exists_gt he
  refine ⟨δ',hδ.trans hgt,hπ',hS,hSi,hS',?_,hW⟩
  intro i
  have hlo := (hθ i).1
  have hhi := (hθ i).2
  change -Real.pi-δ'<θ i ∧ θ i<δ'
  constructor <;> linarith

/-- Pointwise actual physical/regular equality at every order on the full
closed right source chart. The open neighborhood and all physical and
regular descendant differentiability are constructed by the proof. -/
theorem preferredTransportedDensity_factorization_at {N : ℕ} (hN : 0<N)
    (τ δ : ℝ) (η p m r : ℝ → ℝ) (hη : ContDiff ℝ ∞ η) (hp : ContDiff ℝ ∞ p)
    (hm : ContDiff ℝ ∞ m) (hr : ContDiff ℝ ∞ r) (hδ : 0<δ) (hδπ : δ<Real.pi/2)
    (s₀ : ℂ) (ρ : ℝ) (D : Set ℂ) (c : ℝ) (hc : 0<c) (hD : Convex ℝ D)
    (hU : ∀ s, ‖s-s₀‖<ρ → ∀ q∈D,
      AnalyticAt ℂ (fun x : ℂ × ℂ => preferredMovingInverse x.1 x.2) (s,q))
    (hcurv : ∀ s, ‖s-s₀‖<ρ → ∀ q∈D, c≤(deriv (preferredSourceUQ s) q).re)
    (s : ℂ) (θ : Fin N → ℝ) (hs : ‖s-s₀‖<ρ)
    (hS : 0<(temperatureTrace s).re) (hSi : 0<(temperatureTrace s).im)
    (hSδ : (temperatureTrace s).re<2*Real.cos δ)
    (hθ : ∀ i, θ i∈Set.Icc (-Real.pi-δ) δ)
    (hW : ∀ i, 0<(temperatureTrace s-Complex.cos (deformedAngles τ p m θ i)).im)
    (hq : ∀ i, preferredSourceCoordinate τ p m s θ i∈interior D)
    (hR : collectiveDenominator (fun i => preferredMovingInverse s
      (preferredSourceCoordinate τ p m s θ i))≠0)
    (hM : (preferredContourMatrix τ p m θ).det≠0) (j : ℕ) :
    preferredTransportedDensity .right τ η p m r j s θ=
      preferredCoordinateJacobian τ p m s θ*preferredSourceResolvent τ p m s θ*
        preferredRegularTransportedScalar τ η p m r j s θ := by
  obtain ⟨δ',hδ',hδπ',hreg⟩ := preferred_source_regime_enlarge τ δ p m s θ hδ hδπ hS hSi hSδ hθ hW
  let Ω := preferredTransportDomain (N := N) τ δ' p m s₀ ρ D
  have hΩ : IsOpen Ω := preferredTransportDomain_isOpen τ δ' p m hp hm s₀ ρ D hU
  have hz : (s,θ)∈Ω := ⟨hreg,hs,hq,hR,hM⟩
  exact preferredTransportedDensity_factorization hN τ δ' η p m r hη hp hm hr hδ' hδπ'
    Ω hΩ (fun _ hz => hz.1) D c hc hD
    (fun z hz => hU z.1 hz.2.1) (fun z hz => hcurv z.1 hz.2.1)
    (fun _ hz i => interior_subset (hz.2.2.1 i)) (fun _ hz => hz.2.2.2.1)
    (fun _ hz => hz.2.2.2.2) j (s,θ) hz


/-- The actual all-order physical/regular factorization on the complete
right contour. The bump cap and positive geometric radii precede every
particle count and derivative order, and every analytic, R and M premise is
discharged from the source constructions. -/
theorem preferred_actual_all_order_factorization (d : PreferredBranchData) :
    ∃ cap : ℝ,0<cap ∧ cap<d.alpha ∧ ∀ B : PreferredCoareaBump d,B.delta<cap →
      ∃ δB τ₀ ε₀ : ℝ,0<δB ∧ δB<B.delta ∧ 0<τ₀ ∧ 0<ε₀ ∧
      ∀ N : ℕ,2≤N → ∀ ε τ : ℝ,0<ε → ε<ε₀ → 0≤τ → τ<τ₀ →
      ∀ θ : Fin N → ℝ,θ∈preferredRightAngularBox d B.delta δB N →
      0<preferredAngularDiameter θ →
      ∀ η rcut : ℝ → ℝ,ContDiff ℝ ∞ η → ContDiff ℝ ∞ rcut → ∀ j : ℕ,
      let s := IsingBulk.Branch.radialParameter d.alpha ε
      preferredTransportedDensity .right τ η B.p B.m rcut j s θ=
        preferredCoordinateJacobian τ B.p B.m s θ*preferredSourceResolvent τ B.p B.m s θ*
          preferredRegularTransportedScalar τ η B.p B.m rcut j s θ := by
  obtain ⟨cap,ρ,c,D,hcap,hcapa,hρ,hc,_hDc,hDv,_hzero,hgood,hsource⟩ :=
    preferred_uniform_regular_source_domain d
  refine ⟨cap,hcap,hcapa,?_⟩
  intro B hBcap
  obtain ⟨r,hr,himage⟩ := hsource B.p B.m B.smooth.continuous B.m_smooth.continuous
  obtain ⟨εs,hεs,hmargin⟩ := preferred_radial_one_sided_margins d B.delta B.delta_pos (hBcap.trans hcapa)
  obtain ⟨τR,hτR,hRgeom⟩ := balanced_source_collective_geometry B.p B.m B.smooth B.m_smooth
    B.periodic (PreferredCoareaBump.m_periodic B)
  obtain ⟨τM,hτM,hMrow⟩ := preferredContourMatrix_uniform_half_row B.p B.m B.smooth B.m_smooth
    B.periodic (PreferredCoareaBump.m_periodic B)
    (fun x => by rw [abs_of_nonneg (B.lower_bound x)]; exact B.upper_bound x)
    (fun x => by change |B.p (-x)|≤1; rw [abs_of_nonneg (B.lower_bound (-x))]; exact B.upper_bound (-x))
  let δB := min (r/2) (B.delta/2)
  let τ₀ := min r (min τR τM)
  let ε₀ := min r (min ρ εs)
  have hδB : 0<δB := lt_min (half_pos hr) (half_pos B.delta_pos)
  have hδBδ : δB<B.delta := (min_le_right _ _).trans_lt (half_lt_self B.delta_pos)
  have hτ₀ : 0<τ₀ := lt_min hr (lt_min hτR hτM)
  have hε₀ : 0<ε₀ := lt_min hr (lt_min hρ hεs)
  refine ⟨δB,τ₀,ε₀,hδB,hδBδ,hτ₀,hε₀,?_⟩
  intro N hN ε τ hε hεr hτ hτr θ hθ hdiam η rcut hη hrcut j
  have hN0 : 0<N := by omega
  have hεr' : ε<r := hεr.trans_le (min_le_left _ _)
  have hερ : ε<ρ := hεr.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hεs' : ε<εs := hεr.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hτr' : τ<r := hτr.trans_le (min_le_left _ _)
  have hτR' : τ≤τR := (hτr.trans_le ((min_le_right _ _).trans (min_le_left _ _))).le
  have hτM' : τ≤τM := (hτr.trans_le ((min_le_right _ _).trans (min_le_right _ _))).le
  let s := IsingBulk.Branch.radialParameter d.alpha ε
  obtain ⟨hSr,hSi,hSδ⟩ := hmargin ε hε hεs'
  have hθ' (i : Fin N) : θ i∈Icc (-Real.pi-B.delta) B.delta := by
    have hh := hθ i
    exact ⟨by linarith [hh.1,d.b_lt,hδBδ],hh.2⟩
  have hpunit (x : ℝ) : B.p x∈Icc 0 1 := ⟨B.lower_bound x,B.upper_bound x⟩
  have hmunit (x : ℝ) : B.m x∈Icc 0 1 := ⟨B.lower_bound (-x),B.upper_bound (-x)⟩
  have hW (i : Fin N) : 0<(temperatureTrace s-Complex.cos (deformedAngles τ B.p B.m θ i)).im := by
    have hh := homotopy_complexW_im_pos hSi hτ (by norm_num : (0:ℝ)≤1) B.p B.m θ
      B.lower_bound (fun x => B.lower_bound (-x))
      (fun x hx => B.p_zero_of_sin_nonpos hx) (fun x hx => B.m_zero_of_sin_nonneg hx) i
    simpa only [complexW_homotopyRoot_eq] using hh
  have hsd : ‖s-preferredSelectedPoint d‖<ρ := by
    rw [preferred_radial_distance,abs_of_pos hε]
    exact hερ
  have hq (i : Fin N) : preferredSourceCoordinate τ B.p B.m s θ i∈interior D := by
    have hh := himage ε τ (occupancy B.p θ/(N:ℝ)) (occupancy B.m θ/(N:ℝ)) (θ i)
      (by simpa only [abs_of_pos hε] using hεr')
      (by simpa only [abs_of_nonneg hτ] using hτr')
      (preferred_occupancy_mean_mem hN0 B.p hpunit θ)
      (preferred_occupancy_mean_mem hN0 B.m hmunit θ)
      (by have hv := (hθ i).1; have hδ : δB≤r := (min_le_left _ _).trans (by linarith); linarith)
      ((hθ i).2.trans hBcap.le)
    rw [preferredBumpCoordinate_actual] at hh
    exact hh
  have hU (t : ℂ) (ht : ‖t-preferredSelectedPoint d‖<ρ) (q : ℂ) (hq : q∈D) :
      AnalyticAt ℂ (fun x : ℂ × ℂ => preferredMovingInverse x.1 x.2) (t,q) :=
    (hgood t q q ht hq hq).2.1
  have hcurv (t : ℂ) (ht : ‖t-preferredSelectedPoint d‖<ρ) (q : ℂ) (hq : q∈D) :
      c≤(deriv (preferredSourceUQ t) q).re := by
    have hh := hgood t q q ht hq hq
    change c≤(deriv (deriv (preferredMovingInverse t)) q).re
    rw [← preferredMovingCurvature_eq_deriv t q hh.2.1]
    exact hh.2.2.2.1.le
  have hR := (hRgeom τ hτ hτR' N hN0 θ s B.delta B.delta_pos
    (hBcap.trans (hcapa.trans d.alpha_lt)) hSr hSi hSδ hθ' B.lower_bound
    (fun x => B.lower_bound (-x)) (fun x hx => B.p_zero_of_sin_nonpos hx)
    (fun x hx => B.m_zero_of_sin_nonneg hx)).2.2 hdiam
  have hM : (preferredContourMatrix τ B.p B.m θ).det≠0 :=
    (preferred_matrix_inverse_of_row_three_quarters _
      (fun i => (hMrow τ hτ hτM' N hN0 θ i).trans (by norm_num))).1
  exact preferredTransportedDensity_factorization_at hN0 τ B.delta η B.p B.m rcut
    hη B.smooth B.m_smooth hrcut B.delta_pos (hBcap.trans (hcapa.trans d.alpha_lt))
    (preferredSelectedPoint d) ρ D c hc hDv hU hcurv s θ hsd hSr hSi hSδ hθ' hW hq hR hM j

end
end IsingBulk.Preferred22
