import IsingBulk.Preferred22.WeightedTransportCore
import IsingBulk.Preferred22.VandermondeTransport

/-! Exact physical Piola and full collision factorization for a smooth
multiplier inserted into the original physical seed. Derivatives of the
multiplier remain inside the same literal transport recurrence. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false

theorem preferredWeightedPhysicalDensity_factorization_of_mixed {N : ℕ} (hN : 0<N)
    (ψ : (Fin N → ℝ) → ℂ) (τ δ : ℝ) (η p m r : ℝ → ℝ) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
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
      (fun z => preferredWeightedPhysicalDensity ψ τ η p m r j z.1 z.2) Ω) :
    ∀ j, ∀ z∈Ω, preferredWeightedPhysicalDensity ψ τ η p m r j z.1 z.2=
      preferredCoordinateJacobian τ p m z.1 z.2*preferredSourceResolvent τ p m z.1 z.2*
        preferredWeightedRegularScalar ψ τ η p m r j z.1 z.2 := by
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
    change ψ z.2*preferredPhysicalSeed .right τ η p m r z.1 z.2=_
    rw [preferredPhysicalSeed_factorized τ δ η p m r z.1 z.2 hδ hδπ hzS hzSδ
      (fun i => ⟨(hzθ i).1.le,(hzθ i).2.le⟩) hzW]
    simp only [preferredWeightedRegularScalar]
    ring
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
    let Q := fun z : ℂ × (Fin N → ℝ) => preferredWeightedPhysicalDensity ψ τ η p m r j z.1 z.2 /
      (preferredCoordinateJacobian τ p m z.1 z.2*preferredSourceResolvent τ p m z.1 z.2)
    have hQc : ContDiffAt ℝ ∞ Q (s,θ) := by
      simp only [Q,div_eq_mul_inv]
      convert! ((hP j (s,θ) hz).1).mul ((hJc.mul hHc).inv (hnonzero (s,θ) hz)) using 1
    have hQa : DifferentiableAt ℂ (fun t => Q (t,θ)) s :=
      ((hP j (s,θ) hz).2).div (hJa.differentiableAt.mul hHa.differentiableAt) (hnonzero (s,θ) hz)
    have he : (fun z : ℂ × (Fin N → ℝ) => preferredWeightedRegularScalar ψ τ η p m r j z.1 z.2)
        =ᶠ[𝓝 (s,θ)] Q := by
      filter_upwards [hΩ.mem_nhds hz] with z hzz
      apply (eq_div_iff (hnonzero z hzz)).mpr
      calc
        _ = preferredCoordinateJacobian τ p m z.1 z.2*preferredSourceResolvent τ p m z.1 z.2*
          preferredWeightedRegularScalar ψ τ η p m r j z.1 z.2 := by ring
        _ = _ := (ih z hzz).symm
    have hGs : DifferentiableAt ℂ (fun t => preferredWeightedRegularScalar ψ τ η p m r j t θ) s :=
      hQa.congr_of_eventuallyEq
        (he.comp_tendsto ((show Continuous (fun t : ℂ => (t,θ)) by fun_prop).tendsto s))
    have hGθ (i : Fin N) : DifferentiableAt ℝ
        (fun x => preferredWeightedRegularScalar ψ τ η p m r j s (Function.update θ i x)) (θ i) := by
      have hmap : Continuous (fun x : ℝ => (s,Function.update θ i x)) := by fun_prop
      have ht : Filter.Tendsto (fun x : ℝ => (s,Function.update θ i x)) (𝓝 (θ i)) (𝓝 (s,θ)) := by
        simpa only [Function.update_eq_self] using hmap.tendsto (θ i)
      have hd := (hQc.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq (θ i)
        ((hasDerivAt_const (θ i) s).prodMk (hasDerivAt_update θ i (θ i)))
        (by simp only [Function.update_eq_self])
      exact hd.differentiableAt.congr_of_eventuallyEq (he.comp_tendsto ht)
    change preferredTransportStep (preferredSourceAngularField .right τ p m)
      (preferredWeightedPhysicalDensity ψ τ η p m r j) s θ=_
    rw [preferredTransportStep_congr_open (preferredSourceAngularField .right τ p m)
      (preferredWeightedPhysicalDensity ψ τ η p m r j)
      (fun t x => preferredCoordinateJacobian τ p m t x*preferredSourceResolvent τ p m t x*
        preferredWeightedRegularScalar ψ τ η p m r j t x) Ω hΩ ih s θ hz]
    exact preferred_physical_transport_factorization hN τ δ p m hp hm s θ hδ hδπ
      ⟨hS,hSi,hSδ,hθo,hW⟩ D c hc hD (hU (s,θ) hz) (hcurv (s,θ) hz) (hq (s,θ) hz)
      (hR (s,θ) hz) (hM (s,θ) hz) _ hGs hGθ



theorem preferredWeightedRegularScalar_vandermonde {N : ℕ}
    (ψ : (Fin N → ℝ) → ℂ) (τ δ : ℝ) (η p m r : ℝ → ℝ) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (C : ℂ → (Fin N → ℝ) → Fin N → Fin N → ℂ)
    (A : ℂ → (Fin N → ℝ) → ℂ)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2)
    (hV : ∀ i, PreferredMixedSmoothOn (fun z => preferredSourceAngularField .right τ p m z.1 z.2 i) Ω)
    (hc : PreferredMixedSmoothOn (fun z => preferredRegularDivergenceCoefficient τ p m z.1 z.2) Ω)
    (hC : ∀ i j, PreferredMixedSmoothOn (fun z => C z.1 z.2 i j) Ω)
    (hA : PreferredMixedSmoothOn (fun z => A z.1 z.2) Ω)
    (hfactor : ∀ z∈Ω, ∀ i j,
      preferredResidualCollective z.1 (preferredSourceCoordinate τ p m z.1 z.2) i-
        preferredResidualCollective z.1 (preferredSourceCoordinate τ p m z.1 z.2) j=
      (preferredSourceCoordinate τ p m z.1 z.2 i-preferredSourceCoordinate τ p m z.1 z.2 j)*C z.1 z.2 i j)
    (hseed : ∀ z∈Ω, ψ z.2*preferredRegularSeed τ η p m r z.1 z.2=
      A z.1 z.2*preferredSquaredVandermonde (preferredSourceCoordinate τ p m z.1 z.2))
    (j : ℕ) (s : ℂ) (θ : Fin N → ℝ) (hz : (s,θ)∈Ω) :
    preferredWeightedRegularScalar ψ τ η p m r j s θ=
      preferredVandermondeScalar τ p m C A j s θ*
        preferredSquaredVandermonde (preferredSourceCoordinate τ p m s θ) := by
  induction j generalizing s θ with
  | zero => exact hseed (s,θ) hz
  | succ j ih =>
    have hmix := preferredVandermondeScalar_mixed τ p m C A Ω hΩ hV hc hC hA j
    rw [preferredWeightedRegularScalar,
      preferredRegularTransportStep_congr_open τ p m _
        (fun t x => preferredVandermondeScalar τ p m C A j t x*
          preferredSquaredVandermonde (preferredSourceCoordinate τ p m t x))
        Ω hΩ (fun z hz => ih z.1 z.2 hz) s θ hz]
    exact preferredRegularTransportStep_vandermonde τ δ p m hp hm
      (preferredVandermondeScalar τ p m C A j) s θ (hpoint (s,θ) hz)
      (hmix (s,θ) hz).2 (preferredMixed_coordinate_differentiable _ s θ (hmix (s,θ) hz).1)
      (C s θ) (hfactor (s,θ) hz)


end
end IsingBulk.Preferred22
