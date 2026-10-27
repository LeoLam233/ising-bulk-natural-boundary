import IsingBulk.Preferred22.AnchorTransport

/-! All-order physical identification of the literal anchor scalar
recurrence. The unchanged H resolvent is included in its initial amplitude. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- One actual cell step factors J by the proved Piola identity. The
complete resolvent remains part of G, so no phase-freezing premise occurs. -/
theorem preferred_physical_cell_transport_factorization {N : ℕ}
    (cell : PreferredTransportCell N) (τ δ : ℝ) (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m) (s : ℂ) (θ : Fin N → ℝ)
    (hδ : 0<δ) (hδπ : δ<Real.pi/2) (hreg : PreferredSourceRegime τ δ p m (s,θ))
    (hU : ∀ i,AnalyticAt ℂ (fun x : ℂ × ℂ => preferredMovingInverse x.1 x.2)
      (s,preferredSourceCoordinate τ p m s θ i))
    (hBa : AnalyticAt ℂ (fun x : ℂ × (Fin N → ℂ) => preferredResidualField cell x.1 x.2)
      (s,preferredSourceCoordinate τ p m s θ))
    (hM : (preferredContourMatrix τ p m θ).det≠0)
    (G : ℂ → (Fin N → ℝ) → ℂ)
    (hGs : DifferentiableAt ℂ (fun t => G t θ) s)
    (hGθ : ∀ i,DifferentiableAt ℝ (fun x => G s (Function.update θ i x)) (θ i)) :
    preferredTransportStep (preferredSourceAngularField cell τ p m)
      (fun t x => preferredCoordinateJacobian τ p m t x*G t x) s θ=
      preferredCoordinateJacobian τ p m s θ*preferredCellRegularTransportStep cell τ p m G s θ := by
  obtain ⟨hS,hSi,hSδ,hθo,hW⟩ := hreg
  have hθ (i : Fin N) : θ i∈Icc (-Real.pi-δ) δ := ⟨(hθo i).1.le,(hθo i).2.le⟩
  have hv (i : Fin N) : preferredSourceUQ s (preferredSourceCoordinate τ p m s θ i)≠0 := by
    exact (preferred_global_one_sided_q_regular s (deformedAngles τ p m θ i) δ hδ hδπ hS hSδ
      (by simpa only [deformedAngles_re] using (hθ i).1)
      (by simpa only [deformedAngles_re] using (hθ i).2) (hW i)).2
  have hJ := preferredCoordinateJacobian_contDiffAt τ p m hp hm s θ hSi hW hU hv
  have hV (i : Fin N) := preferredSourceAngularField_mixed_cellDomain cell τ p m hp hm i
    (s,θ) ⟨hSi,hW,hM,hBa,hU⟩
  have hcoord (F : ℂ × (Fin N → ℝ) → ℂ) (hF : DifferentiableAt ℝ F (s,θ)) (i : Fin N) :
      DifferentiableAt ℝ (fun x => F (s,Function.update θ i x)) (θ i) :=
    (hF.hasFDerivAt.comp_hasDerivAt_of_eq (θ i)
      ((hasDerivAt_const (θ i) s).prodMk (hasDerivAt_update θ i (θ i)))
      (by simp only [Function.update_eq_self])).differentiableAt
  have hpiola := preferredCoordinateJacobian_cell_piola cell τ δ p m hp hm s θ hδ hδπ
    ⟨hS,hSi,hSδ,hθo,hW⟩ hU hBa hM
  have hh := preferredTransportStep_factored (preferredSourceAngularField cell τ p m)
    (preferredCoordinateJacobian τ p m) (fun _ _ => (1:ℂ)) G s θ
    (preferredCellRegularDivergence cell τ p m s θ)
    (preferredCoordinateJacobian_parameter_analyticAt τ p m s θ hSi hW hU hv).differentiableAt
    (differentiableAt_const _) hGs
    (fun i => hcoord _ (hJ.differentiableAt (by simp)) i)
    (fun _ => differentiableAt_const _) hGθ
    (fun i => hcoord _ ((hV i).1.differentiableAt (by simp)) i)
    hpiola (by simp)
  rw [preferredCellRegularTransportStep_eq]
  simpa only [mul_one,preferredCellRegularDivergence] using hh

/-- The all-order physical factorization derives differentiability of each
generated scalar by division by its nonzero actual coordinate Jacobian. -/
theorem preferredTransportedDensity_cell_factorization_of_mixed {N : ℕ}
    (cell : PreferredTransportCell N) (τ δ : ℝ) (η p m r : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (hδ : 0<δ) (hδπ : δ<Real.pi/2)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hreg : ∀ z∈Ω,PreferredSourceRegime τ δ p m z)
    (hU : ∀ z∈Ω,∀ i,AnalyticAt ℂ (fun x : ℂ × ℂ => preferredMovingInverse x.1 x.2)
      (z.1,preferredSourceCoordinate τ p m z.1 z.2 i))
    (hBa : ∀ z∈Ω,AnalyticAt ℂ (fun x : ℂ × (Fin N → ℂ) => preferredResidualField cell x.1 x.2)
      (z.1,preferredSourceCoordinate τ p m z.1 z.2))
    (hM : ∀ z∈Ω,(preferredContourMatrix τ p m z.2).det≠0)
    (hP : ∀ j,PreferredMixedSmoothOn
      (fun z => preferredTransportedDensity cell τ η p m r j z.1 z.2) Ω) :
    ∀ j,∀ z∈Ω,preferredTransportedDensity cell τ η p m r j z.1 z.2=
      preferredCoordinateJacobian τ p m z.1 z.2*preferredCellRegularScalar cell τ η p m r j z.1 z.2 := by
  have hp' := hp.differentiable (by simp)
  have hm' := hm.differentiable (by simp)
  have hnonzero (z : ℂ × (Fin N → ℝ)) (hz : z∈Ω) : preferredCoordinateJacobian τ p m z.1 z.2≠0 := by
    obtain ⟨hzS,_,hzSδ,hzθ,hzW⟩ := hreg z hz
    exact preferredCoordinateJacobian_ne_zero τ δ p m hp' hm' z.1 z.2 hδ hδπ hzS hzSδ
      (fun i => ⟨(hzθ i).1.le,(hzθ i).2.le⟩) hzW (hM z hz)
  intro j
  induction j with
  | zero =>
    intro z hz
    obtain ⟨hzS,_,hzSδ,hzθ,hzW⟩ := hreg z hz
    exact preferredPhysicalSeed_cell_factorized cell τ δ η p m r z.1 z.2 hδ hδπ hzS hzSδ
      (fun i => ⟨(hzθ i).1.le,(hzθ i).2.le⟩) hzW
  | succ j ih =>
    rintro ⟨s,θ⟩ hz
    obtain ⟨hS,hSi,hSδ,hθo,hW⟩ := hreg (s,θ) hz
    have hθ (i : Fin N) : θ i∈Icc (-Real.pi-δ) δ := ⟨(hθo i).1.le,(hθo i).2.le⟩
    have hv (i : Fin N) : preferredSourceUQ s (preferredSourceCoordinate τ p m s θ i)≠0 :=
      (preferred_global_one_sided_q_regular s (deformedAngles τ p m θ i) δ hδ hδπ hS hSδ
        (by simpa only [deformedAngles_re] using (hθ i).1)
        (by simpa only [deformedAngles_re] using (hθ i).2) (hW i)).2
    have hJa := preferredCoordinateJacobian_parameter_analyticAt τ p m s θ hSi hW (hU (s,θ) hz) hv
    have hJc := preferredCoordinateJacobian_contDiffAt τ p m hp hm s θ hSi hW (hU (s,θ) hz) hv
    let Q := fun z : ℂ × (Fin N → ℝ) => preferredTransportedDensity cell τ η p m r j z.1 z.2 /
      preferredCoordinateJacobian τ p m z.1 z.2
    have hQc : ContDiffAt ℝ ∞ Q (s,θ) := by
      simp only [Q,div_eq_mul_inv]
      convert! ((hP j (s,θ) hz).1).mul (hJc.inv (hnonzero (s,θ) hz)) using 1
    have hQa : DifferentiableAt ℂ (fun t => Q (t,θ)) s :=
      ((hP j (s,θ) hz).2).div hJa.differentiableAt (hnonzero (s,θ) hz)
    have he : (fun z : ℂ × (Fin N → ℝ) => preferredCellRegularScalar cell τ η p m r j z.1 z.2)
        =ᶠ[𝓝 (s,θ)] Q := by
      filter_upwards [hΩ.mem_nhds hz] with z hzz
      apply (eq_div_iff (hnonzero z hzz)).mpr
      calc
        _ = preferredCoordinateJacobian τ p m z.1 z.2*preferredCellRegularScalar cell τ η p m r j z.1 z.2 := mul_comm _ _
        _ = _ := (ih z hzz).symm
    have hGs : DifferentiableAt ℂ (fun t => preferredCellRegularScalar cell τ η p m r j t θ) s :=
      hQa.congr_of_eventuallyEq
        (he.comp_tendsto ((show Continuous (fun t : ℂ => (t,θ)) by fun_prop).tendsto s))
    have hGθ (i : Fin N) : DifferentiableAt ℝ
        (fun x => preferredCellRegularScalar cell τ η p m r j s (Function.update θ i x)) (θ i) := by
      have hmap : Continuous (fun x : ℝ => (s,Function.update θ i x)) := by fun_prop
      have ht : Filter.Tendsto (fun x : ℝ => (s,Function.update θ i x)) (𝓝 (θ i)) (𝓝 (s,θ)) := by
        simpa only [Function.update_eq_self] using hmap.tendsto (θ i)
      have hd := (hQc.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq (θ i)
        ((hasDerivAt_const (θ i) s).prodMk (hasDerivAt_update θ i (θ i)))
        (by simp only [Function.update_eq_self])
      exact hd.differentiableAt.congr_of_eventuallyEq (he.comp_tendsto ht)
    change preferredTransportStep (preferredSourceAngularField cell τ p m)
      (preferredTransportedDensity cell τ η p m r j) s θ=_
    rw [preferredTransportStep_congr_open (preferredSourceAngularField cell τ p m)
      (preferredTransportedDensity cell τ η p m r j)
      (fun t x => preferredCoordinateJacobian τ p m t x*preferredCellRegularScalar cell τ η p m r j t x)
      Ω hΩ ih s θ hz]
    exact preferred_physical_cell_transport_factorization cell τ δ p m hp hm s θ hδ hδπ
      ⟨hS,hSi,hSδ,hθo,hW⟩ (hU (s,θ) hz) (hBa (s,θ) hz) (hM (s,θ) hz) _ hGs hGθ

/-- The finite actual source geometry discharges every descendant
regularity premise in the all-order identity. -/
theorem preferredTransportedDensity_cell_factorization {N : ℕ} (hN : 0<N)
    (cell : PreferredTransportCell N) (τ δ : ℝ) (η p m r : ℝ → ℝ)
    (hη : ContDiff ℝ ∞ η) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m) (hr : ContDiff ℝ ∞ r)
    (hδ : 0<δ) (hδπ : δ<Real.pi/2)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hreg : ∀ z∈Ω,PreferredSourceRegime τ δ p m z)
    (hU : ∀ z∈Ω,∀ i,AnalyticAt ℂ (fun x : ℂ × ℂ => preferredMovingInverse x.1 x.2)
      (z.1,preferredSourceCoordinate τ p m z.1 z.2 i))
    (hBa : ∀ z∈Ω,AnalyticAt ℂ (fun x : ℂ × (Fin N → ℂ) => preferredResidualField cell x.1 x.2)
      (z.1,preferredSourceCoordinate τ p m z.1 z.2))
    (hM : ∀ z∈Ω,(preferredContourMatrix τ p m z.2).det≠0) :
    ∀ j,∀ z∈Ω,preferredTransportedDensity cell τ η p m r j z.1 z.2=
      preferredCoordinateJacobian τ p m z.1 z.2*preferredCellRegularScalar cell τ η p m r j z.1 z.2 := by
  apply preferredTransportedDensity_cell_factorization_of_mixed cell τ δ η p m r hp hm hδ hδπ
    Ω hΩ hreg hU hBa hM
  intro j z hz
  obtain ⟨_,hSi,_,_,hW⟩ := hreg z hz
  exact preferredTransportedDensity_mixed_cellDomain cell hN τ η p m r hη hp hm hr j z
    ⟨hSi,hW,hM z hz,hBa z hz,hU z hz⟩

/-- The actual anchor scalar and physical recurrence agree at every order
on every strict source frame chart, including total particle equality. -/
theorem preferred_anchor_factorization_on_chart {N : ℕ} (hN : 0<N)
    (a : Fin N) (τ δ : ℝ) (η p m r : ℝ → ℝ)
    (hη : ContDiff ℝ ∞ η) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m) (hr : ContDiff ℝ ∞ r)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hpoint : ∀ z∈Ω,PreferredFramePoint τ δ p m z.1 z.2)
    (hstrict : ∀ z∈Ω,∀ i,z.2 i∈Ioo (-Real.pi-δ) δ) :
    ∀ j,∀ z∈Ω,preferredTransportedDensity (.anchor a) τ η p m r j z.1 z.2=
      preferredCoordinateJacobian τ p m z.1 z.2*preferredCellRegularScalar (.anchor a) τ η p m r j z.1 z.2 := by
  by_cases hΩne : Ω.Nonempty
  · obtain ⟨z,hz⟩ := hΩne
    have hd := hpoint z hz
    exact preferredTransportedDensity_cell_factorization hN (.anchor a) τ δ η p m r hη hp hm hr
      hd.delta_pos hd.delta_lt Ω hΩ
      (fun x hx => ⟨(hpoint x hx).trace_re,(hpoint x hx).trace_im,(hpoint x hx).trace_cap,hstrict x hx,(hpoint x hx).upper⟩)
      (fun x hx => (hpoint x hx).inverse_analytic)
      (fun x hx => preferredResidualAnchor_analyticAt a _ _ (hpoint x hx).inverse_analytic
        ((hpoint x hx).inverse_q_ne_zero a))
      (fun x hx => (hpoint x hx).matrix)
  · intro j z hz
    exact (hΩne ⟨z,hz⟩).elim

end
end IsingBulk.Preferred22
