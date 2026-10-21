import IsingBulk.HT.Tail.CoupledPlateau
import IsingBulk.Tail.MixedHybridDensity

/-! The onsite field freezes every branch coordinate separately. It has no
selected-difference denominator and is zero on every compact coordinate.
All contour points retain the full coupled occupancy. -/
namespace IsingBulk.HT.Lie
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Tail Set Filter
open scoped Topology BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def onsiteBranchField {N : ℕ} (J : Finset (Fin N)) (f : SelectorFunctions)
    (r τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ) (i : Fin N) : ℂ :=
  if i∈J then mixedSourceA s (deformedPoint f r τ lam θ i) else 0

@[simp] theorem onsiteBranchField_of_not_mem {N : ℕ} (J : Finset (Fin N))
    (f : SelectorFunctions) (r τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ)
    (i : Fin N) (hi : i∉J) : onsiteBranchField J f r τ lam s θ i=0 := by
  simp [onsiteBranchField,hi]

theorem onsite_individual_phase_transport {N : ℕ} (J : Finset (Fin N))
    (f : SelectorFunctions) {r : ℝ} (hr : 0<r) (τ lam : ℝ)
    (s : ℂ) (θ : Fin N → ℝ) (i : Fin N) (hi : i∈J) (hs : s≠0)
    (hp : ∀ k,DifferentiableAt ℝ f.p (θ k))
    (hm : ∀ k,DifferentiableAt ℝ f.m (θ k))
    (hplateau : ∀ k∈J,deriv f.p (θ k)=0 ∧ deriv f.m (θ k)=0)
    (hW : 0<(sourceW s (deformedPoint f r τ lam θ i)).im)
    (hg : deformedPoint f r τ lam θ i-(deformedPoint f r τ lam θ i)⁻¹≠0) :
    mixedCoordinateTransport (onsiteBranchField J f r τ lam)
      (fun t x => mixedContourPhase f r τ lam t x i) s θ=0 := by
  have he (k : Fin N) : onsiteBranchField J f r τ lam s θ k *
      coordDeriv (fun x => mixedContourPhase f r τ lam s x i) θ k =
      if i=k then mixedSourceTau s (deformedPoint f r τ lam θ i) else 0 := by
    by_cases hk : k∈J
    · rw [mixedContourPhase_plateau_coordinate f hr τ lam s θ k i hp hm
        (hplateau k hk).1 (hplateau k hk).2 hW]
      by_cases hik : i=k
      · subst k
        simp only [onsiteBranchField,hi,ite_true]
        rw [mul_comm,mixedSourceSlope_mul_A hg]
      · simp [hik]
    · have hik : i≠k := by intro he; subst k; exact hk hi
      simp [onsiteBranchField,hk,hik]
  unfold mixedCoordinateTransport
  change deriv (fun t => mixedSourcePhase t (deformedPoint f r τ lam θ i)) s -
    ∑ k, onsiteBranchField J f r τ lam s θ k *
      coordDeriv (fun x => mixedContourPhase f r τ lam s x i) θ k = 0
  rw [(mixedSourcePhase_parameter hs hW).deriv]
  simp_rw [he]
  simp

/-- Every hybrid residual is zero, including all compact spectators. -/
theorem onsite_hybrid_transport_zero {N : ℕ} (J : Finset (Fin N))
    (f : SelectorFunctions) {r : ℝ} (hr : 0<r) (τ lam : ℝ)
    (s : ℂ) (θ : Fin N → ℝ) (hs : s≠0)
    (hp : ∀ k,DifferentiableAt ℝ f.p (θ k))
    (hm : ∀ k,DifferentiableAt ℝ f.m (θ k))
    (hplateau : ∀ k∈J,deriv f.p (θ k)=0 ∧ deriv f.m (θ k)=0)
    (hW : ∀ i∈J,0<(sourceW s (deformedPoint f r τ lam θ i)).im)
    (hg : ∀ i∈J,deformedPoint f r τ lam θ i-(deformedPoint f r τ lam θ i)⁻¹≠0)
    (i : Fin N) :
    mixedCoordinateTransport (onsiteBranchField J f r τ lam)
      (fun t x => mixedHybridMap J f r τ lam t x i) s θ=0 := by
  by_cases hi : i∈J
  · simp only [mixedHybridMap,hi,ite_true]
    exact onsite_individual_phase_transport J f hr τ lam s θ i hi hs hp hm
      hplateau (hW i hi) (hg i hi)
  · simp only [mixedHybridMap,hi,ite_false]
    rw [mixed_angle_transport]
    simp [onsiteBranchField,hi]

/-- Actual regular coefficient differentiation takes place at fixed hybrid
coordinates. No residual or kernel-freezing condition is assumed. -/
theorem onsite_hybrid_transport_chain {N : ℕ} (J : Finset (Fin N))
    (f : SelectorFunctions) {r : ℝ} (hr : 0<r) (τ lam : ℝ)
    (s : ℂ) (θ : Fin N → ℝ) (hs : s≠0)
    (hp : ∀ k,DifferentiableAt ℝ f.p (θ k))
    (hm : ∀ k,DifferentiableAt ℝ f.m (θ k))
    (hplateau : ∀ k∈J,deriv f.p (θ k)=0 ∧ deriv f.m (θ k)=0)
    (hW : ∀ i∈J,0<(sourceW s (deformedPoint f r τ lam θ i)).im)
    (hg : ∀ i∈J,deformedPoint f r τ lam θ i-(deformedPoint f r τ lam θ i)⁻¹≠0)
    (F : ℂ → (Fin N → ℂ) → ℂ)
    (hF : DifferentiableAt ℂ (fun z : ℂ × (Fin N → ℂ) => F z.1 z.2)
      (s,mixedHybridMap J f r τ lam s θ)) :
    mixedCoordinateTransport (onsiteBranchField J f r τ lam)
      (fun t x => F t (mixedHybridMap J f r τ lam t x)) s θ =
      deriv (fun t => F t (mixedHybridMap J f r τ lam s θ)) s := by
  rw [mixedHybrid_transport_chain J f hr τ lam s θ _ F hs hp hm hW hF]
  simp_rw [onsite_hybrid_transport_zero J f hr τ lam s θ hs hp hm hplateau hW hg]
  exact (hF.hasFDerivAt.comp_hasDerivAt s
    ((hasDerivAt_id s).prodMk (hasDerivAt_const s (mixedHybridMap J f r τ lam s θ)))).deriv.symm

/-- The plateau derivatives used above follow from the genuine geometric
core, rather than freezing the occupancy in the definition. -/
theorem onsite_constructed_hybrid_transport_zero {N : ℕ} (J : Finset (Fin N))
    {b η α : ℝ} (hb : 0<Real.sin b) (hη : 0<η)
    (hηsmall : η≤Real.sin b/4) (hα : 0<α)
    {r : ℝ} (hr : 0<r) (τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ)
    (hs : s≠0) (hcore : ∀ i∈J,lowerChord b (θ i)<η^2)
    (hW : ∀ i∈J,0<(sourceW s (deformedPoint (constructedSelector b η α) r τ lam θ i)).im)
    (hg : ∀ i∈J,deformedPoint (constructedSelector b η α) r τ lam θ i-
      (deformedPoint (constructedSelector b η α) r τ lam θ i)⁻¹≠0)
    (i : Fin N) :
    mixedCoordinateTransport (onsiteBranchField J (constructedSelector b η α) r τ lam)
      (fun t x => mixedHybridMap J (constructedSelector b η α) r τ lam t x i) s θ=0 := by
  apply onsite_hybrid_transport_zero J _ hr τ lam s θ hs
    (fun k => (constructedSelector_regular b η α hb hη hηsmall hα).p_smooth.differentiable (by simp) _)
    (fun k => (constructedSelector_regular b η α hb hη hηsmall hα).m_smooth.differentiable (by simp) _)
    _ hW hg i
  intro k hk
  have h := constructed_branch_plateau_germ hb hη hηsmall hα (hcore k hk)
  exact ⟨by simpa only [deriv_const] using h.1.deriv_eq,
    by simpa only [deriv_const] using h.2.deriv_eq⟩

end
end IsingBulk.HT.Lie
