import IsingBulk.Tail.MixedHybridChart

/-! The residuals here are transports of the literal coupled hybrid map.
Only the active columns use plateaus; all spectator occupancy is retained. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set Filter
open scoped Topology BigOperators

theorem mixed_individual_phase_transport {N : ℕ} (J : Finset (Fin N)) (j q i : Fin N)
    (f : SelectorFunctions) {r : ℝ} (hr : 0<r) (τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ)
    (hj : j∈J) (hs : s≠0)
    (hp : ∀ k,DifferentiableAt ℝ f.p (θ k)) (hm : ∀ k,DifferentiableAt ℝ f.m (θ k))
    (hplateau : ∀ k,k∈J ∨ k=q → deriv f.p (θ k)=0 ∧ deriv f.m (θ k)=0)
    (hW : 0<(sourceW s (deformedPoint f r τ lam θ i)).im) :
    mixedCoordinateTransport (mixedContourVelocity J j q f r τ lam)
      (fun t x => mixedContourPhase f r τ lam t x i) s θ =
      mixedSourceTau s (deformedPoint f r τ lam θ i)-
        mixedSourceSlope s (deformedPoint f r τ lam θ i)*mixedContourVelocity J j q f r τ lam s θ i := by
  have he (k : Fin N) : mixedContourVelocity J j q f r τ lam s θ k *
      coordDeriv (fun x => mixedContourPhase f r τ lam s x i) θ k =
      if i=k then mixedSourceSlope s (deformedPoint f r τ lam θ i)*
        mixedContourVelocity J j q f r τ lam s θ i else 0 := by
    by_cases hk : k∈J ∨ k=q
    · rw [mixedContourPhase_plateau_coordinate f hr τ lam s θ k i hp hm
        (hplateau k hk).1 (hplateau k hk).2 hW]
      split_ifs with hik
      · subst k; ring
      · simp
    · have hz := mixedContourVelocity_zero J j q k f r τ lam s θ hj
        (fun h => hk (Or.inl h)) (fun h => hk (Or.inr h))
      rw [hz,zero_mul]
      split_ifs with hik
      · subst k; rw [hz,mul_zero]
      · rfl
  unfold mixedCoordinateTransport
  have ht : deriv (fun t => mixedContourPhase f r τ lam t θ i) s =
      mixedSourceTau s (deformedPoint f r τ lam θ i) := (mixedSourcePhase_parameter hs hW).deriv
  rw [ht]
  simp_rw [he]
  simp

theorem mixed_other_branch_phase_frozen {N : ℕ} (J : Finset (Fin N)) (j q i : Fin N)
    (f : SelectorFunctions) {r : ℝ} (hr : 0<r) (τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ)
    (hj : j∈J) (hi : i∈J) (hij : i≠j) (hq : q∉J) (hs : s≠0)
    (hp : ∀ k,DifferentiableAt ℝ f.p (θ k)) (hm : ∀ k,DifferentiableAt ℝ f.m (θ k))
    (hplateau : ∀ k,k∈J ∨ k=q → deriv f.p (θ k)=0 ∧ deriv f.m (θ k)=0)
    (hW : 0<(sourceW s (deformedPoint f r τ lam θ i)).im)
    (hg : deformedPoint f r τ lam θ i-(deformedPoint f r τ lam θ i)⁻¹≠0) :
    mixedCoordinateTransport (mixedContourVelocity J j q f r τ lam)
      (fun t x => mixedContourPhase f r τ lam t x i) s θ=0 := by
  rw [mixed_individual_phase_transport J j q i f hr τ lam s θ hj hs hp hm hplateau hW]
  unfold mixedContourVelocity
  rw [mixedVelocity_other_branch _ _ _ _ _ hi hij hq,mixedSourceSlope_mul_A hg,sub_self]

theorem mixed_angle_transport {N : ℕ}
    (V : ℂ → (Fin N → ℝ) → Fin N → ℂ) (s : ℂ) (θ : Fin N → ℝ) (i : Fin N) :
    mixedCoordinateTransport V (fun _ x => (x i:ℂ)) s θ = -V s θ i := by
  have hc (k : Fin N) : coordDeriv (fun x : Fin N → ℝ => (x i:ℂ)) θ k =
      if i=k then 1 else 0 := by
    unfold coordDeriv
    by_cases hik : i=k
    · subst k
      simp only [Function.update_self,ite_true]
      exact (Complex.ofRealCLM.hasDerivAt (x := θ i)).deriv
    · simp [hik]
  simp [mixedCoordinateTransport,hc]

/-- The selected branch residual is expressed without a difference pole. -/
theorem mixed_selected_branch_residual {N : ℕ} (J : Finset (Fin N)) (j q : Fin N)
    (f : SelectorFunctions) {r : ℝ} (hr : 0<r) (τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ)
    (hj : j∈J) (hq : q∉J) (hs : s≠0)
    (hp : ∀ k,DifferentiableAt ℝ f.p (θ k)) (hm : ∀ k,DifferentiableAt ℝ f.m (θ k))
    (hplateau : ∀ k,k∈J ∨ k=q → deriv f.p (θ k)=0 ∧ deriv f.m (θ k)=0)
    (hW : 0<(sourceW s (deformedPoint f r τ lam θ j)).im)
    (hg : deformedPoint f r τ lam θ j-(deformedPoint f r τ lam θ j)⁻¹≠0)
    (hb : mixedSourceSlope s (deformedPoint f r τ lam θ j)≠0)
    (hsep : mixedSourceSlope s (deformedPoint f r τ lam θ j)-
      mixedSourceSlope s (deformedPoint f r τ lam θ q)≠0) :
    mixedCoordinateTransport (mixedContourVelocity J j q f r τ lam)
      (fun t x => mixedContourPhase f r τ lam t x j) s θ =
    (let y := deformedPoint f r τ lam θ;
     let A := ∑ i∈J,mixedSourceA s (y i);
     let D := ∑ i∈Finset.univ.filter (fun i => i∉J),mixedSourceTau s (y i);
     -(D+mixedSourceSlope s (y q)*A)/(1-mixedSourceSlope s (y q)/mixedSourceSlope s (y j))) := by
  have hjq : j≠q := by intro he; subst q; exact hq hj
  rw [mixed_individual_phase_transport J j q j f hr τ lam s θ hj hs hp hm hplateau hW]
  simp only [mixedContourVelocity,mixedVelocity,hj,hjq,ite_true,ite_false,sub_zero]
  rw [mul_add,mixedSourceSlope_mul_A hg]
  simp only [sub_add_cancel_left]
  simpa only [neg_mul] using mixed_residual_reciprocal
    (∑ i∈Finset.univ.filter (fun i => i∉J),mixedSourceTau s (deformedPoint f r τ lam θ i))
    (∑ i∈J,mixedSourceA s (deformedPoint f r τ lam θ i)) _ _ hb hsep

/-- Compact hybrid coordinates have residual minus the angular velocity.
This sign is essential in the pullback density divergence. -/
theorem mixed_compact_hybrid_residual {N : ℕ} (J : Finset (Fin N)) (j q i : Fin N)
    (f : SelectorFunctions) (r τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ) (hi : i∉J) :
    mixedCoordinateTransport (mixedContourVelocity J j q f r τ lam)
      (fun t x => mixedHybridMap J f r τ lam t x i) s θ =
      -mixedContourVelocity J j q f r τ lam s θ i := by
  simp only [mixedHybridMap,hi,ite_false]
  exact mixed_angle_transport _ _ _ _

theorem mixedHybridMap_parameter {N : ℕ} (J : Finset (Fin N)) (f : SelectorFunctions)
    (r τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ) (hs : s≠0)
    (hW : ∀ i∈J,0<(sourceW s (deformedPoint f r τ lam θ i)).im) :
    HasDerivAt (fun t => mixedHybridMap J f r τ lam t θ)
      (fun i => if i∈J then mixedSourceTau s (deformedPoint f r τ lam θ i) else 0) s := by
  apply hasDerivAt_pi.mpr
  intro i
  by_cases hi : i∈J
  · simpa only [mixedHybridMap,mixedContourPhase,hi,ite_true] using mixedSourcePhase_parameter hs (hW i hi)
  · simp only [mixedHybridMap,hi,ite_false]
    exact hasDerivAt_const _ _

theorem mixedHybridMap_angular {N : ℕ} (J : Finset (Fin N)) (f : SelectorFunctions)
    {r : ℝ} (hr : 0<r) (τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ) (k : Fin N)
    (hp : ∀ i,DifferentiableAt ℝ f.p (θ i)) (hm : ∀ i,DifferentiableAt ℝ f.m (θ i))
    (hW : ∀ i∈J,0<(sourceW s (deformedPoint f r τ lam θ i)).im) :
    HasDerivAt (fun u => mixedHybridMap J f r τ lam s (Function.update θ k u))
      (fun i => mixedHybridJacobian J f r τ lam s θ i k) (θ k) := by
  apply hasDerivAt_pi.mpr
  intro i
  by_cases hi : i∈J
  · simpa only [mixedHybridMap,mixedHybridJacobian,mixedPhaseJacobianCoefficient,mixedContourPhase,hi,ite_true] using
      mixedContourPhase_coordinate f hr τ lam s θ k i hp hm (hW i hi)
  · simp only [mixedHybridMap,mixedHybridJacobian,hi,ite_false]
    by_cases hik : i=k
    · subst i
      simp only [Function.update_self,ite_true]
      convert (Complex.ofRealCLM.hasDerivAt (x := θ k)) using 1
      · rfl
      · rfl
    · simp only [Function.update_of_ne hik]
      simpa [hik] using hasDerivAt_const (θ k) (θ i:ℂ)

/-- Full coupled chain rule. No off-diagonal occupancy entry is discarded.
The residual vector is the transport of the actual hybrid coordinates. -/
theorem mixedHybrid_transport_chain {N : ℕ} (J : Finset (Fin N)) (f : SelectorFunctions)
    {r : ℝ} (hr : 0<r) (τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ)
    (V : ℂ → (Fin N → ℝ) → Fin N → ℂ)
    (F : ℂ → (Fin N → ℂ) → ℂ) (hs : s≠0)
    (hp : ∀ i,DifferentiableAt ℝ f.p (θ i)) (hm : ∀ i,DifferentiableAt ℝ f.m (θ i))
    (hW : ∀ i∈J,0<(sourceW s (deformedPoint f r τ lam θ i)).im)
    (hF : DifferentiableAt ℂ (fun z : ℂ × (Fin N → ℂ) => F z.1 z.2)
      (s,mixedHybridMap J f r τ lam s θ)) :
    mixedCoordinateTransport V (fun t x => F t (mixedHybridMap J f r τ lam t x)) s θ =
    fderiv ℂ (fun z : ℂ × (Fin N → ℂ) => F z.1 z.2)
      (s,mixedHybridMap J f r τ lam s θ)
      (1,fun i => mixedCoordinateTransport V
        (fun t x => mixedHybridMap J f r τ lam t x i) s θ) := by
  let L := fderiv ℂ (fun z : ℂ × (Fin N → ℂ) => F z.1 z.2)
    (s,mixedHybridMap J f r τ lam s θ)
  let T := fun i => if i∈J then mixedSourceTau s (deformedPoint f r τ lam θ i) else 0
  let M : Fin N → Fin N → ℂ := mixedHybridJacobian J f r τ lam s θ
  have ht : deriv (fun t => F t (mixedHybridMap J f r τ lam t θ)) s=L (1,T) := by
    exact (hF.hasFDerivAt.comp_hasDerivAt s
      ((hasDerivAt_id s).prodMk (mixedHybridMap_parameter J f r τ lam s θ hs hW))).deriv
  have hx (k : Fin N) : coordDeriv (fun x => F s (mixedHybridMap J f r τ lam s x)) θ k =
      L (0,fun i => M i k) := by
    have hh := (hF.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt_of_eq (θ k)
      ((hasDerivAt_const (θ k) s).prodMk (mixedHybridMap_angular J f hr τ lam s θ k hp hm hW))
      (by simp)
    convert hh.deriv using 1 <;> rfl
  have hi (i : Fin N) : mixedCoordinateTransport V
      (fun t x => mixedHybridMap J f r τ lam t x i) s θ = T i-∑ k,V s θ k*M i k := by
    unfold mixedCoordinateTransport
    rw [((hasDerivAt_pi.mp (mixedHybridMap_parameter J f r τ lam s θ hs hW)) i).deriv]
    simp_rw [mixedHybridMap_coordinate J f hr τ lam s θ _ _ hp hm hW]
    rfl
  change deriv (fun t => F t (mixedHybridMap J f r τ lam t θ)) s -
    (∑ k,V s θ k*coordDeriv (fun x => F s (mixedHybridMap J f r τ lam s x)) θ k) =
    L (1,fun i => mixedCoordinateTransport V (fun t x => mixedHybridMap J f r τ lam t x i) s θ)
  rw [ht]
  simp_rw [hx,hi,← smul_eq_mul,← map_smul]
  rw [← map_sum,← map_sub]
  congr 1
  apply Prod.ext
  · change (1:ℂ)-(ContinuousLinearMap.fst ℂ ℂ (Fin N → ℂ))
        (∑ k,V s θ k • (0,fun i => M i k))=1
    rw [map_sum]
    simp
  · change T-(ContinuousLinearMap.snd ℂ ℂ (Fin N → ℂ))
        (∑ k,V s θ k • (0,fun i => M i k))= _
    rw [map_sum]
    ext i
    simp [Finset.sum_apply,smul_eq_mul]

end
end IsingBulk.Tail
