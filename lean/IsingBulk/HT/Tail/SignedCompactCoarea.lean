import IsingBulk.Tail.CompactActualPairCoarea
import IsingBulk.HT.Lie.SignedCoarea

/-! Signed compact-right coarea of the literal coupled phase. The actual
Jacobian and injectivity are reused; constant phase translations alter
neither. Spectator volume and N periods are charged explicitly. -/
namespace IsingBulk.HT.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Tail IsingBulk.HT.Lie Set MeasureTheory Filter
open scoped Topology BigOperators ContDiff
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

def shiftedCoordinatePhaseKernel {N : ℕ} (i j : Fin N) (a b ξ ζ : ℝ) (x : Fin N → ℝ) : ℝ :=
  (phaseDenominator (Real.exp (-a)) (x i+ξ))⁻¹*(phaseDenominator (Real.exp (-b)) (x j+ζ))⁻¹

theorem shiftedCoordinatePhaseKernel_nonneg {N : ℕ} (i j : Fin N) (a b ξ ζ : ℝ) (x : Fin N → ℝ) :
    0≤shiftedCoordinatePhaseKernel i j a b ξ ζ x := by
  unfold shiftedCoordinatePhaseKernel phaseDenominator
  positivity

theorem shiftedCoordinatePhaseKernel_continuous {N : ℕ} (i j : Fin N) {a b : ℝ}
    (ha : 0<a) (hb : 0<b) (ξ ζ : ℝ) : Continuous (shiftedCoordinatePhaseKernel i j a b ξ ζ) :=
  ((simple_kernel_continuous ha).comp ((continuous_apply i).add continuous_const)).mul
    ((simple_kernel_continuous hb).comp ((continuous_apply j).add continuous_const))

theorem shifted_phase_spectator_kernel_integral (ξ ζ : ℝ) {N : ℕ} {i j : Fin N} (hij : i≠j)
    {R a b : ℝ} (hR : 0≤R) (ha : 0<a) (ha1 : a≤1) (hb : 0<b) (hb1 : b≤1) :
    IntegrableOn (shiftedCoordinatePhaseKernel i j a b ξ ζ) (phaseSpectatorBox i j R) ∧
      (∫ x in phaseSpectatorBox i j R, shiftedCoordinatePhaseKernel i j a b ξ ζ x)≤
      ((N:ℝ)*simpleKernelConstant*(1+|Real.log a|))*
      ((N:ℝ)*simpleKernelConstant*(1+|Real.log b|))*(2*R)^(N-2) := by
  have hcont := shiftedCoordinatePhaseKernel_continuous i j ha hb ξ ζ
  refine ⟨hcont.continuousOn.integrableOn_compact isCompact_Icc,?_⟩
  let h : Fin N → ℝ := fun l => if l=i ∨ l=j then (N:ℝ)*Real.pi else R
  let w : Fin N → ℝ → ℝ := fun l t => if l=i then (phaseDenominator (Real.exp (-a)) (t+ξ))⁻¹
    else if l=j then (phaseDenominator (Real.exp (-b)) (t+ζ))⁻¹ else 1
  have hw (x : Fin N → ℝ) : shiftedCoordinatePhaseKernel i j a b ξ ζ x=∏ l, w l (x l) := by
    have he := prod_two_distinguished hij
      ((phaseDenominator (Real.exp (-a)) (x i+ξ))⁻¹)
      ((phaseDenominator (Real.exp (-b)) (x j+ζ))⁻¹) 1
    simp only [one_pow,mul_one] at he
    unfold shiftedCoordinatePhaseKernel
    rw [← he]
    apply Finset.prod_congr rfl
    intro l _
    by_cases hli : l=i
    · subst l; simp [w]
    · by_cases hlj : l=j
      · subst l; simp [w,Ne.symm hij]
      · simp [w,hli,hlj]
  have hmeasure : volume.restrict (phaseSpectatorBox i j R)=
      Measure.pi (fun l => volume.restrict (Icc (-h l) (h l))) := by
    rw [phaseSpectatorBox,← Set.pi_univ_Icc,volume_pi,Measure.restrict_pi_pi]
  simp_rw [hw]
  rw [hmeasure,integral_fintype_prod_eq_prod]
  let A := (N:ℝ)*simpleKernelConstant*(1+|Real.log a|)
  let B := (N:ℝ)*simpleKernelConstant*(1+|Real.log b|)
  have hNpi : 0≤(N:ℝ)*Real.pi := by positivity
  have haI : (∫ t in Icc (-(N:ℝ)*Real.pi) ((N:ℝ)*Real.pi), (phaseDenominator (Real.exp (-a)) (t+ξ))⁻¹)≤A := by
    have he := shifted_kernel_interval_integral ha ha1 ξ N
      (show -(N:ℝ)*Real.pi≤(N:ℝ)*Real.pi by linarith)
      (show (N:ℝ)*Real.pi≤-(N:ℝ)*Real.pi+(N:ℝ)*(2*Real.pi) by ring_nf; rfl)
    rw [intervalIntegral.integral_of_le (show -(N:ℝ)*Real.pi≤(N:ℝ)*Real.pi by linarith),← integral_Icc_eq_integral_Ioc] at he
    exact he
  have hbI : (∫ t in Icc (-(N:ℝ)*Real.pi) ((N:ℝ)*Real.pi), (phaseDenominator (Real.exp (-b)) (t+ζ))⁻¹)≤B := by
    have he := shifted_kernel_interval_integral hb hb1 ζ N
      (show -(N:ℝ)*Real.pi≤(N:ℝ)*Real.pi by linarith)
      (show (N:ℝ)*Real.pi≤-(N:ℝ)*Real.pi+(N:ℝ)*(2*Real.pi) by ring_nf; rfl)
    rw [intervalIntegral.integral_of_le (show -(N:ℝ)*Real.pi≤(N:ℝ)*Real.pi by linarith),← integral_Icc_eq_integral_Ioc] at he
    exact he
  calc
    _ ≤ ∏ l : Fin N, if l=i then A else if l=j then B else 2*R := by
      apply Finset.prod_le_prod₀
      · intro l _
        apply integral_nonneg
        intro t
        dsimp [w]
        split_ifs <;> first | exact inv_nonneg.mpr (norm_nonneg _) | norm_num
      · intro l _
        by_cases hli : l=i
        · subst l; simpa [w,h,neg_mul] using haI
        · by_cases hlj : l=j
          · subst l; simpa [w,h,Ne.symm hij,neg_mul] using hbI
          · simp only [w,h,hli,hlj,ite_false,or_self]
            rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le (by linarith : -R≤R)]
            simp
            linarith
    _ = _ := prod_two_distinguished hij A B (2*R)


theorem signed_actual_compact_right_pair_coarea (ξ ζ : ℝ) (d : LocalBranchData)
    (hcsmall : d.c₀<Real.sin d.theta/2) (f : SelectorFunctions) (hf : RegularSelector f)
    (hp1 : ∀ x, f.p x≤1) {δ : ℝ} (hδ : 0<δ) (hδsmall : δ<2*(1-Real.cos d.thetaB))
    {D β : ℝ} (hD : 0≤D) (hβ : 0<β) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ H : ℝ in atTop, ∀ (N : ℕ), 0<N → (N:ℝ)≤D*Real.sqrt H →
      ∀ (τ lam : ℝ) (i j : Fin N), i≠j → 0≤τ → τ≤1 → 0≤lam → lam≤Real.exp (-β*H) →
      ∀ a b : ℝ, 0<a → a≤1 → 0<b → b≤1 →
      let G := currentUnwrappedPhase (N := N) f (Real.exp (-d.c₀*Real.exp (-H))) τ lam
        (radialParameter d.theta (Real.exp (-H)))
      let T := twoPhaseUpdate (fun y => ∑ l, y l) G i j
      let S := orderedCompactCell i j (rightSectorRadius d.thetaB δ)
      IntegrableOn (fun x => (x j-x i)*shiftedCoordinatePhaseKernel i j a b ξ ζ (T x)) S ∧
      (∫ x in S, (x j-x i)*shiftedCoordinatePhaseKernel i j a b ξ ζ (T x))≤
        C*(((N:ℝ)*simpleKernelConstant*(1+|Real.log a|))*
        ((N:ℝ)*simpleKernelConstant*(1+|Real.log b|))*(2*rightSectorRadius d.thetaB δ)^(N-2)) := by
  obtain ⟨k,hk,hjac⟩ := actual_compact_right_pair_jacobian d hcsmall f hf hp1 hδ hδsmall hD hβ
  have hinj := actual_compact_right_pair_injective d hcsmall f hf hp1 hδ hδsmall hD hβ
  obtain ⟨hR,hRb⟩ := right_sector_radius_bounds d.thetaB_pos d.thetaB_lt hδ hδsmall
  refine ⟨k⁻¹,inv_pos.mpr hk,?_⟩
  filter_upwards [hjac,hinj] with H hjacH hinjH
  intro N hN hND τ lam i j hij hτ hτ1 hlam hlamB a b ha ha1 hb hb1
  let R := rightSectorRadius d.thetaB δ
  let G := currentUnwrappedPhase (N := N) f (Real.exp (-d.c₀*Real.exp (-H))) τ lam
    (radialParameter d.theta (Real.exp (-H)))
  let T := twoPhaseUpdate (fun y => ∑ l, y l) G i j
  let S := orderedCompactCell i j R
  let L := fun x => twoPhaseUpdateDeriv (coordinateSumLinear N) (fderiv ℝ G x) i j
  have hsource (x : Fin N → ℝ) (hx : x∈S) : HasFDerivAt T (L x) x ∧ k*(x j-x i)≤|(L x).det| := by
    have hh := hjacH N hN hND τ lam x i j hij hx.2.le hτ hτ1 hlam hlamB
      (orderedCompactCell_coordinates hx)
    exact ⟨hh.1,hh.2.2⟩
  have himage : T '' S⊆phaseSpectatorBox i j R := by
    rintro _ ⟨x,hx,rfl⟩
    exact actual_phase_update_image f _ _ _ _ i j (hRb.le.trans d.thetaB_lt.le)
      (orderedCompactCell_coordinates hx)
  obtain ⟨hki,hkbound⟩ := shifted_phase_spectator_kernel_integral ξ ζ hij hR.le ha ha1 hb hb1
  have hrati (x : Fin N → ℝ) (hx : x∈S) : x j-x i≤k⁻¹*|(L x).det| := by
    have hh := (le_div_iff₀ hk).mpr (show (x j-x i)*k≤|(L x).det| by
      simpa only [mul_comm] using (hsource x hx).2)
    simpa only [div_eq_mul_inv,mul_comm] using hh
  obtain ⟨hi,hbound⟩ := injective_coordinate_weighted_coarea_le
    (orderedCompactCell_measurable i j R) T L (fun x hx => (hsource x hx).1.hasFDerivWithinAt)
    (hinjH N hN hND τ lam i j hij hτ hτ1 hlam hlamB) himage
    (fun x => x j-x i) (shiftedCoordinatePhaseKernel i j a b ξ ζ)
    ((continuous_apply j).sub (continuous_apply i)).continuousOn
    (shiftedCoordinatePhaseKernel_continuous i j ha hb ξ ζ) (shiftedCoordinatePhaseKernel_nonneg i j a b ξ ζ)
    hki (inv_nonneg.mpr hk.le) (fun _ hx => sub_nonneg.mpr hx.2.le) hrati
  exact ⟨hi,hbound.trans (mul_le_mul_of_nonneg_left hkbound (inv_nonneg.mpr hk.le))⟩

end
end IsingBulk.HT.Tail
