import IsingBulk.Tail.CompactPairCoarea
import IsingBulk.Tail.PairPhaseInjectivity

/-! Multiplicity-one coarea for the actual coupled compact-right phase. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set MeasureTheory Filter
open scoped Topology ContDiff BigOperators
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

def orderedCompactCell {N : ℕ} (i j : Fin N) (R : ℝ) : Set (Fin N → ℝ) :=
  Icc (fun _ => -R) (fun _ => R) ∩ {x | x i<x j}

theorem orderedCompactCell_measurable {N : ℕ} (i j : Fin N) (R : ℝ) :
    MeasurableSet (orderedCompactCell i j R) :=
  measurableSet_Icc.inter (isOpen_lt (continuous_apply i) (continuous_apply j)).measurableSet

theorem orderedCompactCell_convex {N : ℕ} (i j : Fin N) (R : ℝ) :
    Convex ℝ (orderedCompactCell i j R) := by
  apply (convex_Icc _ _).inter
  have hlin : IsLinearMap ℝ (fun x : Fin N → ℝ => x i-x j) := by
    constructor
    · intro x y; simp; ring
    · intro c x; simp; ring
  simpa only [sub_lt_zero] using convex_halfSpace_lt hlin 0

theorem orderedCompactCell_coordinates {N : ℕ} {i j : Fin N} {R : ℝ} {x : Fin N → ℝ}
    (hx : x∈orderedCompactCell i j R) : ∀ l, x l∈Icc (-R) R :=
  fun l => ⟨hx.1.1 l,hx.1.2 l⟩

theorem actual_phase_update_image {N : ℕ} (f : SelectorFunctions) (r τ lam : ℝ) (s : ℂ)
    (i j : Fin N) {R : ℝ} (hRπ : R≤Real.pi) {x : Fin N → ℝ}
    (hx : ∀ l, x l∈Icc (-R) R) :
    twoPhaseUpdate (fun y => ∑ l, y l) (currentUnwrappedPhase f r τ lam s) i j x∈phaseSpectatorBox i j R := by
  have hsum := abs_le.mp (angular_sum_abs_le x (fun l => (abs_le.mpr (hx l)).trans hRπ))
  have hphase := abs_le.mp (currentUnwrappedPhase_abs_le f r τ lam s x)
  constructor <;> intro l
  all_goals
    by_cases hli : l=i
    · subst l
      first | simpa [twoPhaseUpdate] using hsum.1 | simpa [twoPhaseUpdate] using hsum.2
    · by_cases hlj : l=j
      · subst l
        simp only [twoPhaseUpdate,hli,ite_false,ite_true,or_true]
        first | exact hphase.1 | exact hphase.2
      · simp only [twoPhaseUpdate,hli,hlj,ite_false,or_self]
        first | exact (hx l).1 | exact (hx l).2

/-- Actual injectivity follows from the signed source slope on the convex
ordered cell, not from a multiplicity hypothesis. -/
theorem actual_compact_right_pair_injective (d : LocalBranchData)
    (hcsmall : d.c₀<Real.sin d.theta/2) (f : SelectorFunctions) (hf : RegularSelector f)
    (hp1 : ∀ x, f.p x≤1) {δ : ℝ} (hδ : 0<δ) (hδsmall : δ<2*(1-Real.cos d.thetaB))
    {D β : ℝ} (hD : 0≤D) (hβ : 0<β) :
    ∀ᶠ H : ℝ in atTop, ∀ (N : ℕ), 0<N → (N:ℝ)≤D*Real.sqrt H →
      ∀ (τ lam : ℝ) (i j : Fin N), i≠j → 0≤τ → τ≤1 → 0≤lam → lam≤Real.exp (-β*H) →
      InjOn (twoPhaseUpdate (fun y => ∑ l, y l)
        (currentUnwrappedPhase (N := N) f (Real.exp (-d.c₀*Real.exp (-H))) τ lam
          (radialParameter d.theta (Real.exp (-H)))) i j)
        (orderedCompactCell i j (rightSectorRadius d.thetaB δ)) := by
  obtain ⟨k,hk,hjac⟩ := actual_compact_right_pair_jacobian d hcsmall f hf hp1 hδ hδsmall hD hβ
  filter_upwards [hjac,radial_current_phase_eventually_smooth d hcsmall f hf] with H hbound hsmooth
  intro N hN hND τ lam i j hij hτ hτ1 hlam hlamB
  let G := currentUnwrappedPhase (N := N) f (Real.exp (-d.c₀*Real.exp (-H))) τ lam
    (radialParameter d.theta (Real.exp (-H)))
  let S := orderedCompactCell i j (rightSectorRadius d.thetaB δ)
  have hG : ContDiff ℝ ∞ G := hsmooth N hN τ lam hτ hlam
  intro x hx y hy heq
  obtain ⟨hsum,hphase,hspect⟩ := twoPhaseUpdate_equal_data hij heq
  apply fixed_sum_pair_phase_injective S (orderedCompactCell_convex i j _) G i j hij
    (fun z _ => hG.differentiable (by simp) z) _ hx hy hsum hphase hspect
  intro z hz
  have hb := hbound N hN hND τ lam z i j hij hz.2.le hτ hτ1 hlam hlamB
    (orderedCompactCell_coordinates hz)
  exact lt_of_lt_of_le (mul_pos hk (sub_pos.mpr hz.2)) hb.2.1


/-- The full source cell has multiplicity one. Its weighted phase integral
charges the spectator cube and the N-by-N periods exactly once. -/
theorem actual_compact_right_pair_coarea (d : LocalBranchData)
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
      IntegrableOn (fun x => (x j-x i)*coordinatePhaseKernel i j a b (T x)) S ∧
      (∫ x in S, (x j-x i)*coordinatePhaseKernel i j a b (T x))≤
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
  obtain ⟨hki,hkbound⟩ := phase_spectator_kernel_integral hij hR.le ha ha1 hb hb1
  have hrati (x : Fin N → ℝ) (hx : x∈S) : x j-x i≤k⁻¹*|(L x).det| := by
    have hh := (le_div_iff₀ hk).mpr (show (x j-x i)*k≤|(L x).det| by
      simpa only [mul_comm] using (hsource x hx).2)
    simpa only [div_eq_mul_inv,mul_comm] using hh
  obtain ⟨hi,hbound⟩ := injective_coordinate_weighted_coarea_le
    (orderedCompactCell_measurable i j R) T L (fun x hx => (hsource x hx).1.hasFDerivWithinAt)
    (hinjH N hN hND τ lam i j hij hτ hτ1 hlam hlamB) himage
    (fun x => x j-x i) (coordinatePhaseKernel i j a b)
    ((continuous_apply j).sub (continuous_apply i)).continuousOn
    (coordinatePhaseKernel_continuous i j ha hb) (coordinatePhaseKernel_nonneg i j a b)
    hki (inv_nonneg.mpr hk.le) (fun _ hx => sub_nonneg.mpr hx.2.le) hrati
  exact ⟨hi,hbound.trans (mul_le_mul_of_nonneg_left hkbound (inv_nonneg.mpr hk.le))⟩

end
end IsingBulk.Tail
