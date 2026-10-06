import IsingBulk.Tail.CompactActualPairCoarea
import IsingBulk.Tail.AllBranchExteriorPositiveCover

/-! The ordered-cell coarea estimates cover the whole compact cube after
taking absolute values. One diameter power pays for the colliding Jacobian;
the cover has at most N squared members, with no differentiated extremum. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Branch Set MeasureTheory Filter
open scoped Topology BigOperators ContDiff
set_option maxHeartbeats 1800000

theorem compact_diameter_integral_of_pair_bounds {N : ℕ} (R : ℝ)
    (K : (Fin N → ℝ) → ℝ) (hK : Continuous K) (hK0 : ∀ x, 0 ≤ K x)
    {C : ℝ} (hC : 0 ≤ C)
    (hpairs : ∀ i j : Fin N, i ≠ j →
      IntegrableOn (fun x => (x j-x i)*K x) (orderedCompactCell i j R) ∧
      (∫ x in orderedCompactCell i j R, (x j-x i)*K x) ≤ C) :
    IntegrableOn (fun x => allBranchExteriorDiameter x*K x)
      (Icc (fun _ => -R) (fun _ => R)) ∧
    (∫ x in Icc (fun _ => -R) (fun _ => R), allBranchExteriorDiameter x*K x) ≤
      (N:ℝ)^2*C := by
  classical
  let S : Set (Fin N → ℝ) := Icc (fun _ => -R) (fun _ => R)
  let f := fun x => allBranchExteriorDiameter x*K x
  let E := (Finset.univ : Finset (Fin N × Fin N)).filter (fun p => p.1 ≠ p.2)
  let G := fun (p : Fin N × Fin N) =>
    (orderedCompactCell p.1 p.2 R).indicator (fun x => (x p.2-x p.1)*K x)
  have hf : IntegrableOn f S :=
    (allBranchExterior_diameter_continuous.mul hK).continuousOn.integrableOn_compact isCompact_Icc
  have hG0 (p : Fin N × Fin N) (x : Fin N → ℝ) : 0 ≤ G p x := by
    apply indicator_nonneg
    intro y hy
    exact mul_nonneg (sub_nonneg.mpr hy.2.le) (hK0 y)
  have hGi (p : Fin N × Fin N) (hp : p ∈ E) : Integrable (G p) :=
    (integrable_indicator_iff (orderedCompactCell_measurable _ _ _)).mpr
      (hpairs p.1 p.2 (Finset.mem_filter.mp hp).2).1
  have hsum : Integrable (fun x => ∑ p ∈ E, G p x) := integrable_finsetSum E hGi
  have hpoint (x : Fin N → ℝ) : S.indicator f x ≤ ∑ p ∈ E, G p x := by
    by_cases hx : x ∈ S
    · rw [indicator_of_mem hx]
      by_cases hd : 0 < allBranchExteriorDiameter x
      · obtain ⟨i,j,hij,he,_⟩ := allBranchExterior_oriented_extrema x hd
        have hE : (i,j) ∈ E := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hij⟩
        have hcell : x ∈ orderedCompactCell i j R := ⟨hx,by change x i < x j; linarith⟩
        have hone := Finset.single_le_sum (s := E) (fun p _ => hG0 p x) hE
        have heq : G (i,j) x=f x := by
          rw [show G (i,j) x=(orderedCompactCell i j R).indicator
            (fun y => (y j-y i)*K y) x from rfl,indicator_of_mem hcell]
          exact congrArg (fun t => t*K x) he
        rwa [heq] at hone
      · have hz : allBranchExteriorDiameter x=0 := le_antisymm (le_of_not_gt hd)
          (allBranchExterior_diameter_nonneg x)
        simpa only [f,hz,zero_mul] using Finset.sum_nonneg (fun p (_ : p ∈ E) => hG0 p x)
    · rw [indicator_of_notMem hx]
      exact Finset.sum_nonneg (fun p _ => hG0 p x)
  have hcard : (E.card:ℝ) ≤ (N:ℝ)^2 := by
    have hh := Finset.card_le_univ E
    have hn : E.card ≤ N^2 := by simpa [pow_two] using hh
    exact_mod_cast hn
  refine ⟨hf,?_⟩
  calc
    _ = ∫ x, S.indicator f x := (integral_indicator measurableSet_Icc).symm
    _ ≤ ∫ x, ∑ p ∈ E, G p x :=
      integral_mono ((integrable_indicator_iff measurableSet_Icc).mpr hf) hsum hpoint
    _ = ∑ p ∈ E, ∫ x, G p x := integral_finsetSum E hGi
    _ ≤ ∑ _p ∈ E, C := by
      apply Finset.sum_le_sum
      intro p hp
      change (∫ x, (orderedCompactCell p.1 p.2 R).indicator
        (fun y => (y p.2-y p.1)*K y) x) ≤ C
      rw [integral_indicator (orderedCompactCell_measurable _ _ _)]
      exact (hpairs p.1 p.2 (Finset.mem_filter.mp hp).2).2
    _ = (E.card:ℝ)*C := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard hC

theorem coordinatePhaseKernel_update {N : ℕ} {i j : Fin N} (hij : i ≠ j)
    (F G : (Fin N → ℝ) → ℝ) (a b : ℝ) (x : Fin N → ℝ) :
    coordinatePhaseKernel i j a b (twoPhaseUpdate F G i j x)=
      twoPhaseKernel a b (F x,G x) := by
  simp [coordinatePhaseKernel,twoPhaseUpdate,twoPhaseKernel,Ne.symm hij]

/-- Actual compact-right phase kernel on the entire signed cube, with all
spectator volume and all periods retained. -/
theorem actual_compact_right_diameter_integral (d : IsingBulk.Branch.LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) (f : SelectorFunctions) (hf : RegularSelector f)
    (hp1 : ∀ x, f.p x ≤ 1) {δ : ℝ} (hδ : 0 < δ) (hδsmall : δ < 2*(1-Real.cos d.thetaB))
    {D β : ℝ} (hD : 0 ≤ D) (hβ : 0 < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ H : ℝ in atTop, ∀ N : ℕ, 0 < N → (N:ℝ) ≤ D*Real.sqrt H →
      ∀ τ lam : ℝ, 0 ≤ τ → τ ≤ 1 → 0 ≤ lam → lam ≤ Real.exp (-β*H) →
      ∀ a b : ℝ, 0 < a → a ≤ 1 → 0 < b → b ≤ 1 →
      let G := currentUnwrappedPhase (N := N) f (Real.exp (-d.c₀*Real.exp (-H))) τ lam
        (radialParameter d.theta (Real.exp (-H)))
      let S := Icc (fun _ : Fin N => -rightSectorRadius d.thetaB δ)
        (fun _ => rightSectorRadius d.thetaB δ)
      let K := fun x => twoPhaseKernel a b ((∑ i, x i),G x)
      IntegrableOn (fun x => allBranchExteriorDiameter x*K x) S ∧
      (∫ x in S, allBranchExteriorDiameter x*K x) ≤
        (N:ℝ)^2*(C*(((N:ℝ)*simpleKernelConstant*(1+|Real.log a|))*
        ((N:ℝ)*simpleKernelConstant*(1+|Real.log b|))*(2*rightSectorRadius d.thetaB δ)^(N-2))) := by
  obtain ⟨C,hC,hpairs⟩ := actual_compact_right_pair_coarea d hcsmall f hf hp1 hδ hδsmall hD hβ
  obtain ⟨hR,_⟩ := right_sector_radius_bounds d.thetaB_pos d.thetaB_lt hδ hδsmall
  refine ⟨C,hC,?_⟩
  filter_upwards [hpairs,radial_current_phase_eventually_smooth d hcsmall f hf] with H hpair hphase
  intro N hN hND τ lam hτ hτ1 hlam hlamB a b ha ha1 hb hb1
  dsimp only
  apply compact_diameter_integral_of_pair_bounds
  · exact (twoPhaseKernel_continuous ha hb).comp
      ((continuous_finsetSum _ (fun i _ => continuous_apply i)).prodMk
        (hphase N hN τ lam hτ hlam).continuous)
  · intro x; exact twoPhaseKernel_nonneg _ _ _
  · have := simpleKernelConstant_pos
    positivity
  · intro i j hij
    simpa only [coordinatePhaseKernel_update hij] using
      hpair N hN hND τ lam i j hij hτ hτ1 hlam hlamB a b ha ha1 hb hb1

end
end IsingBulk.Tail
