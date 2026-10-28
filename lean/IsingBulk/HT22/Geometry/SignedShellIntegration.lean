import IsingBulk.HT22.Geometry.SignedFiberBound
import IsingBulk.Preferred22.ShellIntegration

/-! Exact signed affine shell integration. Generic hyperplane permutation,
Lebesgue disintegration and the N−2 independent one-body box are reused;
the denominator and all coarea inputs are the newly proved signed ones. -/
namespace IsingBulk.HT22.Geometry
noncomputable section
open scoped BigOperators Topology ENNReal
open Set MeasureTheory IsingBulk.Preferred22

theorem signed_full_shell_indicator_permutation (η : ℝ) {n : ℕ} (d : PreferredBranchData)
    (B : PreferredCoareaBump d) (δB r ε τ c : ℝ) (i j : Fin (n+1))
    (e : Equiv.Perm (Fin (n+1))) :
    (∫⁻ x : Fin n → ℝ,
      (preferredFullRightShell d B δB r (e.symm i) (e.symm j)).indicator
        (fun w => ENNReal.ofReal (signedJacobianResolvent η d B ε τ w)) (constrainedAtTotal c x)) =
      ∫⁻ x : Fin n → ℝ,
        (preferredFullRightShell d B δB r i j).indicator
          (fun w => ENNReal.ofReal (signedJacobianResolvent η d B ε τ w)) (constrainedAtTotal c x) := by
  rw [← constrained_hyperplane_lintegral_perm e c]
  apply lintegral_congr
  intro x
  let w := constrainedAtTotal c x
  change (preferredFullRightShell d B δB r (e.symm i) (e.symm j)).indicator
    (fun w => ENNReal.ofReal (signedJacobianResolvent η d B ε τ w)) (w ∘ e) =
      (preferredFullRightShell d B δB r i j).indicator
        (fun w => ENNReal.ofReal (signedJacobianResolvent η d B ε τ w)) w
  by_cases hw : w∈preferredFullRightShell d B δB r i j
  · have he := (preferredFullRightShell_perm d B δB r i j e w).2 hw
    rw [Set.indicator_of_mem he,Set.indicator_of_mem hw,signedJacobianResolvent_equiv]
  · have he := mt (preferredFullRightShell_perm d B δB r i j e w).1 hw
    rw [Set.indicator_of_notMem he,Set.indicator_of_notMem hw]

set_option maxHeartbeats 1400000 in
/-- Complete actual constrained Jacobian/resolvent shell integral, with the
canonical minimum and maximum. The full fiber and all remaining coordinates
are integrated with their true Lebesgue measures. -/
theorem signed_canonical_shell_jacobian_lintegral (d : PreferredBranchData)
    (B : PreferredCoareaBump d) :
    ∃ A C ε₀ τ₀ δ₀ : ℝ, 0 < A ∧ 0 < C ∧ 0 < ε₀ ∧ 0 < τ₀ ∧ 0 < δ₀ ∧ δ₀ < B.delta ∧
      ∀ η : ℝ, ∀ n : ℕ, ∀ ε τ c r δB : ℝ, 0 < ε → ε < ε₀ → 0 ≤ τ → τ < τ₀ →
      0 < r → 0 < δB → δB ≤ δ₀ →
      (∫⁻ x : Fin (n+1) → ℝ,
        (preferredFullRightShell d B δB r 0 (Fin.last (n+1))).indicator
          (fun w => ENNReal.ofReal (signedJacobianResolvent η d B ε τ w)) (constrainedAtTotal c x)) ≤
      ENNReal.ofReal (A^n*(C*((n+2:ℕ):ℝ)*Real.sqrt (|d.b+c/((n+2:ℕ):ℝ)|+r+ε)/r*(1+|Real.log ε|))*
        (32*r/Real.sqrt (|d.b+c/((n+2:ℕ):ℝ)|+r+ε))^n) := by
  obtain ⟨A,C,ε₀,τ₀,δ₀,hA,hC,hε₀,hτ₀,hδ₀,hδ₀δ,hfiber⟩ := signed_q20_fiber_lintegral d B
  refine ⟨A,C,ε₀,τ₀,δ₀,hA,hC,hε₀,hτ₀,hδ₀,hδ₀δ,?_⟩
  intro η n ε τ c r δB hε hεr hτ hτr hr hδB hδ
  let S := preferredFullRightShell d B δB r 0 (Fin.last (n+1))
  let G := S.indicator (fun w => ENNReal.ofReal (signedJacobianResolvent η d B ε τ w))
  let t := d.b+c/((n+2:ℕ):ℝ)
  let T := |t|+r+ε
  let L := C*((n+2:ℕ):ℝ)*Real.sqrt T/r*(1+|Real.log ε|)
  let W := preferredShiftedOneBodyBox n d.b t r
  have hG : Measurable G :=
    ((signedJacobianResolvent_continuous η (by omega : 0<n+2) d B hε hτ).measurable.ennreal_ofReal).indicator
      (preferredFullRightShell_isClosed d B δB r 0 (Fin.last (n+1))).measurableSet
  have hc : Continuous (constrainedAtTotal (n := n+1) c) := by unfold constrainedAtTotal; fun_prop
  change (∫⁻ x : Fin (n+1) → ℝ,G (constrainedAtTotal c x)) ≤ _
  rw [constrained_hyperplane_lintegral_cons c G (hG.comp hc.measurable).aemeasurable]
  have hinner (z : Fin n → ℝ) :
      (∫⁻ m : ℝ,G (preferredFiberConfiguration c z m)) ≤
        W.indicator (fun z => ENNReal.ofReal (A^n*(∏ i,preferredOneBodyMajorant ε (z i+d.b))*L)) z := by
    let F := extremeShellFiber (c-∑ i,z i) r (-d.b-δB) B.delta z
    have he : (fun m => G (preferredFiberConfiguration c z m)) =
        F.indicator (fun m => ENNReal.ofReal (signedJacobianResolvent η d B ε τ (preferredFiberConfiguration c z m))) := by
      funext m
      by_cases hm : m∈F
      · have hs := (preferredFullRightShell_fiber_iff d B δB r c m z).2 hm
        exact (Set.indicator_of_mem hs _).trans (Set.indicator_of_mem hm (fun t => ENNReal.ofReal (signedJacobianResolvent η d B ε τ (preferredFiberConfiguration c z t)))).symm
      · have hs := mt (preferredFullRightShell_fiber_iff d B δB r c m z).1 hm
        exact (Set.indicator_of_notMem hs _).trans (Set.indicator_of_notMem hm (fun t => ENNReal.ofReal (signedJacobianResolvent η d B ε τ (preferredFiberConfiguration c z t)))).symm
    rw [he,lintegral_indicator (extremeShellFiber_isClosed _ _ _ _ _).measurableSet]
    have hh := hfiber η n ε τ c r δB 1 hε hεr hτ hτr hr hδB hδ (by norm_num)
      (signedJacobianResolvent η d B ε τ) (Equiv.refl _) z (by intro m _; simp)
    simpa only [Function.comp_def,Equiv.refl_apply,one_mul] using hh
  have hL : 0 ≤ A^n*L := by dsimp [L,T]; positivity
  calc
    _ ≤ ∫⁻ z : Fin n → ℝ,
        W.indicator (fun z => ENNReal.ofReal (A^n*(∏ i,preferredOneBodyMajorant ε (z i+d.b))*L)) z :=
      lintegral_mono hinner
    _ = ∫⁻ z in W,ENNReal.ofReal (A^n*L)*ENNReal.ofReal (∏ i,preferredOneBodyMajorant ε (z i+d.b)) := by
      rw [lintegral_indicator (preferredShiftedOneBodyBox_measurable _ _ _ _)]
      apply lintegral_congr
      intro z
      rw [← ENNReal.ofReal_mul hL]
      congr 1
      ring
    _ = ENNReal.ofReal (A^n*L)*∫⁻ z in W,ENNReal.ofReal (∏ i,preferredOneBodyMajorant ε (z i+d.b)) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (A^n*L)*ENNReal.ofReal ((32*r/Real.sqrt T)^n) := by
      have hh := preferredShiftedOneBodyBox_lintegral n hε hr d.b t
      simpa only [mul_comm] using mul_le_mul_left hh (ENNReal.ofReal (A^n*L))
    _ = _ := by rw [← ENNReal.ofReal_mul hL]


/-- The complete actual shell Jacobian/resolvent bound for every pair of
extreme indices. Every change of eliminated coordinate preserves Lebesgue
measure exactly. -/
theorem signed_shell_jacobian_lintegral (d : PreferredBranchData)
    (B : PreferredCoareaBump d) :
    ∃ A C ε₀ τ₀ δ₀ : ℝ, 0 < A ∧ 0 < C ∧ 0 < ε₀ ∧ 0 < τ₀ ∧ 0 < δ₀ ∧ δ₀ < B.delta ∧
      ∀ η : ℝ, ∀ n : ℕ, ∀ ε τ c r δB : ℝ, 0 < ε → ε < ε₀ → 0 ≤ τ → τ < τ₀ →
      0 < r → 0 < δB → δB ≤ δ₀ → ∀ i j : Fin (n+2),
      (∫⁻ x : Fin (n+1) → ℝ,
        (preferredFullRightShell d B δB r i j).indicator
          (fun w => ENNReal.ofReal (signedJacobianResolvent η d B ε τ w)) (constrainedAtTotal c x)) ≤
      ENNReal.ofReal (A^n*(C*((n+2:ℕ):ℝ)*Real.sqrt (|d.b+c/((n+2:ℕ):ℝ)|+r+ε)/r*(1+|Real.log ε|))*
        (32*r/Real.sqrt (|d.b+c/((n+2:ℕ):ℝ)|+r+ε))^n) := by
  obtain ⟨A,C,ε₀,τ₀,δ₀,hA,hC,hε₀,hτ₀,hδ₀,hδ₀δ,hcanon⟩ := signed_canonical_shell_jacobian_lintegral d B
  refine ⟨A,C,ε₀,τ₀,δ₀,hA,hC,hε₀,hτ₀,hδ₀,hδ₀δ,?_⟩
  intro η n ε τ c r δB hε hεr hτ hτr hr hδB hδ i j
  by_cases hij : i=j
  · subst j
    have hs : preferredFullRightShell d B δB r i i=∅ := by
      apply Set.eq_empty_of_forall_notMem
      intro w hw
      have hh := hw.2.2.1
      simp only [sub_self] at hh
      exact (not_le_of_gt hr) hh
    rw [hs]
    simp only [Set.indicator_empty,lintegral_zero]
    exact bot_le
  · obtain ⟨e,hi,hj⟩ := preferred_extreme_permutation i j hij
    have hi' : e.symm 0=i := e.injective (by simp only [Equiv.apply_symm_apply,hi])
    have hj' : e.symm (Fin.last (n+1))=j := e.injective (by simp only [Equiv.apply_symm_apply,hj])
    have he := signed_full_shell_indicator_permutation η d B δB r ε τ c 0 (Fin.last (n+1)) e
    rw [hi',hj'] at he
    rw [he]
    exact hcanon η n ε τ c r δB hε hεr hτ hτr hr hδB hδ

/-- Integrated q20 on the actual affine shell from its literal pointwise
majorant. This theorem proves the complete measure conversion and integration;
it does not assume a shell estimate or a tail estimate. -/
theorem signed_shell_q20_lintegral (d : PreferredBranchData)
    (B : PreferredCoareaBump d) :
    ∃ A C ε₀ τ₀ δ₀ : ℝ, 0 < A ∧ 0 < C ∧ 0 < ε₀ ∧ 0 < τ₀ ∧ 0 < δ₀ ∧ δ₀ < B.delta ∧
      ∀ η : ℝ, ∀ n : ℕ, ∀ ε τ c r δB K : ℝ, 0 < ε → ε < ε₀ → 0 ≤ τ → τ < τ₀ →
      0 < r → 0 < δB → δB ≤ δ₀ → 0 ≤ K → ∀ i j : Fin (n+2),
      ∀ f : (Fin (n+2) → ℝ) → ℝ,
      (∀ x : Fin (n+1) → ℝ, constrainedAtTotal c x∈preferredFullRightShell d B δB r i j →
        f (constrainedAtTotal c x) ≤ K*signedJacobianResolvent η d B ε τ (constrainedAtTotal c x)) →
      (∫⁻ x : Fin (n+1) → ℝ,
        (preferredFullRightShell d B δB r i j).indicator
          (fun w => ENNReal.ofReal (f w)) (constrainedAtTotal c x)) ≤
      ENNReal.ofReal (K*(A^n*(C*((n+2:ℕ):ℝ)*Real.sqrt (|d.b+c/((n+2:ℕ):ℝ)|+r+ε)/r*(1+|Real.log ε|))*
        (32*r/Real.sqrt (|d.b+c/((n+2:ℕ):ℝ)|+r+ε))^n)) := by
  obtain ⟨A,C,ε₀,τ₀,δ₀,hA,hC,hε₀,hτ₀,hδ₀,hδ₀δ,hjac⟩ := signed_shell_jacobian_lintegral d B
  refine ⟨A,C,ε₀,τ₀,δ₀,hA,hC,hε₀,hτ₀,hδ₀,hδ₀δ,?_⟩
  intro η n ε τ c r δB K hε hεr hτ hτr hr hδB hδ hK i j f hpoint
  let S := preferredFullRightShell d B δB r i j
  let J := fun x : Fin (n+1) → ℝ =>
    S.indicator (fun w => ENNReal.ofReal (signedJacobianResolvent η d B ε τ w)) (constrainedAtTotal c x)
  calc
    _ ≤ ∫⁻ x : Fin (n+1) → ℝ,ENNReal.ofReal K*J x := by
      apply lintegral_mono
      intro x
      by_cases hx : constrainedAtTotal c x∈S
      · dsimp [J]
        rw [Set.indicator_of_mem hx,Set.indicator_of_mem hx,← ENNReal.ofReal_mul hK]
        exact ENNReal.ofReal_le_ofReal (hpoint x hx)
      · dsimp [J]
        rw [Set.indicator_of_notMem hx,Set.indicator_of_notMem hx,mul_zero]
    _ = ENNReal.ofReal K*∫⁻ x : Fin (n+1) → ℝ,J x :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal K*ENNReal.ofReal
        (A^n*(C*((n+2:ℕ):ℝ)*Real.sqrt (|d.b+c/((n+2:ℕ):ℝ)|+r+ε)/r*(1+|Real.log ε|))*
          (32*r/Real.sqrt (|d.b+c/((n+2:ℕ):ℝ)|+r+ε))^n) := by
      have hh := hjac η n ε τ c r δB hε hεr hτ hτr hr hδB hδ i j
      simpa only [mul_comm] using mul_le_mul_left hh (ENNReal.ofReal K)
    _ = _ := by rw [← ENNReal.ofReal_mul hK]



end
end IsingBulk.HT22.Geometry
