import IsingBulk.HT22.Geometry.SignedShellCover

namespace IsingBulk.HT22.Geometry
noncomputable section
open Set MeasureTheory IsingBulk.Preferred22
open scoped BigOperators ENNReal

/-- Exact equality in the original eliminated-angle Haar variables. -/
theorem signed_shell_lintegral_eq_affine {n : ℕ} (a : ℝ) (d : PreferredBranchData)
    (B : PreferredCoareaBump d) {δB : ℝ} (hδB : δB<B.delta)
    (r : ℝ) (l : ℤ) (i j : Fin (n+1)) (f : (Fin (n+1) → ℝ) → ℝ≥0∞) :
    (∫⁻ x in signedRightShell a d B δB r l i j,
      f (preferredLiftedAngles B.delta (constrainedAtTotal a x))) =
    ∫⁻ x : Fin n → ℝ,(preferredFullRightShell d B δB r i j).indicator f
      (constrainedAtTotal (a+2*Real.pi*(l:ℝ)) x) := by
  rw [← lintegral_indicator (signedRightShell_isClosed a d B hδB r l i j).measurableSet]
  apply lintegral_congr
  intro x
  by_cases hx : x∈signedRightShell a d B δB r l i j
  · have he := signed_lift_eq_affine_on_right d B hδB a x hx.1 hx.2.1.1 hx.2.2
    have hm : constrainedAtTotal (a+2*Real.pi*(l:ℝ)) x∈preferredFullRightShell d B δB r i j := by
      simpa only [he] using hx.2.1
    simp only [Set.indicator_of_mem hx,Set.indicator_of_mem hm,he]
  · have hm : constrainedAtTotal (a+2*Real.pi*(l:ℝ)) x∉preferredFullRightShell d B δB r i j := by
      simpa only [signedRightShell_eq_affine a d B hδB r l i j,Set.mem_preimage] using hx
    simp only [Set.indicator_of_notMem hx,Set.indicator_of_notMem hm]

/-- The signed physical shell cost in actual torus variables, with the
same one affine chart and exactly N−3 powers of the normalized diameter. -/
theorem signed_actual_shell_scale_lintegral (d : PreferredBranchData) (B : PreferredCoareaBump d) :
    ∃ A C ε₀ τ₀ δ₀ : ℝ, 0<A ∧ 0<C ∧ 0<ε₀ ∧ 0<τ₀ ∧ 0<δ₀ ∧ δ₀<B.delta ∧
      ∀ a η : ℝ, ∀ m : ℕ, ∀ ε τ r δB K : ℝ, 0<ε → ε<ε₀ → 0≤τ → τ<τ₀ →
      0<r → 0<δB → δB≤δ₀ → 0≤K → ∀ l : ℤ, ∀ i j : Fin (m+3),
      ∀ f : (Fin (m+3) → ℝ) → ℝ,
      (∀ x : Fin (m+2) → ℝ, constrainedAtTotal (a+2*Real.pi*(l:ℝ)) x∈preferredFullRightShell d B δB r i j →
        f (constrainedAtTotal (a+2*Real.pi*(l:ℝ)) x)≤
          K*signedJacobianResolvent η d B ε τ (constrainedAtTotal (a+2*Real.pi*(l:ℝ)) x)) →
      (∫⁻ x in signedRightShell a d B δB r l i j,
        ENNReal.ofReal (f (preferredLiftedAngles B.delta (constrainedAtTotal a x)))) ≤
      ENNReal.ofReal (K*C*((m+3:ℕ):ℝ)*A^(m+1)*
        (r/Real.sqrt (|d.b+(a+2*Real.pi*(l:ℝ))/((m+3:ℕ):ℝ)|+r+ε))^m*(1+|Real.log ε|)) := by
  obtain ⟨A,C,e,t,δ,hA,hC,he,ht,hδ,hδB,hbound⟩ := signed_shell_scale_lintegral d B
  refine ⟨A,C,e,t,δ,hA,hC,he,ht,hδ,hδB,?_⟩
  intro a η m ε τ r δB K hε hεr hτ hτr hr hδB' hδ' hK l i j f hf
  rw [signed_shell_lintegral_eq_affine (n := m+2) a d B (hδ'.trans_lt hδB) r l i j (fun w => ENNReal.ofReal (f w))]
  exact hbound η m ε τ (a+2*Real.pi*(l:ℝ)) r δB K hε hεr hτ hτr hr hδB' hδ' hK i j f hf

end
end IsingBulk.HT22.Geometry
