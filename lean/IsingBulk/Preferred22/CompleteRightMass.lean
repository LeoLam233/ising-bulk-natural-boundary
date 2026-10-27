import IsingBulk.Preferred22.FiniteRightMass

/-! The complete actual right absolute mass above the first singular order.
The finite block uses its full Vandermonde shells and the infinite block uses
q28; both are summed on their literal positive even particle indices. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ENNReal

/-- Exact finite-plus-infinite right mass summation. The source shell
premises are visible and no all-order integrated mass estimate is assumed. -/
theorem preferred_complete_right_mass_tail_of_shells (d : PreferredBranchData)
    (B : PreferredCoareaBump d) {δB τ ε₀ : ℝ} (rcut : ℝ → ℝ)
    (hcut : PreferredRightCutoffData d B δB rcut) (Nstar k : ℕ)
    (hNstar : 2≤Nstar) (hEvenStar : Even Nstar) (hk : 2*k+2=Nstar^2)
    (hq28 : PreferredAllDiameterShellBound d B δB τ ε₀ preferredPopulationCutoff rcut k)
    (hfinite : PreferredFiniteBlockShellBound d B δB τ ε₀ preferredPopulationCutoff rcut Nstar k) :
    PreferredRightAbsoluteMassTail d B τ ε₀ rcut Nstar k := by
  classical
  intro j hj
  obtain ⟨A,hA,hlarge⟩ := preferred_complete_right_mass_tail_of_q28 d B rcut hcut k hq28 j hj
  have hchoices (m : Fin (k+2)) : ∃ D : ℝ,0<D ∧ ∀ ε : ℝ,0<ε → ε<ε₀ →
      preferredRightAbsoluteMassTailTerms d B τ rcut Nstar j ε m≤D*(1+|Real.log ε|) := by
    by_cases hNs : Nstar<2*(m.val+1)
    · have hNl : Nstar+2≤2*m.val+1+1 := by
        obtain ⟨a,ha⟩ := hEvenStar
        omega
      have hNu : 2*m.val+1+1≤2*k+4 := by omega
      have hEven : Even (2*m.val+1+1) := ⟨m.val+1,by omega⟩
      obtain ⟨D,hD,hbound⟩ := preferred_finite_right_absolute_bound_of_shells d B rcut hcut Nstar k
        hNstar hk hq28 hfinite (2*m.val+1) hNl hNu hEven j hj
      refine ⟨D,hD,?_⟩
      intro ε hε hεr
      simpa only [preferredRightAbsoluteMassTailTerms,ite_eq_left hNs] using (hbound ε hε hεr).2
    · refine ⟨1,zero_lt_one,?_⟩
      intro ε _hε _hεr
      simp only [preferredRightAbsoluteMassTailTerms,ite_eq_right hNs,one_mul]
      positivity
  choose D hD hboundD using hchoices
  let P := 1+∑ m : Fin (k+2),D m
  have hP : 0<P := by
    have hs : 0≤∑ m : Fin (k+2),D m := Finset.sum_nonneg (fun m _ => (hD m).le)
    dsimp [P]
    linarith
  have hDP (m : Fin (k+2)) : D m≤P := by
    have hh := Finset.single_le_sum (fun a (_ : a∈(Finset.univ : Finset (Fin (k+2)))) => (hD a).le)
      (Finset.mem_univ m)
    dsimp [P]
    linarith
  let E := fun m : ℕ => if m<k+2 then P else 0
  have hE : Summable E := summable_of_ne_finset_zero (s := Finset.range (k+2)) (fun m hm => by
    rw [Finset.mem_range] at hm
    exact ite_eq_right hm)
  have hEn (m : ℕ) : 0≤E m := by dsimp [E]; split_ifs <;> positivity
  have hsumE : 0≤∑' m,E m := tsum_nonneg hEn
  refine ⟨A+∑' m,E m,add_pos_of_pos_of_nonneg hA hsumE,?_⟩
  intro ε hε hεr
  obtain ⟨hLs,hLb⟩ := hlarge ε hε hεr
  let H := 1+|Real.log ε|
  have hH : 0≤H := by dsimp [H]; positivity
  have hn (m : ℕ) : 0≤preferredRightAbsoluteMassTailTerms d B τ rcut Nstar j ε m := by
    unfold preferredRightAbsoluteMassTailTerms
    split_ifs
    · exact preferredRightAbsoluteTransportMass_nonneg d B τ rcut _ j ε
    · exact le_rfl
  have hLn (m : ℕ) : 0≤preferredRightLargeMassTerms d B τ rcut k j ε m := by
    unfold preferredRightLargeMassTerms
    split_ifs
    · exact preferredRightAbsoluteTransportMass_nonneg d B τ rcut _ j ε
    · exact le_rfl
  have hle (m : ℕ) : preferredRightAbsoluteMassTailTerms d B τ rcut Nstar j ε m≤
      preferredRightLargeMassTerms d B τ rcut k j ε m+H*E m := by
    by_cases hN : Nstar<2*(m+1)
    · by_cases hL : 2*k+4<2*(m+1)
      · simp only [preferredRightAbsoluteMassTailTerms,ite_eq_left hN,
          preferredRightLargeMassTerms,ite_eq_left hL]
        exact le_add_of_nonneg_right (mul_nonneg hH (hEn m))
      · have hm : m<k+2 := by omega
        have hb := hboundD ⟨m,hm⟩ ε hε hεr
        have hDPm := hDP ⟨m,hm⟩
        dsimp [E]
        rw [ite_eq_left hm]
        calc
          _ ≤ D ⟨m,hm⟩*H := hb
          _ ≤ P*H := mul_le_mul_of_nonneg_right hDPm hH
          _ ≤ preferredRightLargeMassTerms d B τ rcut k j ε m+H*P := by
            nlinarith [hLn m]
    · simp only [preferredRightAbsoluteMassTailTerms,ite_eq_right hN]
      exact add_nonneg (hLn m) (mul_nonneg hH (hEn m))
  have hmaj : Summable (fun m => preferredRightLargeMassTerms d B τ rcut k j ε m+H*E m) :=
    hLs.add (hE.mul_left H)
  have hs := hmaj.of_nonneg_of_le hn hle
  refine ⟨hs,?_⟩
  calc
    _ ≤ ∑' m,(preferredRightLargeMassTerms d B τ rcut k j ε m+H*E m) :=
      Summable.tsum_le_tsum hle hs hmaj
    _ = (∑' m,preferredRightLargeMassTerms d B τ rcut k j ε m)+H*(∑' m,E m) := by
      rw [hLs.tsum_add (hE.mul_left H),tsum_mul_left]
    _ ≤ A*H+H*(∑' m,E m) := add_le_add hLb le_rfl
    _ = _ := by ring

end
end IsingBulk.Preferred22
