import IsingBulk.Joint.FormFactors.ActualFamilyLeadingData

/-! The actual complex-ratio physical tails on a common closed lambda disk.
The physical-side condition in the raw mixed-tail estimate is discharged from
the constructed same-component geometry, before any derivative order. -/
namespace IsingBulk.Joint.FormFactors
noncomputable section
open Set Filter Metric
open scoped Topology
namespace ComplexRatioFamily
variable {b : ℝ} {z₀ lam₀ : ℂ}

/-- All mixed jets of the literal high-temperature normalized particle tails
have common summable envelopes on one genuinely complex-lambda polydisk. -/
theorem actual_high_ratio_mixed_tails
    (F : ComplexRatioFamily (Transverse.positiveParameter (b:ℂ)) highPrefactor 1 z₀ lam₀)
    (hK : (z₀,lam₀*z₀)∈closure highDomain) (hp : p (z₀,lam₀*z₀)^2≠1)
    (hS : S (z₀,lam₀*z₀)≠0) (hB : 0<(transferB (z₀,lam₀*z₀)).im) (hb : |b|<1) :
    ∃ρ : ℝ,0<ρ ∧ ρ≤F.radius ∧
      (∀lam∈closedBall lam₀ ρ,∀u : ℂ,‖u‖<ρ → 0<u.im → F.coupling (u,lam)∈highDomain) ∧
      ∀j : ℕ,∃G : ℕ→ℝ,Summable G ∧ (∀k,0≤G k) ∧
        ∀lam∈closedBall lam₀ ρ,∀u : ℂ,‖u‖<ρ → 0<u.im → ∀k : ℕ,
          ‖iteratedFDeriv ℂ j (F.actualFamilyOddTerm (j+2+k)) (u,lam)‖≤G k := by
  obtain ⟨r,hr,hrF,hdata,_⟩ := positive_ratio_common_high_side F hK hp hS hB hb
  obtain ⟨δ,hδ,htails⟩ := F.actual_complex_ratio_full_coefficient_mixed_tails hb
  let ρ := min r (δ/2)
  have hρ : 0<ρ := lt_min hr (half_pos hδ)
  have hρr : ρ≤r := min_le_left _ _
  have hρδ : ρ<δ := (min_le_right _ _).trans_lt (half_lt_self hδ)
  have hside (lam : ℂ) (hl : lam∈closedBall lam₀ ρ) (u : ℂ) (hu : ‖u‖<ρ) (hi : 0<u.im) :
      F.coupling (u,lam)∈highDomain :=
    (hdata u lam (hu.le.trans hρr) ((show ‖lam-lam₀‖≤ρ by simpa only [mem_closedBall,dist_eq_norm] using hl).trans hρr)).2.2.2.2.mpr hi
  refine ⟨ρ,hρ,hρr.trans hrF,hside,?_⟩
  intro j
  obtain ⟨G,H,hG,_hH,hG0,_hH0,hbound⟩ := htails j
  refine ⟨G,hG,hG0,?_⟩
  intro lam hl u hu hi k
  have hball : (u,lam)∈ball (0,lam₀) δ := by
    rw [mem_ball,Prod.dist_eq,max_lt_iff,dist_zero_right]
    exact ⟨hu.trans hρδ,(show dist lam lam₀≤ρ from hl).trans_lt hρδ⟩
  exact (hbound (u,lam) hball hi (Or.inl (hside lam hl u hu hi)) k).1

/-- Low-temperature counterpart, with the exact positive-even integer p
powers and the physical low-temperature prefactor. -/
theorem actual_low_ratio_mixed_tails
    (F : ComplexRatioFamily (Transverse.positiveParameter (b:ℂ)) lowPrefactor 1 z₀ lam₀)
    (hK : (z₀,lam₀*z₀)∈closure lowDomain) (hp : p (z₀,lam₀*z₀)^2≠1)
    (hS : S (z₀,lam₀*z₀)≠0) (hB : 0<(transferB (z₀,lam₀*z₀)).im) (hb : |b|<1) :
    ∃ρ : ℝ,0<ρ ∧ ρ≤F.radius ∧
      (∀lam∈closedBall lam₀ ρ,∀u : ℂ,‖u‖<ρ → 0<u.im → F.coupling (u,lam)∈lowDomain) ∧
      ∀j : ℕ,∃G : ℕ→ℝ,Summable G ∧ (∀k,0≤G k) ∧
        ∀lam∈closedBall lam₀ ρ,∀u : ℂ,‖u‖<ρ → 0<u.im → ∀k : ℕ,
          ‖iteratedFDeriv ℂ j (F.actualFamilyEvenTerm (j+1+k)) (u,lam)‖≤G k := by
  obtain ⟨r,hr,hrF,hdata,_⟩ := positive_ratio_common_low_side F hK hp hS hB hb
  obtain ⟨δ,hδ,htails⟩ := F.actual_complex_ratio_full_coefficient_mixed_tails hb
  let ρ := min r (δ/2)
  have hρ : 0<ρ := lt_min hr (half_pos hδ)
  have hρr : ρ≤r := min_le_left _ _
  have hρδ : ρ<δ := (min_le_right _ _).trans_lt (half_lt_self hδ)
  have hside (lam : ℂ) (hl : lam∈closedBall lam₀ ρ) (u : ℂ) (hu : ‖u‖<ρ) (hi : 0<u.im) :
      F.coupling (u,lam)∈lowDomain :=
    (hdata u lam (hu.le.trans hρr) ((show ‖lam-lam₀‖≤ρ by simpa only [mem_closedBall,dist_eq_norm] using hl).trans hρr)).2.2.2.2.mpr hi
  refine ⟨ρ,hρ,hρr.trans hrF,hside,?_⟩
  intro j
  obtain ⟨G,H,_hG,hH,_hG0,hH0,hbound⟩ := htails j
  refine ⟨H,hH,hH0,?_⟩
  intro lam hl u hu hi k
  have hball : (u,lam)∈ball (0,lam₀) δ := by
    rw [mem_ball,Prod.dist_eq,max_lt_iff,dist_zero_right]
    exact ⟨hu.trans hρδ,(show dist lam lam₀≤ρ from hl).trans_lt hρδ⟩
  exact (hbound (u,lam) hball hi (Or.inr (hside lam hl u hu hi)) k).2

end ComplexRatioFamily
end
end IsingBulk.Joint.FormFactors
