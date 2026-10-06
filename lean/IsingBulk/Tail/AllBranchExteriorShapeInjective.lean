import IsingBulk.Tail.AllBranchExteriorShapePhase

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Branch Set
open scoped BigOperators

def allBranchExteriorShapeRegion {N : ℕ} (a r : ℝ) (ω : Fin N → ℝ) : Set (ℝ × ℝ) :=
  {x | 0 < x.2 ∧ a ≤ x.1 ∧ x.1 ≤ r ∧ ∀ i, a ≤ x.1+x.2*ω i ∧ x.1+x.2*ω i ≤ r}

def allBranchExteriorShapeMap {N : ℕ} (d : LocalBranchData) (ε : ℝ)
    (ω : Fin N → ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  ((N:ℝ)*x.1,allBranchExteriorShapePhase d ε x.1 ω x.2)

theorem allBranchExterior_shape_strictAnti {N : ℕ} {d : LocalBranchData}
    (B : BranchEstimates d) (ε t a ρ₁ ρ₂ : ℝ) (ω : Fin N → ℝ)
    (hε : 0 < ε) (hεr : ε ≤ B.ε₀) (ha : B.original.C₀*ε ≤ a)
    (hzero : ∑ i, ω i=0) (hunit : ∑ i, (ω i)^2=1)
    (h₁ : (t,ρ₁) ∈ allBranchExteriorShapeRegion a B.r ω)
    (h₂ : (t,ρ₂) ∈ allBranchExteriorShapeRegion a B.r ω) (hρ : ρ₁ < ρ₂) :
    allBranchExteriorShapePhase d ε t ω ρ₂ < allBranchExteriorShapePhase d ε t ω ρ₁ := by
  have hcell : ∀ ρ ∈ Icc ρ₁ ρ₂, ∀ i,
      B.original.C₀*ε ≤ t+ρ*ω i ∧ t+ρ*ω i ≤ B.r := by
    intro ρ hρi i
    by_cases hw : 0 ≤ ω i
    · constructor
      · exact ha.trans ((h₁.2.2.2 i).1.trans (by nlinarith [hρi.1]))
      · exact (show t+ρ*ω i ≤ t+ρ₂*ω i by nlinarith [hρi.2]).trans (h₂.2.2.2 i).2
    · have hw' : ω i ≤ 0 := le_of_not_ge hw
      constructor
      · exact ha.trans ((h₂.2.2.2 i).1.trans (by nlinarith [hρi.2]))
      · exact (show t+ρ*ω i ≤ t+ρ₁*ω i by nlinarith [hρi.1]).trans (h₁.2.2.2 i).2
  have hmono : StrictAntiOn (allBranchExteriorShapePhase d ε t ω) (Icc ρ₁ ρ₂) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
    · intro ρ hρi
      exact (allBranchExterior_shape_hasDerivAt B ε t ρ ω hε hεr
        (fun i => ⟨(mul_pos B.original.C₀_pos hε).le.trans (hcell ρ hρi i).1,
          (hcell ρ hρi i).2⟩)).continuousAt.continuousWithinAt
    · intro ρ hρi
      have hmem := interior_subset hρi
      have hρp : 0 < ρ := h₁.1.trans_le hmem.1
      have hh := allBranchExterior_shape_radial_bound B ε t ρ ω hε hεr hρp.le hzero hunit
        (ha.trans h₁.2.1) h₁.2.2.1 (hcell ρ hmem)
      have hp := mul_pos (allBranchExterior_curvature_pos B) hρp
      linarith
  exact hmono (left_mem_Icc.mpr hρ.le) (right_mem_Icc.mpr hρ.le) hρ

theorem allBranchExterior_shape_injective {N : ℕ} {d : LocalBranchData}
    (B : BranchEstimates d) (ε a : ℝ) (ω : Fin N → ℝ) (hN : 0 < N)
    (hε : 0 < ε) (hεr : ε ≤ B.ε₀) (ha : B.original.C₀*ε ≤ a)
    (hzero : ∑ i, ω i=0) (hunit : ∑ i, (ω i)^2=1) :
    InjOn (allBranchExteriorShapeMap d ε ω) (allBranchExteriorShapeRegion a B.r ω) := by
  intro x hx y hy he
  have hNr : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have ht : x.1=y.1 := mul_left_cancel₀ hNr (congrArg Prod.fst he)
  have hg : allBranchExteriorShapePhase d ε x.1 ω x.2=
      allBranchExteriorShapePhase d ε y.1 ω y.2 := congrArg Prod.snd he
  have hx' : (x.1,y.2) ∈ allBranchExteriorShapeRegion a B.r ω := by simpa [ht] using hy
  have hρ : x.2=y.2 := by
    rcases lt_trichotomy x.2 y.2 with h|h|h
    · have hh := allBranchExterior_shape_strictAnti B ε x.1 a x.2 y.2 ω hε hεr ha hzero hunit hx hx' h
      rw [← ht] at hg
      rw [hg] at hh
      exact False.elim (lt_irrefl _ hh)
    · exact h
    · have hh := allBranchExterior_shape_strictAnti B ε x.1 a y.2 x.2 ω hε hεr ha hzero hunit hx' hx h
      rw [← ht] at hg
      rw [hg] at hh
      exact False.elim (lt_irrefl _ hh)
  exact Prod.ext ht hρ

end
end IsingBulk.Tail
