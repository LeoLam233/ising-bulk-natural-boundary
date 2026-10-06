import IsingBulk.Tail.AllBranchExteriorCoordinatePhase
import IsingBulk.Tail.CompactPairCoarea

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Branch Set
open scoped BigOperators

def allBranchExteriorCoordinateCell {N : ℕ} (p q : Fin N) (r a σ : ℝ) : Set (Fin N → ℝ) :=
  Icc (fun _ => 0) (fun _ => r) ∩ ({u | a ≤ u q} ∩ {u | σ ≤ u q-u p})

theorem allBranchExterior_coordinate_cell_convex {N : ℕ} (p q : Fin N) (r a σ : ℝ) :
    Convex ℝ (allBranchExteriorCoordinateCell p q r a σ) := by
  apply (convex_Icc _ _).inter
  apply (convex_halfSpace_ge (LinearMap.proj q : (Fin N → ℝ) →ₗ[ℝ] ℝ).isLinear a).inter
  exact convex_halfSpace_ge ((LinearMap.proj q : (Fin N → ℝ) →ₗ[ℝ] ℝ)-(LinearMap.proj p : (Fin N → ℝ) →ₗ[ℝ] ℝ)).isLinear σ

theorem allBranchExterior_coordinate_cell_measurable {N : ℕ} (p q : Fin N) (r a σ : ℝ) :
    MeasurableSet (allBranchExteriorCoordinateCell p q r a σ) := by
  unfold allBranchExteriorCoordinateCell
  measurability

theorem allBranchExterior_coordinate_injective {N : ℕ} {d : LocalBranchData}
    (B : BranchEstimates d) (ε a σ : ℝ) (p q : Fin N) (hpq : p ≠ q)
    (hε : 0 < ε) (hεr : ε ≤ B.ε₀) (ha : 0 < a) (hσ : 0 < σ)
    (hsmall₁ : B.original.separationThreshold*ε ≤ a) (hsmall₂ : 2*B.original.C₀*ε ≤ a) :
    InjOn (allBranchExteriorCoordinateMap d ε p q) (allBranchExteriorCoordinateCell p q B.r a σ) := by
  intro x hx y hy he
  obtain ⟨hF,hG,hspect⟩ := twoPhaseUpdate_equal_data hpq he
  have hsum : ∑ i, x i=∑ i, y i := by
    change (∑ i, x i)-(N:ℝ)*d.thetaB=(∑ i, y i)-(N:ℝ)*d.thetaB at hF
    linarith
  have hd (u : Fin N → ℝ) (hu : u ∈ allBranchExteriorCoordinateCell p q B.r a σ) :=
    allBranchExterior_total_hasFDerivAt B ε hε hεr u (fun i => ⟨hu.1.1 i,hu.1.2 i⟩)
  apply fixed_sum_pair_phase_injective _ (allBranchExterior_coordinate_cell_convex p q B.r a σ)
    (allBranchExteriorTotalPhase d ε) p q hpq (fun u hu => (hd u hu).differentiableAt) _
    hx hy hsum hG hspect
  intro u hu
  rw [(hd u hu).fderiv]
  change 0 < allBranchExteriorTotalDerivative d ε u (pairDirection p q)
  rw [allBranchExterior_total_pair_direction]
  exact (allBranchExterior_positive_slope_ratio B ε a σ (u p) (u q) hε hεr ha hσ hsmall₁ hsmall₂
    (hu.1.1 p) (hu.1.2 q) hu.2.1 hu.2.2).1

theorem allBranchExterior_coordinate_image_on_subradius {N : ℕ} {d : LocalBranchData}
    (B : BranchEstimates d) (ε a σ R : ℝ) (p q : Fin N) (hε : 0 < ε) (hεr : ε ≤ B.ε₀)
    (hR : 0 ≤ R) (hRB : R ≤ B.r) (hrπ : R ≤ Real.pi) :
    allBranchExteriorCoordinateMap d ε p q '' allBranchExteriorCoordinateCell p q R a σ ⊆
      phaseSpectatorBox p q R := by
  rintro _ ⟨u,hu,rfl⟩
  have hF : |(∑ i, u i)-(N:ℝ)*d.thetaB| ≤ (N:ℝ)*Real.pi := by
    have he : (∑ i, u i)-(N:ℝ)*d.thetaB=∑ i, (u i-d.thetaB) := by simp [Finset.sum_sub_distrib]
    rw [he]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
      (show |u i-d.thetaB| ≤ Real.pi by
        rw [abs_le]
        constructor <;> linarith [hu.1.1 i,hu.1.2 i,d.thetaB_pos,d.thetaB_lt]))
    simpa using hh
  have hφ (i : Fin N) : 0 ≤ originalRealPhase d ε (u i) ∧ originalRealPhase d ε (u i) ≤ Real.pi/2 := by
    obtain ⟨hr,hi⟩ := B.quadrant ε (u i) hε hεr (by simpa [abs_of_nonneg (hu.1.1 i)] using (hu.1.2 i).trans hRB)
    have hh := lowerArccos_sheet _ hr hi
    exact ⟨hh.2.1.le,hh.2.2.1.le⟩
  have hG : |allBranchExteriorTotalPhase d ε u| ≤ (N:ℝ)*Real.pi := by
    unfold allBranchExteriorTotalPhase
    rw [abs_of_nonneg (Finset.sum_nonneg (fun i _ => (hφ i).1))]
    have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => (hφ i).2)
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hh
    have hn : (0:ℝ) ≤ N := Nat.cast_nonneg _
    nlinarith [Real.pi_pos]
  constructor <;> intro i
  all_goals
    by_cases hip : i=p
    · subst i
      first | simpa [allBranchExteriorCoordinateMap,twoPhaseUpdate] using (abs_le.mp hF).1
            | simpa [allBranchExteriorCoordinateMap,twoPhaseUpdate] using (abs_le.mp hF).2
    · by_cases hiq : i=q
      · subst i
        first | simpa [allBranchExteriorCoordinateMap,twoPhaseUpdate,hip] using (abs_le.mp hG).1
              | simpa [allBranchExteriorCoordinateMap,twoPhaseUpdate,hip] using (abs_le.mp hG).2
      · simp only [allBranchExteriorCoordinateMap,twoPhaseUpdate,hip,hiq,ite_false,or_self]
        first | linarith [hu.1.1 i,hR] | exact hu.1.2 i


theorem allBranchExterior_coordinate_image {N : ℕ} {d : LocalBranchData}
    (B : BranchEstimates d) (ε a σ : ℝ) (p q : Fin N) (hε : 0 < ε) (hεr : ε ≤ B.ε₀)
    (hrπ : B.r ≤ Real.pi) :
    allBranchExteriorCoordinateMap d ε p q '' allBranchExteriorCoordinateCell p q B.r a σ ⊆
      phaseSpectatorBox p q B.r :=
  allBranchExterior_coordinate_image_on_subradius B ε a σ B.r p q hε hεr B.r_pos.le le_rfl hrπ

end
end IsingBulk.Tail
