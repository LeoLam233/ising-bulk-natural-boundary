import IsingBulk.Tail.AllBranchExteriorPositiveMaster

/-! A positive collision power absorbs the extreme-pair Jacobian loss.
The positive-coordinate cell has no fixed lower gap; injectivity is recovered
from the existing separated cells for each pair of points. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Branch Set MeasureTheory
open scoped BigOperators

def allBranchExteriorPositiveGapCell {N : ℕ} (p q : Fin N) (R a D : ℝ) : Set (Fin N → ℝ) :=
  allBranchExteriorCoordinateCell p q R a 0 ∩ {u | 0 < u q-u p ∧ u q-u p ≤ D}

theorem allBranchExterior_positive_gap_cell_measurable {N : ℕ} (p q : Fin N) (R a D : ℝ) :
    MeasurableSet (allBranchExteriorPositiveGapCell p q R a D) := by
  unfold allBranchExteriorPositiveGapCell allBranchExteriorCoordinateCell
  measurability

theorem allBranchExterior_positive_cost_nonneg {d : LocalBranchData} (B : BranchEstimates d)
    {a D : ℝ} (ha : 0 < a) (hD : 0 < D) : 0 ≤ allBranchExteriorPositiveCost B a D := by
  have hk := B.original.k_pos
  have hA := B.original.a_pos
  unfold allBranchExteriorPositiveCost
  positivity

theorem allBranchExterior_positive_power_absorption {d : LocalBranchData} (B : BranchEstimates d)
    {a δ D : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hδD : δ ≤ D) (P : ℕ) :
    δ^(P+1)*allBranchExteriorPositiveCost B a δ ≤
      D^(P+1)*allBranchExteriorPositiveCost B a D := by
  let A := (B.original.C^2/min (B.original.k/4) (B.original.a/2))/Real.sqrt a
  let C := (2*B.original.C^2/B.original.k)*Real.sqrt B.r
  have hk := B.original.k_pos
  have hA' := B.original.a_pos
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have he (x : ℝ) (hx : 0 < x) :
      x^(P+1)*(A+C/x)=A*x^(P+1)+C*x^P := by
    rw [pow_succ]
    field_simp
  change δ^(P+1)*(A+C/δ) ≤ D^(P+1)*(A+C/D)
  rw [he δ hδ,he D (hδ.trans_le hδD)]
  exact add_le_add
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hδ.le hδD (P+1)) hA)
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hδ.le hδD P) hC)

theorem allBranchExterior_positive_gap_injective {N : ℕ} {d : LocalBranchData}
    (B : BranchEstimates d) (ε a D R : ℝ) (p q : Fin N) (hpq : p ≠ q)
    (hε : 0 < ε) (hεr : ε ≤ B.ε₀) (ha : 0 < a) (hR : R ≤ B.r)
    (hsmall₁ : B.original.separationThreshold*ε ≤ a) (hsmall₂ : 2*B.original.C₀*ε ≤ a) :
    InjOn (allBranchExteriorCoordinateMap d ε p q) (allBranchExteriorPositiveGapCell p q R a D) := by
  intro x hx y hy he
  let σ := min (x q-x p) (y q-y p)
  have hσ : 0 < σ := lt_min hx.2.1 hy.2.1
  have hx' : x ∈ allBranchExteriorCoordinateCell p q B.r a σ :=
    ⟨⟨hx.1.1.1,fun i => (hx.1.1.2 i).trans hR⟩,hx.1.2.1,
      show σ ≤ x q-x p from min_le_left _ _⟩
  have hy' : y ∈ allBranchExteriorCoordinateCell p q B.r a σ :=
    ⟨⟨hy.1.1.1,fun i => (hy.1.1.2 i).trans hR⟩,hy.1.2.1,
      show σ ≤ y q-y p from min_le_right _ _⟩
  exact allBranchExterior_coordinate_injective B ε a σ p q hpq hε hεr ha hσ hsmall₁ hsmall₂ hx' hy' he

/-- The true two-kernel integral is bounded with the collision power retained.
No lower bound on the selected coordinate gap is assumed. -/
theorem allBranchExterior_positive_power_master_integral {N : ℕ} {d : LocalBranchData}
    (B : BranchEstimates d) (ε a D R α β : ℝ) (P : ℕ) (p q : Fin N) (hpq : p ≠ q)
    (hε : 0 < ε) (hεr : ε ≤ B.ε₀) (ha : 0 < a) (hD : 0 < D)
    (hsmall₁ : B.original.separationThreshold*ε ≤ a) (hsmall₂ : 2*B.original.C₀*ε ≤ a)
    (hR : 0 ≤ R) (hRB : R ≤ B.r) (hRπ : R ≤ Real.pi)
    (hα : 0 < α) (hα1 : α ≤ 1) (hβ : 0 < β) (hβ1 : β ≤ 1) :
    let L := fun t => ‖deriv (originalPhase d ε) t‖
    let k := weightedPhaseSpectatorKernel p q α β L
    let T := allBranchExteriorCoordinateMap d ε p q
    let S := allBranchExteriorPositiveGapCell p q R a D
    IntegrableOn (fun u => (u q-u p)^(P+1)*
      ‖deriv (originalPhase d ε) (u p)*deriv (originalPhase d ε) (u q)‖*k (T u)) S ∧
    (∫ u in S, (u q-u p)^(P+1)*
      ‖deriv (originalPhase d ε) (u p)*deriv (originalPhase d ε) (u q)‖*k (T u)) ≤
      (D^(P+1)*allBranchExteriorPositiveCost B a D)*
        (((N:ℝ)*simpleKernelConstant*(1+|Real.log α|))*
          ((N:ℝ)*simpleKernelConstant*(1+|Real.log β|))*B.lengthC^(N-2)) := by
  dsimp only
  let S := allBranchExteriorPositiveGapCell p q R a D
  let L := fun t => ‖deriv (originalPhase d ε) t‖
  let k := weightedPhaseSpectatorKernel p q α β L
  let T := allBranchExteriorCoordinateMap d ε p q
  let T' := fun u => twoPhaseUpdateDeriv (coordinateSumLinear N) (allBranchExteriorTotalDerivative d ε u) p q
  have hL := allBranchExterior_arclength_continuousOn B ε R hε hεr hRB
  have hLint := (B.length_restrict ε hε hεr (Icc (-R) R) (by
    intro t ht
    constructor <;> linarith [ht.1,ht.2])).2
  have hki := weighted_phase_spectator_kernel_integral hpq L B.lengthC B.lengthC_pos.le
    (fun _ => norm_nonneg _) hR hα hα1 hβ hβ1 hL hLint
  have hd (u : Fin N → ℝ) (hu : u ∈ S) : HasFDerivWithinAt T (T' u) S u :=
    (allBranchExterior_coordinate_hasFDerivAt B ε hε hεr u
      (fun i => ⟨hu.1.1.1 i,(hu.1.1.2 i).trans hRB⟩) p q).hasFDerivWithinAt
  have hw : ContinuousOn (fun u : Fin N → ℝ => (u q-u p)^(P+1)*
      ‖deriv (originalPhase d ε) (u p)*deriv (originalPhase d ε) (u q)‖) S := by
    have hp : ContinuousOn (fun u : Fin N → ℝ => L (u p)) S :=
      hL.comp (continuous_apply p).continuousOn (fun u hu =>
        ⟨by linarith [hu.1.1.1 p],hu.1.1.2 p⟩)
    have hq : ContinuousOn (fun u : Fin N → ℝ => L (u q)) S :=
      hL.comp (continuous_apply q).continuousOn (fun u hu =>
        ⟨by linarith [hu.1.1.1 q],hu.1.1.2 q⟩)
    simp_rw [norm_mul]
    exact (((continuous_apply q).sub (continuous_apply p)).pow (P+1)).continuousOn.mul (hp.mul hq)
  have hC : 0 ≤ D^(P+1)*allBranchExteriorPositiveCost B a D :=
    mul_nonneg (pow_nonneg hD.le _) (allBranchExterior_positive_cost_nonneg B ha hD)
  have hratio (u : Fin N → ℝ) (hu : u ∈ S) :
      (u q-u p)^(P+1)*‖deriv (originalPhase d ε) (u p)*deriv (originalPhase d ε) (u q)‖ ≤
        (D^(P+1)*allBranchExteriorPositiveCost B a D)*|(T' u).det| := by
    have hh := allBranchExterior_positive_jacobian_ratio B ε a (u q-u p) hε hεr ha hu.2.1
      hsmall₁ hsmall₂ (u p,u q) ⟨hu.1.1.1 p,(hu.1.1.2 q).trans hRB,hu.1.2.1,le_rfl⟩
    have hpair : ‖deriv (originalPhase d ε) (u p)*deriv (originalPhase d ε) (u q)‖ ≤
        allBranchExteriorPositiveCost B a (u q-u p)*|(T' u).det| := by
      simpa only [T',allBranchExterior_coordinate_det d ε u p q hpq,allBranchExterior_positive_det] using hh
    calc
      _ ≤ (u q-u p)^(P+1)*(allBranchExteriorPositiveCost B a (u q-u p)*|(T' u).det|) :=
        mul_le_mul_of_nonneg_left hpair (pow_nonneg hu.2.1.le _)
      _ = ((u q-u p)^(P+1)*allBranchExteriorPositiveCost B a (u q-u p))*|(T' u).det| := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (allBranchExterior_positive_power_absorption B ha hu.2.1 hu.2.2 P) (abs_nonneg _)
  have himage : T '' S ⊆ phaseSpectatorBox p q R := by
    rintro _ ⟨u,hu,rfl⟩
    exact allBranchExterior_coordinate_image_on_subradius B ε a 0 R p q hε hεr hR hRB hRπ ⟨u,hu.1,rfl⟩
  obtain ⟨hi,hb⟩ := injective_coordinate_weighted_coarea_on
    (allBranchExterior_positive_gap_cell_measurable p q R a D) T T' hd
    (allBranchExterior_positive_gap_injective B ε a D R p q hpq hε hεr ha hRB hsmall₁ hsmall₂)
    himage _ k hw (weightedPhaseSpectatorKernel_continuousOn p q hα hβ L hL)
    (weightedPhaseSpectatorKernel_nonneg p q α β L (fun _ => norm_nonneg _)) hki.1 hC
    (fun u hu => mul_nonneg (pow_nonneg hu.2.1.le _) (norm_nonneg _)) hratio
  exact ⟨hi,hb.trans (mul_le_mul_of_nonneg_left hki.2 hC)⟩

end
end IsingBulk.Tail
