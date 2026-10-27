import IsingBulk.Preferred22.WeightedEqualitySupport
import IsingBulk.Preferred22.FiniteEqualityGeometry
import IsingBulk.Preferred22.ZerothSourceBound

/-! Actual support and norm of the inner equality-tube multiplier. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set
open scoped BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false

theorem preferredInnerEqualityMultiplier_smooth {N : ℕ} (R : ℝ) :
    ContDiff ℝ ∞ (fun θ : Fin N → ℝ => 1-preferredEqualityMultiplier R θ) :=
  contDiff_const.sub (preferredEqualityMultiplier_smooth R)

theorem preferredInnerEqualityMultiplier_norm {N : ℕ} (R : ℝ) (θ : Fin N → ℝ) :
    ‖1-preferredEqualityMultiplier R θ‖≤1 := by
  obtain ⟨hlo,hhi⟩ := preferredEqualityCutoff_bounds R θ
  change ‖(1:ℂ)-(preferredEqualityCutoff R θ:ℂ)‖≤1
  rw [←Complex.ofReal_one,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (by linarith)]
  linarith

theorem preferredInnerEqualityMultiplier_diameter {N : ℕ} {R : ℝ} (hR : 0<R)
    (θ : Fin N → ℝ) (hne : 1-preferredEqualityMultiplier R θ≠0) :
    preferredAngularDiameter θ≤R := by
  by_contra hn
  have hd : R<preferredAngularDiameter θ := lt_of_not_ge hn
  have hs := preferredEqualitySize_diameter_sq θ
  have hq : (1/2:ℝ)≤preferredEqualitySize θ/R^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hR)).mpr
    nlinarith [Metric.diam_nonneg (s := Set.range θ)]
  have he := preferredPopulationCutoff_one hq
  apply hne
  simp only [preferredEqualityMultiplier,preferredEqualityCutoff,he,Complex.ofReal_one,sub_self]

theorem preferredCellWeight_right_support (d : PreferredBranchData)
    (B : PreferredCoareaBump d) {N : ℕ} {δB : ℝ} (rcut : ℝ → ℝ)
    (hcut : PreferredRightCutoffData d B δB rcut) (θ : Fin N → ℝ)
    (hθ : ∀i,θ i∈Ioc (-Real.pi-B.delta) (Real.pi-B.delta))
    (hw : preferredCellWeight .right preferredPopulationCutoff B.p B.m rcut θ≠0) :
    ∀i,θ i∈Icc (-d.b-δB) B.delta := by
  classical
  intro i
  constructor
  · by_contra hn
    have hlo : θ i< -d.b-δB := lt_of_not_ge hn
    have hi : θ i∈Icc (-Real.pi-B.delta) B.delta :=
      ⟨(hθ i).1.le,by linarith [d.b_pos,B.delta_pos,hcut.1]⟩
    have hz := (hcut.2.2.2.2.2 (θ i) hi).1 (by linarith)
    have hp : (∏v,rcut (θ v))=0 := Finset.prod_eq_zero (Finset.mem_univ i) hz
    exact hw (by simp only [preferredCellWeight,preferredRightWeight,hp,mul_zero])
  · by_contra hn
    have hp : B.p (θ i)=1 := B.plateau (θ i) ⟨(lt_of_not_ge hn).le,(hθ i).2⟩
    have hP : 1/2≤occupancy B.p θ := by
      have hh := Finset.single_le_sum (s := (Finset.univ : Finset (Fin N)))
        (fun v _ => B.lower_bound (θ v)) (Finset.mem_univ i)
      rw [hp] at hh
      exact (by norm_num : (1/2:ℝ)≤1).trans hh
    exact hw (by simp only [preferredCellWeight,preferredLowerWeight,lowerWeight,
      preferredPopulationCutoff_one hP,sub_self,zero_mul,zero_div])

theorem preferred_inner_right_weight_norm (d : PreferredBranchData)
    (B : PreferredCoareaBump d) {N : ℕ} {δB : ℝ} (rcut : ℝ → ℝ)
    (hcut : PreferredRightCutoffData d B δB rcut) (R : ℝ) (θ : Fin N → ℝ) :
    ‖(1-preferredEqualityMultiplier R θ)*
      (preferredCellWeight .right preferredPopulationCutoff B.p B.m rcut θ:ℂ)‖≤1 := by
  have hw := preferred_right_weight_bounds preferredPopulationCutoff B.p B.m rcut
    preferredPopulationCutoff_bounds hcut.2.2.2.2.1 θ
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hw.1]
  exact (mul_le_mul (preferredInnerEqualityMultiplier_norm R θ) hw.2 hw.1
    (by norm_num : (0:ℝ)≤1)).trans_eq (one_mul 1)

theorem preferred_inner_right_support {n : ℕ} (d : PreferredBranchData)
    (B : PreferredCoareaBump d) {δB R : ℝ} (hR : 0<R) (rcut : ℝ → ℝ)
    (hcut : PreferredRightCutoffData d B δB rcut) (θ : Fin n → ℝ)
    (hθ : θ∈angularBox n)
    (hne : let w := preferredLiftedAngles B.delta (constrainedAngles θ)
      (1-preferredEqualityMultiplier R w)*
        (preferredCellWeight .right preferredPopulationCutoff B.p B.m rcut w:ℂ)≠0) :
    θ∈preferredRightRegion d B δB ∧
      preferredAngularDiameter (preferredLiftedAngles B.delta (constrainedAngles θ))≤R := by
  let w := preferredLiftedAngles B.delta (constrainedAngles θ)
  change (1-preferredEqualityMultiplier R w)*
    (preferredCellWeight .right preferredPopulationCutoff B.p B.m rcut w:ℂ)≠0 at hne
  have hw : preferredCellWeight .right preferredPopulationCutoff B.p B.m rcut w≠0 := by
    intro hh
    exact hne (by simp only [hh,Complex.ofReal_zero,mul_zero])
  have hinner : 1-preferredEqualityMultiplier R w≠0 := by
    intro hh
    exact hne (by simp only [hh,zero_mul])
  exact ⟨⟨hθ,preferredCellWeight_right_support d B rcut hcut w
    (preferredLiftedAngles_mem_oneSided B.delta (constrainedAngles θ)) hw⟩,
    preferredInnerEqualityMultiplier_diameter hR w hinner⟩

end
end IsingBulk.Preferred22
