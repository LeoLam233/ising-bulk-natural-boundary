import IsingBulk.HT22.Physical.ContourDensity
import IsingBulk.Preferred22.FirstLocalization

namespace IsingBulk.HT22.Geometry
noncomputable section
open Set IsingBulk.Preferred22
open scoped BigOperators

theorem signed_first_plateau_density {N : ℕ} (negative : Bool)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) (τ : ℝ) (t : ℂ) (θ : Fin N → ℝ)
    (hθ : ∀ i,θ i∈Ioo (-Real.pi+B.delta) (-B.delta)) :
    Physical.bareContourDensity negative τ B.p B.m t θ=
      Physical.signedAngularDensity negative t θ/((N.factorial:ℂ)*(2*Real.pi:ℂ)^(N-1)) := by
  have hp : ∀ i,B.p (θ i)=0 := fun i => (preferred_lower_plateau_values d B (hθ i)).1
  have hP : occupancy B.p θ=0 := by simp [occupancy,hp]
  have hw : deformedAngles τ B.p B.m θ=(fun i => (θ i:ℂ)) := by
    funext i
    simp only [deformedAngles,balancedShift,hP,hp,zero_mul,mul_zero,sub_self,
      Complex.ofReal_zero,sub_zero]
  unfold Physical.bareContourDensity
  rw [preferred_first_plateau_matrix d B τ θ hθ,Matrix.det_one,one_mul,hw,
    Physical.complexSignedDensity_real]

theorem first_plateau_cellWeight {N : ℕ} (hN : 0<N) (d : PreferredBranchData)
    (B : PreferredCoareaBump d) (r : ℝ → ℝ) (θ : Fin N → ℝ)
    (hθ : ∀ i,θ i∈Ioo (-Real.pi+B.delta) (-B.delta)) (hr : ∀ i,r (θ i)=1) :
    preferredCellWeight .right preferredPopulationCutoff B.p B.m r θ=1 := by
  have hp : ∀ i,B.p (θ i)=0 := fun i => (preferred_lower_plateau_values d B (hθ i)).1
  have hm : ∀ i,B.m (θ i)=1 := fun i => (preferred_lower_plateau_values d B (hθ i)).2.1
  have hP : occupancy B.p θ=0 := by simp [occupancy,hp]
  have hQ : occupancy B.m θ=(N:ℝ) := by simp [occupancy,hm]
  have hη0 : preferredPopulationCutoff 0=0 := preferredPopulationCutoff_zero (by norm_num)
  have hηN : preferredPopulationCutoff (N:ℝ)=1 := preferredPopulationCutoff_one (by
    have : (1:ℝ)≤N := by exact_mod_cast hN
    linarith)
  simp only [preferredCellWeight,preferredLowerWeight,lowerWeight,preferredRightWeight,
    hP,hQ,hη0,hηN,hr,Finset.prod_const_one]
  norm_num

/-- A genuine source neighborhood where the complete signed right seed
is exactly the normalized undeformed physical density, including N! and
N−1 Haar factors. No endpoint/asymptotic theorem is reused. -/
theorem signed_first_chart_seed_neighborhood (d : PreferredBranchData)
    (B : PreferredCoareaBump d) (δB : ℝ) (r : ℝ → ℝ)
    (hr : PreferredRightCutoffData d B δB r) :
    ∃ ρ : ℝ,0<ρ ∧ ∀ N : ℕ,0<N → ∀ θ : Fin N → ℝ,
      (∀ i,|θ i+d.alpha|<ρ) → ∀ negative : Bool,∀ τ : ℝ,∀ t : ℂ,
      (preferredCellWeight .right preferredPopulationCutoff B.p B.m r θ:ℂ)*
        Physical.bareContourDensity negative τ B.p B.m t θ=
      Physical.signedAngularDensity negative t θ/((N.factorial:ℂ)*(2*Real.pi:ℂ)^(N-1)) := by
  have h1 : 0<d.alpha-B.delta := by linarith [B.delta_alpha,d.alpha_pos]
  have h2 : 0<Real.pi-B.delta-d.alpha := by linarith [B.delta_alpha,d.alpha_lt,Real.pi_pos]
  have h3 : 0<d.b-d.alpha := sub_pos.mpr (preferred_alpha_lt_branch d)
  let ρ := min ((d.alpha-B.delta)/2)
    (min ((Real.pi-B.delta-d.alpha)/2) ((d.b-d.alpha)/2))
  have hρ : 0<ρ := by dsimp [ρ]; positivity
  have hρ1 : ρ≤(d.alpha-B.delta)/2 := min_le_left _ _
  have hρ2 : ρ≤(Real.pi-B.delta-d.alpha)/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hρ3 : ρ≤(d.b-d.alpha)/2 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨ρ,hρ,?_⟩
  intro N hN θ hθ negative τ t
  have hw (i : Fin N) : θ i∈Ioo (-Real.pi+B.delta) (-B.delta) := by
    obtain ⟨hl,hu⟩ := abs_lt.mp (hθ i)
    constructor <;> linarith
  have hrθ (i : Fin N) : r (θ i)=1 := by
    have hi := abs_lt.mp (hθ i)
    apply (hr.2.2.2.2.2 (θ i)
      ⟨by linarith [(hw i).1,B.delta_pos],by linarith [(hw i).2,B.delta_pos]⟩).2
    linarith [hr.1]
  rw [first_plateau_cellWeight hN d B r θ hw hrθ,Complex.ofReal_one,one_mul]
  exact signed_first_plateau_density negative d B τ t θ hw

end
end IsingBulk.HT22.Geometry
