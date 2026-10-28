import IsingBulk.HT22.Geometry.FiniteEqualityCover
import IsingBulk.HT22.Geometry.SmoothFinitePartition

namespace IsingBulk.HT22.Geometry
noncomputable section
open Set Filter Metric IsingBulk.Preferred22 IsingBulk.First LocalLimit
open scoped BigOperators Topology ContDiff

/-- A strictly positive common radius for a genuinely finite family. -/
theorem finite_positive_radius {ι : Type*} (S : Finset ι) (R : ι → ℝ)
    (hR : ∀ i∈S,0<R i) : ∃ r : ℝ, 0<r ∧ ∀ i∈S,r<R i := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1,zero_lt_one,by simp⟩
  | @insert i S hi ih =>
    obtain ⟨r,hr,hsmall⟩ := ih (fun j hj => hR j (Finset.mem_insert_of_mem hj))
    have hRi := hR i (Finset.mem_insert_self ..)
    refine ⟨min r (R i/2),lt_min hr (half_pos hRi),?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact (min_le_right _ _).trans_lt (half_lt_self hRi)
    · exact (min_le_left _ _).trans_lt (hsmall j hj)

/-- Explicit cutoffs centered at every possible signed equality point in
the original free angular coordinates. Their finite product remainder
vanishes on a proved positive-diameter tube of the actual right region. -/
theorem exists_signed_equality_cutoffs (n : ℕ) (a : ℝ) (ha : |a|≤Real.pi)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {δB : ℝ} (hδB : δB<B.delta)
    (R : ℤ → ℝ) (hR : ∀ l∈preferredMeanIndices (n+1),0<R l) :
    ∃ χ : ℤ → (Fin n → ℝ) → ℝ, ∃ r : ℝ, 0<r ∧
      (∀ l∈preferredMeanIndices (n+1),
        ContDiff ℝ ∞ (χ l) ∧ HasCompactSupport (χ l) ∧
        (∀ x,0≤χ l x ∧ χ l x≤1) ∧
        tsupport (χ l) ⊆ ball (fun _ => (a+2*Real.pi*(l:ℝ))/((n+1:ℕ):ℝ)) (R l)) ∧
      (∀ θ : Fin n → ℝ, θ∈signedRightRegion a d B δB →
        preferredAngularDiameter (preferredLiftedAngles B.delta (constrainedAtTotal a θ))≤r →
        ∃ l∈preferredMeanIndices (n+1),χ l θ=1) := by
  classical
  let L := preferredMeanIndices (n+1)
  let center (l : ℤ) : Fin n → ℝ := fun _ => (a+2*Real.pi*(l:ℝ))/((n+1:ℕ):ℝ)
  have hex (l : {l : ℤ // l∈L}) : ∃ χ : (Fin n → ℝ) → ℝ,
      ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ (∀ x,0≤χ x ∧ χ x≤1) ∧
      χ =ᶠ[𝓝 (center l)] (fun _ => 1) ∧ tsupport χ ⊆ ball (center l) (R l) :=
    exists_fixed_smooth_cutoff (center l) (ball_mem_nhds _ (hR l l.2))
  choose χ hc hcomp hb hone hsupp using hex
  have hrad (l : {l : ℤ // l∈L}) : ∃ r : ℝ,0<r ∧ ∀ x∈ball (center l) r,χ l x=1 := by
    obtain ⟨r,hr,hb⟩ := Metric.mem_nhds_iff.mp (hone l)
    exact ⟨r,hr,hb⟩
  choose ρ hρ hρone using hrad
  let χ' : ℤ → (Fin n → ℝ) → ℝ := fun l => if hl : l∈L then χ ⟨l,hl⟩ else fun _ => 0
  let ρ' : ℤ → ℝ := fun l => if hl : l∈L then ρ ⟨l,hl⟩ else 1
  obtain ⟨r,hr,hsmall⟩ := finite_positive_radius L ρ' (fun l hl => by simpa only [ρ',dite_eq_left hl] using hρ ⟨l,hl⟩)
  refine ⟨χ',r,hr,?_,?_⟩
  · intro l hl
    simpa only [χ',L,dite_eq_left hl,center] using And.intro (hc ⟨l,hl⟩)
      (And.intro (hcomp ⟨l,hl⟩) (And.intro (hb ⟨l,hl⟩) (hsupp ⟨l,hl⟩)))
  · intro θ hθ hD
    obtain ⟨l,hl⟩ := signedLiftedAngles_integer_mean B.delta a θ
    have hlmem : l∈L := signedRightRegion_mean_mem a ha d B hδB hθ hl
    have hNr : ((n+1:ℕ):ℝ)≠0 := by positivity
    have hsum : (∑ i,preferredLiftedAngles B.delta (constrainedAtTotal a θ) i)=
        ((n+1:ℕ):ℝ)*((a+2*Real.pi*(l:ℝ))/((n+1:ℕ):ℝ)) := by
      rw [mul_div_cancel₀ _ hNr]
      exact hl
    have hw := preferred_mean_diameter_window (by omega : 0<n+1)
      (preferredLiftedAngles B.delta (constrainedAtTotal a θ)) _ hsum
    have hnorm : ‖θ-center l‖≤r := by
      apply (pi_norm_le_iff_of_nonneg hr.le).mpr
      intro j
      have hj := hw j.castSucc
      rw [signed_lift_free_eq_of_right d B hδB a θ hθ.1 hθ.2 j] at hj
      simpa only [Pi.sub_apply,Real.norm_eq_abs,center] using hj.trans hD
    refine ⟨l,hlmem,?_⟩
    simp only [χ',dite_eq_left hlmem]
    apply hρone ⟨l,hlmem⟩
    rw [mem_ball,dist_eq_norm]
    exact hnorm.trans_lt (by simpa only [ρ',dite_eq_left hlmem] using hsmall l hlmem)

end
end IsingBulk.HT22.Geometry
