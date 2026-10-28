import IsingBulk.HT22.Geometry.SignedShellAggregation
import IsingBulk.HT22.First.LocalLimit.SignedEqualityTube

namespace IsingBulk.HT22.Geometry
noncomputable section
open Set MeasureTheory IsingBulk.Preferred22 IsingBulk.PrimeFamily Arithmetic LocalLimit
open scoped BigOperators ENNReal

/-- Every true constrained mean in the right region, including the full
collision locus, belongs to the same explicit finite index set. -/
theorem signedRightRegion_mean_mem {n : ℕ} (a : ℝ) (ha : |a|≤Real.pi)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {δB : ℝ} (hδB : δB<B.delta)
    {θ : Fin n → ℝ} (hθ : θ∈signedRightRegion a d B δB) {l : ℤ}
    (hs : (∑ i,preferredLiftedAngles B.delta (constrainedAtTotal a θ) i)=a+2*Real.pi*(l:ℝ)) :
    l∈preferredMeanIndices (n+1) := by
  let w := preferredLiftedAngles B.delta (constrainedAtTotal a θ)
  have hne : (Finset.univ : Finset (Fin (n+1))).Nonempty := ⟨0,Finset.mem_univ _⟩
  obtain ⟨i,_,hmin⟩ := Finset.exists_min_image Finset.univ w hne
  obtain ⟨j,_,hmax⟩ := Finset.exists_max_image Finset.univ w hne
  have hext (v : Fin (n+1)) : w i≤w v ∧ w v≤w j :=
    ⟨hmin v (Finset.mem_univ _),hmax v (Finset.mem_univ _)⟩
  have hg : 0≤w j-w i := sub_nonneg.mpr (hext j).1
  apply signedRightShell_mean_mem a ha d B hδB (r := w j-w i) (i := i) (j := j)
  exact ⟨hθ.1,⟨hθ.2,hext,le_rfl,by linarith⟩,hs⟩

/-- A genuine finite signed equality chart cover for the actual one-sided
torus lift. The arithmetic gap is proved for the selected prime point,
not assumed as an analytic-cover premise. -/
theorem finite_signed_actual_equality_tube {p : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    {a : ℤ} (ha : PrimeIndex p a) {M : ℕ} (hM : 0<M)
    (d : PreferredBranchData)
    (hb : d.b=Real.arccos (|2*Real.cos (angle p a)|-1)) :
    ∃ g : ℝ, 0<g ∧ ∀ B : PreferredCoareaBump d, ∀ negative : Bool,
      ∀ n : ℕ, n+1≤M → ∀ δB : ℝ, δB<B.delta → δB≤g/4 →
      ∀ θ : Fin n → ℝ,
      θ∈signedRightRegion (Physical.constraintAngle negative) d B δB →
      preferredAngularDiameter (preferredLiftedAngles B.delta
        (constrainedAtTotal (Physical.constraintAngle negative) θ))≤g/4 →
      ∃ l : ℤ, l∈preferredMeanIndices (n+1) ∧
        (∑ i,preferredLiftedAngles B.delta (constrainedAtTotal (Physical.constraintAngle negative) θ) i)=
          Physical.constraintAngle negative+2*Real.pi*(l:ℝ) ∧
        (∀ i, |preferredLiftedAngles B.delta (constrainedAtTotal (Physical.constraintAngle negative) θ) i-
          signedEqualityMean negative (n+1) l|≤
            preferredAngularDiameter (preferredLiftedAngles B.delta
              (constrainedAtTotal (Physical.constraintAngle negative) θ))) ∧
        (∀ i,g/2≤preferredLiftedAngles B.delta (constrainedAtTotal (Physical.constraintAngle negative) θ) i+d.b) := by
  obtain ⟨g,hg,hTube⟩ := finite_signed_equality_tube hp hp5 ha hM
  refine ⟨g,hg,?_⟩
  intro B negative n hn δB hδB hδ θ hθ hD
  obtain ⟨l,hl⟩ := signedLiftedAngles_integer_mean B.delta (Physical.constraintAngle negative) θ
  have ha' : |Physical.constraintAngle negative|≤Real.pi := by
    cases negative <;> simp [Physical.constraintAngle,Real.pi_pos.le]
  have hmean := signedRightRegion_mean_mem (Physical.constraintAngle negative) ha' d B hδB hθ hl
  have ht := hTube negative (n+1) (by omega) hn δB hδ l
    (preferredLiftedAngles B.delta (constrainedAtTotal (Physical.constraintAngle negative) θ))
    (by simpa only [add_comm] using hl)
    (fun i => by rw [←hb]; linarith [(hθ.2 i).1]) hD
  refine ⟨l,hmean,hl,ht.1,?_⟩
  intro i
  simpa only [hb] using ht.2 i

theorem signedRightRegion_mean_upper {n : ℕ} (a : ℝ)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {δB : ℝ}
    {θ : Fin n → ℝ} (hθ : θ∈signedRightRegion a d B δB) {l : ℤ}
    (hs : (∑ i,preferredLiftedAngles B.delta (constrainedAtTotal a θ) i)=a+2*Real.pi*(l:ℝ)) :
    (a+2*Real.pi*(l:ℝ))/((n+1:ℕ):ℝ)≤B.delta := by
  have hh := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => (hθ.2 i).2)
  rw [hs] at hh
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hh
  exact (div_le_iff₀ (by positivity : (0:ℝ)<((n+1:ℕ):ℝ))).mpr (by simpa only [mul_comm] using hh)

/-- Only a finite list of genuinely regular right-arc centers is needed
near the equality locus; labels outside this list are not assumed analytic. -/
theorem finite_signed_regular_center_cover {p : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    {a : ℤ} (ha : PrimeIndex p a) {M : ℕ} (hM : 0<M)
    (d : PreferredBranchData)
    (hb : d.b=Real.arccos (|2*Real.cos (angle p a)|-1)) :
    ∃ g : ℝ, 0<g ∧ ∀ B : PreferredCoareaBump d, ∀ negative : Bool,
      ∀ n : ℕ,n+1≤M → ∀ δB : ℝ,δB<B.delta → δB≤g/4 →
      ∀ θ : Fin n → ℝ,θ∈signedRightRegion (Physical.constraintAngle negative) d B δB →
      preferredAngularDiameter (preferredLiftedAngles B.delta
        (constrainedAtTotal (Physical.constraintAngle negative) θ))≤g/4 →
      ∃ l : ℤ,l∈preferredMeanIndices (n+1) ∧
        signedEqualityMean negative (n+1) l∈Icc (-d.b+g/4) B.delta ∧
        (∑ i,preferredLiftedAngles B.delta (constrainedAtTotal (Physical.constraintAngle negative) θ) i)=
          Physical.constraintAngle negative+2*Real.pi*(l:ℝ) ∧
        (∀ i,|preferredLiftedAngles B.delta (constrainedAtTotal (Physical.constraintAngle negative) θ) i-
          signedEqualityMean negative (n+1) l|≤
            preferredAngularDiameter (preferredLiftedAngles B.delta
              (constrainedAtTotal (Physical.constraintAngle negative) θ))) := by
  obtain ⟨g,hg,htube⟩ := finite_signed_actual_equality_tube hp hp5 ha hM d hb
  refine ⟨g,hg,?_⟩
  intro B negative n hn δB hδB hδ θ hθ hD
  obtain ⟨l,hl,hs,hw,hbranch⟩ := htube B negative n hn δB hδB hδ θ hθ hD
  refine ⟨l,hl,⟨?_,?_⟩,hs,hw⟩
  · have h0 := (abs_le.mp (hw 0)).2
    have hg0 := hbranch 0
    linarith
  · simpa only [signedEqualityMean,add_comm] using
      signedRightRegion_mean_upper (Physical.constraintAngle negative) d B hθ hs

end
end IsingBulk.HT22.Geometry
