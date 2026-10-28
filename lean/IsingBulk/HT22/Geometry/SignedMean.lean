import IsingBulk.HT22.Geometry.SignedLift

namespace IsingBulk.HT22.Geometry
noncomputable section
open Set MeasureTheory IsingBulk.Preferred22
open scoped BigOperators ENNReal

/-- The same O(N) means suffice for both a=0 and a=pi. -/
theorem signedRightShell_mean_mem {n : ℕ} (a : ℝ) (ha : |a|≤Real.pi)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {δB r : ℝ} (hδB : δB<B.delta)
    {l : ℤ} {i j : Fin (n+1)} {θ : Fin n → ℝ}
    (hθ : θ∈signedRightShell a d B δB r l i j) : l∈preferredMeanIndices (n+1) := by
  obtain ⟨_,hw,hs⟩ := hθ
  let w := preferredLiftedAngles B.delta (constrainedAtTotal a θ)
  have hb (v : Fin (n+1)) : -Real.pi≤w v ∧ w v≤Real.pi := by
    have hh := preferred_right_interval_original d B hδB (hw.1 v)
    exact ⟨hh.1.le,hh.2⟩
  have hlo := Finset.sum_le_sum (fun v (_ : v∈Finset.univ) => (hb v).1)
  have hhi := Finset.sum_le_sum (fun v (_ : v∈Finset.univ) => (hb v).2)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hlo hhi
  change (∑ v,w v)=a+2*Real.pi*(l:ℝ) at hs
  rw [hs] at hlo hhi
  have ha' := abs_le.mp ha
  have hn : (1:ℝ)≤((n+1:ℕ):ℝ) := by exact_mod_cast Nat.le_add_left 1 n
  have hp : 0<Real.pi := Real.pi_pos
  have hlow : -((n+1:ℕ):ℝ)≤(l:ℝ) := by nlinarith
  have hupp : (l:ℝ)≤((n+1:ℕ):ℝ) := by nlinarith
  apply Finset.mem_Icc.mpr
  constructor
  · exact_mod_cast hlow
  · exact_mod_cast hupp

/-- The total number of mean/extremum labels is at most 3N^3;
no connected-component multiplicity is inserted. -/
theorem signed_shell_label_count (N : ℕ) (hN : 0<N) :
    (preferredMeanIndices N).card*N*N≤3*N^3 := by
  have h := preferredMeanIndices_card_le hN
  calc
    _ ≤ (3*N)*N*N := Nat.mul_le_mul_right N (Nat.mul_le_mul_right N h)
    _ = _ := by ring

/-- Actual shifted mean window, before any analytic scale is evaluated. -/
theorem signedRightShell_window {n : ℕ} (a : ℝ) (d : PreferredBranchData)
    (B : PreferredCoareaBump d) {δB r : ℝ} {l : ℤ} {i j : Fin (n+1)}
    {θ : Fin n → ℝ} (hθ : θ∈signedRightShell a d B δB r l i j) :
    ∀ v : Fin (n+1),
      d.b+(a+2*Real.pi*(l:ℝ))/((n+1:ℕ):ℝ)-2*r ≤
        preferredLiftedAngles B.delta (constrainedAtTotal a θ) v+d.b ∧
      preferredLiftedAngles B.delta (constrainedAtTotal a θ) v+d.b ≤
        d.b+(a+2*Real.pi*(l:ℝ))/((n+1:ℕ):ℝ)+2*r := by
  obtain ⟨_,hw,hs⟩ := hθ
  let w := preferredLiftedAngles B.delta (constrainedAtTotal a θ)
  have hmean : (∑ v,(w v+d.b))=((n+1:ℕ):ℝ)*(d.b+(a+2*Real.pi*(l:ℝ))/((n+1:ℕ):ℝ)) := by
    rw [Finset.sum_add_distrib]
    change (∑ v,w v)=a+2*Real.pi*(l:ℝ) at hs
    rw [hs]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    have hN : ((n+1:ℕ):ℝ)≠0 := by positivity
    field_simp
    ring
  apply constrained_shell_coordinate_window (i := i) (j := j) (Nat.succ_pos n) hmean
  · intro v
    have hv := hw.2.1 v
    constructor <;> linarith [hv.1,hv.2]
  · have hh := hw.2.2.2
    linarith

end
end IsingBulk.HT22.Geometry
