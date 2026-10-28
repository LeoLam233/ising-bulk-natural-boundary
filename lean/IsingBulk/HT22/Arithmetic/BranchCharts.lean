import IsingBulk.HT22.Arithmetic.FullFamily
import IsingBulk.HT22.First.LocalLimit.SignedMeanGap
import IsingBulk.Preferred22.Coordinates

/-! Canonical positive-trace charts for the entire original upper prime
family. Reflection changes the physical signed constraint, not the observable. -/
namespace IsingBulk.HT22.Arithmetic
noncomputable section
open IsingBulk.PrimeFamily IsingBulk.Preferred22 Complex

 def negativeSide (α : ℝ) : Bool := decide (Real.pi/2<α)
 def effectiveAngle (α : ℝ) : ℝ := if Real.pi/2<α then Real.pi-α else α

theorem effectiveAngle_bounds {α : ℝ} (hα : 0<α) (hαπ : α<Real.pi)
    (hc : Real.cos α≠0) : 0<effectiveAngle α ∧ effectiveAngle α<Real.pi/2 := by
  have hne : α≠Real.pi/2 := by intro he;rw [he,Real.cos_pi_div_two] at hc;exact hc rfl
  by_cases h : Real.pi/2<α
  · simp only [effectiveAngle,ite_eq_left h]
    constructor <;> linarith
  · simp only [effectiveAngle,ite_eq_right h]
    exact ⟨hα,lt_of_le_of_ne (le_of_not_gt h) hne⟩

theorem effectiveAngle_cos {α : ℝ} (hα : 0<α) (hαπ : α<Real.pi)
    (hc : Real.cos α≠0) :
    Real.cos (effectiveAngle α)=|Real.cos α| ∧
      Real.cos (effectiveAngle α)=if negativeSide α then -Real.cos α else Real.cos α := by
  by_cases h : Real.pi/2<α
  · have hn := Real.cos_neg_of_pi_div_two_lt_of_lt h (by linarith [Real.pi_pos])
    simp [effectiveAngle,negativeSide,h,Real.cos_pi_sub,abs_of_neg hn]
  · have heff := (effectiveAngle_bounds hα hαπ hc).2
    simp only [effectiveAngle,ite_eq_right h] at heff
    have hp := Real.cos_pos_of_mem_Ioo (show α∈Set.Ioo (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [Real.pi_pos])
    simp [effectiveAngle,negativeSide,h,abs_of_pos hp]

def positiveTraceBranchData (α : ℝ) (hα : 0<α) (hlt : α<Real.pi/2) : PreferredBranchData where
  alpha := α
  b := Real.arccos (2*Real.cos α-1)
  alpha_pos := hα
  alpha_lt := hlt
  b_pos := Real.arccos_pos.mpr (by
    have hh := Real.cos_lt_cos_of_nonneg_of_le_pi (by norm_num : (0:ℝ)≤0)
      (by linarith [Real.pi_pos] : α≤Real.pi) hα
    rw [Real.cos_zero] at hh
    linarith)
  b_lt := Real.arccos_lt_pi.mpr (by
    have hh := Real.cos_pos_of_mem_Ioo (show α∈Set.Ioo (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [Real.pi_pos])
    linarith)
  angle_relation := Real.cos_arccos (by
    have hh := Real.cos_pos_of_mem_Ioo (show α∈Set.Ioo (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [Real.pi_pos])
    linarith) (by linarith [Real.cos_le_one α])

def primeBranchData {p : ℕ} (hp : p.Prime) (hp5 : 5≤p) {a : ℤ}
    (ha : PrimeIndex p a) : PreferredBranchData :=
  positiveTraceBranchData (effectiveAngle (angle p a))
    (effectiveAngle_bounds (primeIndex_angle_bounds hp.pos ha).1
      (primeIndex_angle_bounds hp.pos ha).2 (by
        intro hz;exact primeRoot_level_ne_zero hp hp5 ha (by rw [hz,mul_zero]))).1
    (effectiveAngle_bounds (primeIndex_angle_bounds hp.pos ha).1
      (primeIndex_angle_bounds hp.pos ha).2 (by
        intro hz;exact primeRoot_level_ne_zero hp hp5 ha (by rw [hz,mul_zero]))).2

theorem primeBranchData_cos {p : ℕ} (hp : p.Prime) (hp5 : 5≤p) {a : ℤ}
    (ha : PrimeIndex p a) :
    Real.cos (primeBranchData hp hp5 ha).alpha=
      if negativeSide (angle p a) then -Real.cos (angle p a) else Real.cos (angle p a) := by
  exact (effectiveAngle_cos (primeIndex_angle_bounds hp.pos ha).1
    (primeIndex_angle_bounds hp.pos ha).2 (by
      intro hz;exact primeRoot_level_ne_zero hp hp5 ha (by rw [hz,mul_zero]))).2

theorem primeBranchData_endpoint {p : ℕ} (hp : p.Prime) (hp5 : 5≤p) {a : ℤ}
    (ha : PrimeIndex p a) :
    exp (-((primeBranchData hp hp5 ha).b:ℂ)*I)=endpointBranch p a := by
  have hh := (effectiveAngle_cos (primeIndex_angle_bounds hp.pos ha).1
    (primeIndex_angle_bounds hp.pos ha).2 (by
      intro hz;exact primeRoot_level_ne_zero hp hp5 ha (by rw [hz,mul_zero]))).1
  unfold primeBranchData positiveTraceBranchData endpointBranch
  dsimp only
  rw [hh,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]

theorem primeBranchData_critical_mean {p : ℕ} (hp : p.Prime) (hp5 : 5≤p) {a : ℤ}
    (ha : PrimeIndex p a) :
    ∃ l : ℤ, LocalLimit.signedEqualityMean (negativeSide (angle p a)) p l=
      -(primeBranchData hp hp5 ha).alpha := by
  have hpr : (p:ℝ)≠0 := by exact_mod_cast hp.ne_zero
  by_cases h : Real.pi/2<angle p a
  · obtain ⟨k,hk⟩ := hp.odd_of_ne_two (by omega)
    refine ⟨a-k-1,?_⟩
    have hs : negativeSide (angle p a)=true := by simp [negativeSide,h]
    have hd : (primeBranchData hp hp5 ha).alpha=Real.pi-angle p a := by
      simp [primeBranchData,positiveTraceBranchData,effectiveAngle,h]
    rw [hs,hd]
    simp only [LocalLimit.signedEqualityMean,Physical.constraintAngle,↓reduceIte,angle]
    have hkp : (p:ℝ)=2*(k:ℝ)+1 := by exact_mod_cast hk
    push_cast
    field_simp
    rw [hkp]
    ring
  · refine ⟨-a,?_⟩
    have hs : negativeSide (angle p a)=false := by simp [negativeSide,h]
    have hd : (primeBranchData hp hp5 ha).alpha=angle p a := by
      simp [primeBranchData,positiveTraceBranchData,effectiveAngle,h]
    rw [hs,hd]
    simp only [LocalLimit.signedEqualityMean,Physical.constraintAngle,Bool.false_eq_true,
      ↓reduceIte,angle]
    push_cast
    ring

theorem primeBranchData_signed_resonance {p : ℕ} (hp : p.Prime) (hp5 : 5≤p) {a : ℤ}
    (ha : PrimeIndex p a) :
    Physical.constraintSign (negativeSide (angle p a))*
      exp (-((primeBranchData hp hp5 ha).alpha:ℂ)*I)^p=1 := by
  obtain ⟨l,hl⟩ := primeBranchData_critical_mean hp hp5 ha
  rw [LocalLimit.signed_mean_phase_identity _ hp.pos l,hl]
  simp


theorem effectiveAngle_root (α : ℝ) :
    exp ((effectiveAngle α:ℂ)*I)=
      if negativeSide α then -star (exp ((α:ℂ)*I)) else exp ((α:ℂ)*I) := by
  by_cases h : Real.pi/2<α
  · simp only [effectiveAngle,ite_eq_left h,negativeSide,decide_eq_true h,↓reduceIte,
      ofReal_sub,sub_mul,exp_sub,exp_pi_mul_I]
    have hc : star (exp ((α:ℂ)*I))=exp (-((α:ℂ)*I)) := by
      change (starRingEnd ℂ) (exp ((α:ℂ)*I))=exp (-((α:ℂ)*I))
      rw [←Complex.exp_conj]
      congr 1
      simp
    rw [hc,exp_neg]
    ring
  · simp [effectiveAngle,negativeSide,h]

end
end IsingBulk.HT22.Arithmetic
