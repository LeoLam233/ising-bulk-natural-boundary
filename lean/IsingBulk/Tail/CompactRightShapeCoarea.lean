import IsingBulk.Tail.CompactRightCurvature

/-! Source limiting compact-right shape rays. The coupled finite-jet
perturbation is deliberately not replaced by a limiting assertion. -/
namespace IsingBulk.Tail
noncomputable section
open Set
open scoped BigOperators

def compactRightShapePhase {N : ℕ} (S t : ℝ) (ω : Fin N → ℝ) (ρ : ℝ) : ℝ :=
  ∑ i, compactRightPhase S (t+ρ*ω i)

theorem compactRightShapePhase_hasDerivAt {N : ℕ} (S t ρ : ℝ) (ω : Fin N → ℝ)
    (hm : ∀ i, |S-Real.cos (t+ρ*ω i)| < 1) :
    HasDerivAt (compactRightShapePhase S t ω)
      (∑ i, deriv (compactRightPhase S) (t+ρ*ω i)*ω i) ρ := by
  apply HasDerivAt.fun_sum
  intro i _
  have hline : HasDerivAt (fun x : ℝ => t+x*ω i) (ω i) ρ := by
    simpa using ((hasDerivAt_id ρ).mul_const (ω i)).const_add t
  simpa only [Function.comp_def, (compactRightPhase_hasDerivAt S (t+ρ*ω i) (hm i)).deriv] using
    (compactRightPhase_hasDerivAt S (t+ρ*ω i) (hm i)).comp ρ hline

theorem compactRightShapePhase_radial_bound {N : ℕ} {S δ t ρ : ℝ}
    (hS : 0<S) (hδ : 0<δ) (hρ : 0≤ρ) (ω : Fin N → ℝ)
    (hzero : ∑ i, ω i=0) (hunit : ∑ i, (ω i)^2=1)
    (hm : ∀ i, ∀ x ∈ uIcc t (t+ρ*ω i), |S-Real.cos x| ≤ 1-δ) :
    -deriv (compactRightShapePhase S t ω) ρ ≥ S*δ*ρ := by
  have hi (i : Fin N) : S*δ*ρ*(ω i)^2 ≤
      (deriv (compactRightPhase S) t-deriv (compactRightPhase S) (t+ρ*ω i))*ω i := by
    by_cases hw : 0≤ω i
    · have ht : t≤t+ρ*ω i := by nlinarith
      have hg := compactRightPhase_slope_gap hS hδ ht
        (fun x hx => hm i x (by simpa [uIcc_of_le ht] using hx))
      have hh := mul_le_mul_of_nonneg_right hg hw
      nlinarith
    · have hw' : ω i ≤ 0 := le_of_not_ge hw
      have ht : t+ρ*ω i≤t := by nlinarith
      have hg := compactRightPhase_slope_gap hS hδ ht
        (fun x hx => hm i x (by simpa [uIcc_of_ge ht] using hx))
      have hh := mul_le_mul_of_nonpos_right hg hw'
      nlinarith
  have hd := compactRightShapePhase_hasDerivAt S t ρ ω (fun i => by
    have hh := hm i (t+ρ*ω i) (right_mem_uIcc); linarith)
  rw [hd.deriv]
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hi i)
  simp only [Finset.sum_sub_distrib,sub_mul,← Finset.mul_sum,hzero,hunit,mul_zero,mul_one,
    zero_sub] at hh
  exact hh

/-- The literal limiting phase pair F=N*t and G=sum g(t+rho*omega)
has the coarea determinant margin N*c_R*rho on each normalized shape ray. -/
theorem compactRightShapePhase_jacobian {N : ℕ} {S δ t ρ : ℝ}
    (hS : 0<S) (hδ : 0<δ) (hρ : 0≤ρ) (ω : Fin N → ℝ)
    (hzero : ∑ i, ω i=0) (hunit : ∑ i, (ω i)^2=1)
    (hm : ∀ i, ∀ x ∈ uIcc t (t+ρ*ω i), |S-Real.cos x| ≤ 1-δ) :
    (N:ℝ)*S*δ*ρ ≤ |(N:ℝ)*deriv (compactRightShapePhase S t ω) ρ| := by
  have hb := compactRightShapePhase_radial_bound hS hδ hρ ω hzero hunit hm
  have hh := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg N : (0:ℝ)≤N)
  calc
    _ ≤ -((N:ℝ)*deriv (compactRightShapePhase S t ω) ρ) := by nlinarith
    _ ≤ _ := neg_le_abs _


/-- Each positive shape ray has multiplicity one for the limiting G phase. -/
theorem compactRightShapePhase_strictAntiOn {N : ℕ} {S δ t R : ℝ}
    (hS : 0<S) (hδ : 0<δ) (ω : Fin N → ℝ)
    (hzero : ∑ i, ω i=0) (hunit : ∑ i, (ω i)^2=1)
    (hm : ∀ ρ ∈ Ioc 0 R, ∀ i, ∀ x ∈ uIcc t (t+ρ*ω i),
      |S-Real.cos x| ≤ 1-δ) :
    StrictAntiOn (compactRightShapePhase S t ω) (Ioc 0 R) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioc 0 R)
  · have hc : Continuous (compactRightShapePhase S t ω) := by
      unfold compactRightShapePhase compactRightPhase
      fun_prop
    exact hc.continuousOn
  · intro ρ hρ
    have hρ' : ρ ∈ Ioc 0 R := interior_subset hρ
    have hb := compactRightShapePhase_radial_bound hS hδ hρ'.1.le ω hzero hunit (hm ρ hρ')
    have hp := mul_pos (mul_pos hS hδ) hρ'.1
    linarith

/-- The intersection of an interval cube with a straight shape ray is convex.
Thus no extra ray multiplicity is hidden in the limiting compact chart. -/
theorem compactRightShapeRay_convex {N : ℕ} (a b t : ℝ) (ω : Fin N → ℝ) :
    Convex ℝ {ρ : ℝ | 0 ≤ ρ ∧ ∀ i, t+ρ*ω i ∈ Icc a b} := by
  intro x hx y hy u v hu hv huv
  change 0 ≤ u*x+v*y ∧ ∀ i, t+(u*x+v*y)*ω i ∈ Icc a b
  refine ⟨add_nonneg (mul_nonneg hu hx.1) (mul_nonneg hv hy.1),?_⟩
  intro i
  have hlo := add_le_add (mul_le_mul_of_nonneg_left (hx.2 i).1 hu)
    (mul_le_mul_of_nonneg_left (hy.2 i).1 hv)
  have hhi := add_le_add (mul_le_mul_of_nonneg_left (hx.2 i).2 hu)
    (mul_le_mul_of_nonneg_left (hy.2 i).2 hv)
  have he : u*(t+x*ω i)+v*(t+y*ω i)=t+(u*x+v*y)*ω i := by
    calc
      _ = (u+v)*t+(u*x+v*y)*ω i := by ring
      _ = _ := by rw [huv,one_mul]
  rw [he,← add_mul,huv,one_mul] at hlo hhi
  exact ⟨hlo,hhi⟩

end
end IsingBulk.Tail
