import IsingBulk.Joint.Negative.FamilyQuadratic
import IsingBulk.Joint.Negative.FamilyPairSlope
import IsingBulk.Anisotropic.NegativeNormalForm.RootPairBounds

namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter Metric IsingBulk.Anisotropic.NegativeNormalForm
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
/-- Scalar pair bounds retain each coordinate's energy, rather than replacing
all coordinates by the configuration sup norm. Constants precede every n. -/
theorem compact_family_root_pair_bounds (B : ℂ × E→ℂ) (phi : ℝ) (hphi : Real.sin phi≠0)
    {P : Set E} (hP : IsCompact P) (hB : ∀eta∈P,AnalyticAt ℂ B (0,eta))
    (hBn : ∀eta∈P,B (0,eta)≠0) :
    ∃ r L : ℝ, 0<r ∧ 0<L ∧ ∀eta∈P,∀ t d x y : ℂ,
      ‖t‖<r → ‖d‖<r → ‖x‖<r → ‖y‖<r →
      rootScalar (familyMember B eta) phi hphi (t,(d,x))-rootScalar (familyMember B eta) phi hphi (t,(d,y))=
        (x-y)*rootPairSlope (familyMember B eta) phi hphi t d x y ∧
      x*rootScalar (familyMember B eta) phi hphi (t,(d,x))-y*rootScalar (familyMember B eta) phi hphi (t,(d,y))=
        (x-y)*separablePairFactor (familyMember B eta) phi hphi t d x y ∧
      ‖rootPairSlope (familyMember B eta) phi hphi t d x y‖≤L*(‖d‖+‖x‖+‖y‖) ∧
      ‖separablePairFactor (familyMember B eta) phi hphi t d x y-rootScalar (familyMember B eta) phi hphi (t,(d,0))‖≤
        L*(‖d‖*(‖x‖+‖y‖)+‖x‖^2+‖y‖^2) := by
  obtain ⟨r₁,L₁,hr₁,hL₁,hpair⟩ := compact_family_pair_slope
    (fun q : ScalarTriple × E=>rootScalar (familyMember B q.2) phi hphi q.1) hP
    (fun eta heta=>family_rootEnergy_analyticAt B phi hphi eta (hB eta heta) (hBn eta heta))
    (fun eta _ t v=>congrArg Complex.sqrt (phaseEnergy_even_at_delta_zero (familyMember B eta) phi hphi t v))
  obtain ⟨r₂,L₂,hr₂,hL₂,hquad⟩ := compact_family_root_quadratic B phi hphi hP hB hBn
  let L := max L₁ L₂
  have hL : 0<L := lt_of_lt_of_le hL₁ (le_max_left _ _)
  refine ⟨min r₁ r₂,2*L,lt_min hr₁ hr₂,by positivity,?_⟩
  intro eta heta t d x y ht hd hx hy
  have hp := hpair eta heta t d x y (ht.trans_le (min_le_left _ _)) (hd.trans_le (min_le_left _ _))
    (hx.trans_le (min_le_left _ _)) (hy.trans_le (min_le_left _ _))
  have hq := hquad eta heta (t,(d,y)) (show ‖(t,(d,y))‖<r₂ from
    max_lt (ht.trans_le (min_le_right _ _)) (max_lt (hd.trans_le (min_le_right _ _)) (hy.trans_le (min_le_right _ _))))
  have hs : ‖rootPairSlope (familyMember B eta) phi hphi t d x y‖≤L*(‖d‖+‖x‖+‖y‖) :=
    hp.2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have hq' : ‖rootScalar (familyMember B eta) phi hphi (t,(d,y))-rootScalar (familyMember B eta) phi hphi (t,(d,0))‖≤L*(‖d‖+‖y‖)*‖y‖ :=
    hq.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)) (norm_nonneg _))
  refine ⟨hp.1,?_,hs.trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity)),?_⟩
  · have he : rootScalar (familyMember B eta) phi hphi (t,(d,x))=
        rootScalar (familyMember B eta) phi hphi (t,(d,y))+(x-y)*rootPairSlope (familyMember B eta) phi hphi t d x y := by
      dsimp [rootPairSlope] at *
      linear_combination hp.1
    rw [he]
    unfold separablePairFactor
    ring
  · have he : separablePairFactor (familyMember B eta) phi hphi t d x y-rootScalar (familyMember B eta) phi hphi (t,(d,0))=
        (rootScalar (familyMember B eta) phi hphi (t,(d,y))-rootScalar (familyMember B eta) phi hphi (t,(d,0)))+x*rootPairSlope (familyMember B eta) phi hphi t d x y := by
      unfold separablePairFactor
      ring
    rw [he]
    have hh := norm_add_le (rootScalar (familyMember B eta) phi hphi (t,(d,y))-rootScalar (familyMember B eta) phi hphi (t,(d,0)))
      (x*rootPairSlope (familyMember B eta) phi hphi t d x y)
    rw [norm_mul] at hh
    have hb := mul_le_mul_of_nonneg_left hs (norm_nonneg x)
    nlinarith [sq_nonneg (‖x‖-‖y‖),mul_nonneg hL.le (sq_nonneg (‖x‖-‖y‖)),
      mul_nonneg hL.le (sq_nonneg ‖x‖),mul_nonneg hL.le (sq_nonneg ‖y‖),
      mul_nonneg hL.le (mul_nonneg (norm_nonneg d) (add_nonneg (norm_nonneg x) (norm_nonneg y)))]

end
end IsingBulk.Joint.Negative
