import IsingBulk.Anisotropic.NegativeNormalForm.ScalarPairSlope

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open Set Metric Filter
open scoped Topology

def rootScalar (B : ℂ → ℂ) (phi : ℝ) (hphi : Real.sin phi≠0) (p : ScalarTriple) : ℂ :=
  Complex.sqrt (phaseEnergy B phi hphi p.2.1 p.1 p.2.2)

def rootPairSlope (B : ℂ → ℂ) (phi : ℝ) (hphi : Real.sin phi≠0) (t d x y : ℂ) : ℂ :=
  scalarPairSlope (rootScalar B phi hphi) ((t,(d,y)),x-y)

def separablePairFactor (B : ℂ → ℂ) (phi : ℝ) (hphi : Real.sin phi≠0) (t d x y : ℂ) : ℂ :=
  rootScalar B phi hphi (t,(d,y))+x*rootPairSlope B phi hphi t d x y

/-- Scalar pair bounds retain each coordinate's energy, rather than replacing
all coordinates by the configuration sup norm. Constants precede every n. -/
theorem rootPair_uniform_bounds (B : ℂ → ℂ) (phi : ℝ) (hphi : Real.sin phi≠0)
    (hB : AnalyticAt ℂ B 0) (hBn : B 0≠0) :
    ∃ r L : ℝ, 0<r ∧ 0<L ∧ ∀ t d x y : ℂ,
      ‖t‖<r → ‖d‖<r → ‖x‖<r → ‖y‖<r →
      rootScalar B phi hphi (t,(d,x))-rootScalar B phi hphi (t,(d,y))=
        (x-y)*rootPairSlope B phi hphi t d x y ∧
      x*rootScalar B phi hphi (t,(d,x))-y*rootScalar B phi hphi (t,(d,y))=
        (x-y)*separablePairFactor B phi hphi t d x y ∧
      ‖rootPairSlope B phi hphi t d x y‖≤L*(‖d‖+‖x‖+‖y‖) ∧
      ‖separablePairFactor B phi hphi t d x y-rootScalar B phi hphi (t,(d,0))‖≤
        L*(‖d‖*(‖x‖+‖y‖)+‖x‖^2+‖y‖^2) := by
  obtain ⟨r₁,L₁,hr₁,hL₁,hpair⟩ := scalarPairSlope_even_uniform (rootScalar B phi hphi)
    (phaseRootEnergy_triple_analyticAt B phi hphi hB hBn)
    (fun t v => congrArg Complex.sqrt (phaseEnergy_even_at_delta_zero B phi hphi t v))
  obtain ⟨r₂,L₂,hr₂,hL₂,hquad⟩ := phaseRootEnergy_quadratic_control B phi hphi hB hBn
  let L := max L₁ L₂
  have hL : 0<L := lt_of_lt_of_le hL₁ (le_max_left _ _)
  refine ⟨min r₁ r₂,2*L,lt_min hr₁ hr₂,by positivity,?_⟩
  intro t d x y ht hd hx hy
  have hp := hpair t d x y (ht.trans_le (min_le_left _ _)) (hd.trans_le (min_le_left _ _))
    (hx.trans_le (min_le_left _ _)) (hy.trans_le (min_le_left _ _))
  have hq := hquad (t,(d,y)) (show ‖(t,(d,y))‖<r₂ from
    max_lt (ht.trans_le (min_le_right _ _)) (max_lt (hd.trans_le (min_le_right _ _)) (hy.trans_le (min_le_right _ _))))
  have hs : ‖rootPairSlope B phi hphi t d x y‖≤L*(‖d‖+‖x‖+‖y‖) :=
    hp.2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have hq' : ‖rootScalar B phi hphi (t,(d,y))-rootScalar B phi hphi (t,(d,0))‖≤L*(‖d‖+‖y‖)*‖y‖ :=
    hq.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)) (norm_nonneg _))
  refine ⟨hp.1,?_,hs.trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity)),?_⟩
  · have he : rootScalar B phi hphi (t,(d,x))=
        rootScalar B phi hphi (t,(d,y))+(x-y)*rootPairSlope B phi hphi t d x y := by
      dsimp [rootPairSlope] at *
      linear_combination hp.1
    rw [he]
    unfold separablePairFactor
    ring
  · have he : separablePairFactor B phi hphi t d x y-rootScalar B phi hphi (t,(d,0))=
        (rootScalar B phi hphi (t,(d,y))-rootScalar B phi hphi (t,(d,0)))+x*rootPairSlope B phi hphi t d x y := by
      unfold separablePairFactor
      ring
    rw [he]
    have hh := norm_add_le (rootScalar B phi hphi (t,(d,y))-rootScalar B phi hphi (t,(d,0)))
      (x*rootPairSlope B phi hphi t d x y)
    rw [norm_mul] at hh
    have hb := mul_le_mul_of_nonneg_left hs (norm_nonneg x)
    nlinarith [sq_nonneg (‖x‖-‖y‖),mul_nonneg hL.le (sq_nonneg (‖x‖-‖y‖)),
      mul_nonneg hL.le (sq_nonneg ‖x‖),mul_nonneg hL.le (sq_nonneg ‖y‖),
      mul_nonneg hL.le (mul_nonneg (norm_nonneg d) (add_nonneg (norm_nonneg x) (norm_nonneg y)))]

end
end IsingBulk.Anisotropic.NegativeNormalForm
