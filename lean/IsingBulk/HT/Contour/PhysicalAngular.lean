import IsingBulk.First.WeightedResidue
import IsingBulk.Tail.RightExteriorRoots
import IsingBulk.Tail.CompactLimitingGeometry
import Mathlib.Analysis.SpecialFunctions.Arcosh

/-! Literal real high-temperature angular form factors.  The index `n` of
`physicalAngularCoefficient` is the number of independent angles, so the
particle number is `n+1`.  In particular zero independent angles is the genuine
one-particle term, with no dummy integration or altered factorial.

This independent staging leaf does not assert the angular/contour identity.
It fixes the physical source, its real branch, and the one-particle
normalization before that remaining integral theorem is attached. -/
namespace IsingBulk.HT.Contour
noncomputable section
open IsingBulk.First IsingBulk.Tail
open scoped BigOperators

/-- Positive physical rapidity for real exterior temperature `t>1`. -/
def physicalGamma (t phi : ℝ) : ℝ :=
  Real.arcosh (t+t⁻¹-Real.cos phi)

def physicalRoot (t phi : ℝ) : ℝ := Real.exp (-physicalGamma t phi)

def physicalZ {N : ℕ} (t : ℝ) (phi : Fin N → ℝ) : ℝ :=
  ∏ i, physicalRoot t (phi i)

/-- The complete squared pair product, in the published angular variables. -/
def physicalPairProduct {N : ℕ} (t : ℝ) (phi : Fin N → ℝ) : ℝ :=
  ∏ i, ∏ j ∈ Finset.univ.filter (fun j => i < j),
    (Real.sin ((phi i-phi j)/2) /
      Real.sinh ((physicalGamma t (phi i)+physicalGamma t (phi j))/2))^2

def physicalAngularWeight {N : ℕ} (t : ℝ) (phi : Fin N → ℝ) : ℝ :=
  (∏ i, (Real.sinh (physicalGamma t (phi i)))⁻¹) * physicalPairProduct t phi

/-- Last angle is minus the sum of the independent angles.  No reduction
modulo a period is needed because the source is periodic. -/
def physicalDependentAngles (n : ℕ) (phi : Fin n → ℝ) : Fin (n+1) → ℝ :=
  Fin.snoc (α := fun _ : Fin (n+1) => ℝ) phi (-∑ i, phi i)

/-- Published full-site angular coefficient with `n+1` particles. -/
def physicalAngularCoefficient (n : ℕ) (t : ℝ) : ℂ :=
  ((n+1).factorial:ℂ)⁻¹ * ((2*(Real.pi:ℂ))⁻¹)^n *
    multiAngleIntegral n (fun phi =>
      let psi := physicalDependentAngles n phi
      ((physicalAngularWeight t psi *
        ((1+physicalZ t psi)/(1-physicalZ t psi)):ℝ):ℂ))

/-- Literal lattice coefficient with N independent angles.  The vertical
coordinate is nonnegative, while the horizontal Fourier index is integral. -/
def physicalLatticeCoefficient (N : ℕ) (t : ℝ) (m : ℕ) (n : ℤ) : ℂ :=
  (N.factorial:ℂ)⁻¹ * ((2*(Real.pi:ℂ))⁻¹)^N *
    multiAngleIntegral N (fun phi =>
      ((physicalAngularWeight t phi * (physicalZ t phi)^m:ℝ):ℂ) *
        Complex.exp (Complex.I*(n:ℂ)*(∑ i, (phi i:ℂ))))

/-- The full lattice extension reflects the vertical coordinate. -/
def physicalFullLatticeCoefficient (N : ℕ) (t : ℝ) (v : ℤ × ℤ) : ℂ :=
  physicalLatticeCoefficient N t v.1.natAbs v.2

theorem physical_trace_gt_two {t : ℝ} (ht : 1 < t) : 2 < t+t⁻¹ := by
  have ht0 : 0 < t := lt_trans zero_lt_one ht
  have hprod : t*t⁻¹=1 := mul_inv_cancel₀ ht0.ne'
  apply (mul_lt_mul_iff_right₀ ht0).mp
  nlinarith [sq_pos_of_pos (sub_pos.mpr ht)]

theorem physical_W_gt_one {t : ℝ} (ht : 1 < t) (phi : ℝ) :
    1 < t+t⁻¹-Real.cos phi := by
  have hs := physical_trace_gt_two ht
  linarith [Real.cos_le_one phi]

theorem physicalGamma_pos {t : ℝ} (ht : 1 < t) (phi : ℝ) :
    0 < physicalGamma t phi := Real.arcosh_pos (physical_W_gt_one ht phi)

theorem physicalGamma_cosh {t : ℝ} (ht : 1 < t) (phi : ℝ) :
    Real.cosh (physicalGamma t phi) = t+t⁻¹-Real.cos phi :=
  Real.cosh_arcosh (physical_W_gt_one ht phi).le

theorem physicalRoot_bounds {t : ℝ} (ht : 1 < t) (phi : ℝ) :
    0 < physicalRoot t phi ∧ physicalRoot t phi < 1 := by
  exact ⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr (neg_neg_of_pos (physicalGamma_pos ht phi))⟩

/-- The branch already present in LT is exactly the positive real physical
root; the upper-half-plane `globalRoot` is not substituted on its branch cut. -/
theorem compactLeftRoot_eq_exp_neg_arcosh {w : ℝ} (hw : 1 < w) :
    compactLeftRoot (w:ℂ) = (Real.exp (-Real.arcosh w):ℂ) := by
  rw [compactLeftRoot_real_formula hw]
  congr 1
  calc
    w-Real.sqrt (w^2-1) =
        Real.cosh (Real.arcosh w)-Real.sinh (Real.arcosh w) := by
      rw [Real.cosh_arcosh hw.le, Real.sinh_arcosh hw.le]
    _ = _ := Real.cosh_sub_sinh (Real.arcosh w)

theorem sourceW_real_unit_angle (t phi : ℝ) :
    sourceW (t:ℂ) (limitingAngle phi) = ((t+t⁻¹-Real.cos phi:ℝ):ℂ) := by
  unfold sourceW
  rw [limitingAngle_trace]
  simp only [sourceS]
  push_cast
  ring

theorem rightRoot_real_unit_angle {t : ℝ} (ht : 1 < t) (phi : ℝ) :
    rightRoot (t:ℂ) (limitingAngle phi) = (physicalRoot t phi:ℂ) := by
  unfold rightRoot
  rw [sourceW_real_unit_angle, compactLeftRoot_eq_exp_neg_arcosh (physical_W_gt_one ht phi)]
  rfl

theorem physicalRoot_trace {t : ℝ} (ht : 1 < t) (phi : ℝ) :
    physicalRoot t phi+(physicalRoot t phi)⁻¹ =
      2*(t+t⁻¹-Real.cos phi) := by
  have he := Real.cosh_eq (physicalGamma t phi)
  rw [physicalGamma_cosh ht,Real.exp_neg] at he
  unfold physicalRoot
  rw [Real.exp_neg, inv_inv]
  linarith

/-- This is the exact one-body measure conversion used by the residue proof. -/
theorem physical_residueFactor {t : ℝ} (ht : 1 < t) (phi : ℝ) :
    residueFactor (physicalRoot t phi:ℂ) =
      (physicalRoot t phi / Real.sinh (physicalGamma t phi):ℝ) := by
  have hpos := physicalRoot_bounds ht phi
  have hE : Real.exp (physicalGamma t phi) ≠ 0 := (Real.exp_pos _).ne'
  have hg : Real.sinh (physicalGamma t phi) ≠ 0 :=
    (Real.sinh_pos_iff.mpr (physicalGamma_pos ht phi)).ne'
  have hgap : 1-(physicalRoot t phi)^2 ≠ 0 := by nlinarith [hpos.1,hpos.2]
  have hid : 2*(physicalRoot t phi)*Real.sinh (physicalGamma t phi) =
      1-(physicalRoot t phi)^2 := by
    rw [Real.sinh_eq, physicalRoot, Real.exp_neg]
    field_simp [hE]
  have hreal : 2*(physicalRoot t phi)^2/(1-(physicalRoot t phi)^2) =
      physicalRoot t phi/Real.sinh (physicalGamma t phi) := by
    apply (div_eq_div_iff hgap hg).mpr
    nlinarith [hid]
  unfold residueFactor
  exact_mod_cast hreal

/-- Closed scalar identity, with all nonzero denominators proved from gamma>0. -/
theorem physical_one_particle_scalar {gamma : ℝ} (hg : 0 < gamma) :
    (Real.sinh gamma)⁻¹ * ((1+Real.exp (-gamma))/(1-Real.exp (-gamma))) =
      (Real.cosh gamma-1)⁻¹ := by
  have hE : Real.exp gamma ≠ 0 := (Real.exp_pos _).ne'
  have hs : Real.sinh gamma ≠ 0 := (Real.sinh_pos_iff.mpr hg).ne'
  have hz : 1-Real.exp (-gamma) ≠ 0 :=
    sub_ne_zero.mpr (ne_of_gt (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hg)))
  have hc : Real.cosh gamma-1 ≠ 0 :=
    sub_ne_zero.mpr (Real.one_lt_cosh.mpr hg.ne').ne'
  have hid : (Real.cosh gamma-1)*(1+Real.exp (-gamma)) =
      Real.sinh gamma*(1-Real.exp (-gamma)) := by
    rw [Real.cosh_eq,Real.sinh_eq,Real.exp_neg]
    field_simp
    ring
  field_simp
  nlinarith [hid]

/-- N=1 in the literal published N-1-angle formula. -/
theorem physicalAngularCoefficient_one {t : ℝ} (ht : 1 < t) :
    physicalAngularCoefficient 0 t = ((t+t⁻¹-2)⁻¹:ℝ) := by
  have hscalar := physical_one_particle_scalar (physicalGamma_pos ht 0)
  rw [physicalGamma_cosh ht,Real.cos_zero] at hscalar
  have he : t+t⁻¹-1-1=t+t⁻¹-2 := by ring
  rw [he] at hscalar
  have hpsi : physicalDependentAngles 0 (Fin.elim0 : Fin 0 → ℝ) =
      (fun _ : Fin 1 => 0) := by
    funext i
    have hi : i = Fin.last 0 := Fin.ext (by omega)
    subst i
    dsimp only [physicalDependentAngles]
    rw [Fin.snoc_last]
    simp
  have hempty (i : Fin 1) : Finset.univ.filter (fun j : Fin 1 => i < j) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro j hj
    have hji : j = i := Fin.ext (by omega)
    exact (lt_irrefl i) (by simpa only [hji] using (Finset.mem_filter.mp hj).2)
  have hpair : physicalPairProduct t (fun _ : Fin 1 => 0) = 1 := by
    simp only [physicalPairProduct,hempty,Finset.prod_empty,Finset.prod_const_one]
  simp only [physicalAngularCoefficient,Nat.zero_add,Nat.factorial_one,
    Nat.cast_one,inv_one,pow_zero,one_mul,multiAngleIntegral,hpsi]
  simpa only [physicalAngularWeight,physicalZ,hpair,Finset.prod_const,Finset.card_univ,
    Fintype.card_fin,Nat.zero_add,pow_one,mul_one,physicalRoot] using congrArg (fun x : ℝ => (x:ℂ)) hscalar

/-- The normalization check C_1(1/s)=s/(1-s)^2 on the physical HT interval. -/
theorem physicalAngularCoefficient_one_inverse {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    physicalAngularCoefficient 0 s⁻¹ = (s/(1-s)^2:ℝ) := by
  rw [physicalAngularCoefficient_one ((one_lt_inv₀ hs).mpr hs1)]
  congr 1
  have hs0 : s ≠ 0 := hs.ne'
  have hid : s⁻¹+s-2=(1-s)^2/s := by
    field_simp [hs0]
    ring
  rw [inv_inv,hid,inv_div]

end
end IsingBulk.HT.Contour
