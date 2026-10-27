import IsingBulk.Preferred22.SelectedGaugeBounds
import IsingBulk.Preferred22.Hadamard

/-! The selected root continuation preserves every physical pair margin
and the full row estimate. The numerator and real angle weights are held
fixed, including all zero entries, while the actual roots move. -/
namespace IsingBulk.Preferred22
noncomputable section
open scoped BigOperators Matrix ComplexOrder
set_option maxHeartbeats 1500000

lemma preferred_relative_root_norm_bounds {u v : ℂ} {δ : ℝ}
    (hu : u≠0) (hδ : δ≤1) (hv : ‖v/u-1‖≤δ) :
    ‖v‖≤2*‖u‖ ∧ ‖v-u‖≤δ*‖u‖ := by
  have he : v-u=(v/u-1)*u := by field_simp
  have hd : ‖v-u‖≤δ*‖u‖ := by rw [he,norm_mul]; exact mul_le_mul_of_nonneg_right hv (norm_nonneg _)
  have hn := norm_sub_norm_le v u
  have hh := mul_le_mul_of_nonneg_right hδ (norm_nonneg u)
  exact ⟨by linarith,hd⟩

theorem preferred_pair_relative_preservation {u v u' v' : ℂ} {δ d : ℝ}
    (hu : u≠0) (hv : v≠0) (hu1 : ‖u‖≤1) (hv1 : ‖v‖≤1)
    (hδ : 0≤δ) (hδ1 : δ≤1) (hd : 0<d) (hδd : 6*δ≤d)
    (hpair : d≤‖1-u*v‖) (hu' : ‖u'/u-1‖≤δ) (hv' : ‖v'/v-1‖≤δ) :
    ‖1-u*v‖/2≤‖1-u'*v'‖ ∧ 1-u'*v'≠0 := by
  obtain ⟨hu'n,hud⟩ := preferred_relative_root_norm_bounds hu hδ1 hu'
  obtain ⟨hv'n,hvd⟩ := preferred_relative_root_norm_bounds hv hδ1 hv'
  have hud' : ‖u'-u‖≤δ := hud.trans ((mul_le_mul_of_nonneg_left hu1 hδ).trans_eq (mul_one _))
  have hvd' : ‖v'-v‖≤δ := hvd.trans ((mul_le_mul_of_nonneg_left hv1 hδ).trans_eq (mul_one _))
  have hm : ‖u'*v'-u*v‖≤3*δ := by
    have he : u'*v'-u*v=(u'-u)*v'+u*(v'-v) := by ring
    rw [he]
    calc
      _ ≤ ‖u'-u‖*‖v'‖+‖u‖*‖v'-v‖ := by simpa only [norm_mul] using norm_add_le ((u'-u)*v') (u*(v'-v))
      _ ≤ δ*2+1*δ := add_le_add
        (mul_le_mul hud' (by linarith : ‖v'‖≤2) (norm_nonneg _) hδ)
        (mul_le_mul hu1 hvd' (norm_nonneg _) (by norm_num))
      _ = _ := by ring
  have hnorm := norm_sub_norm_le (1-u*v) (1-u'*v')
  have he : (1-u*v)-(1-u'*v')=u'*v'-u*v := by ring
  rw [he] at hnorm
  have hl : ‖1-u*v‖/2≤‖1-u'*v'‖ := by linarith
  refine ⟨hl,?_⟩
  exact norm_pos_iff.mp ((by linarith : 0<‖1-u*v‖/2).trans_le hl)

theorem preferred_gaugeKernel_relative_squared_bound {N : ℕ}
    (y z z' : Fin N → ℂ) (i j : Fin N) {δ d : ℝ}
    (hzi : z i≠0) (hzj : z j≠0) (hzi1 : ‖z i‖≤1) (hzj1 : ‖z j‖≤1)
    (hδ : 0≤δ) (hδ1 : δ≤1) (hd : 0<d) (hδd : 6*δ≤d)
    (hpair : d≤‖1-z i*z j‖)
    (hi : ‖z' i/z i-1‖≤δ) (hj : ‖z' j/z j-1‖≤δ) :
    1-z' i*z' j≠0 ∧ ‖gaugeKernel y z' i j‖^2≤16*‖gaugeKernel y z i j‖^2 := by
  obtain ⟨hden,hne⟩ := preferred_pair_relative_preservation hzi hzj hzi1 hzj1 hδ hδ1 hd hδd hpair hi hj
  have hni := (preferred_relative_root_norm_bounds hzi hδ1 hi).1
  have hnj := (preferred_relative_root_norm_bounds hzj hδ1 hj).1
  have hratio : ‖y i-y j‖/‖1-z' i*z' j‖≤2*(‖y i-y j‖/‖1-z i*z j‖) := by
    calc
      _ ≤ ‖y i-y j‖/(‖1-z i*z j‖/2) :=
        div_le_div_of_nonneg_left (norm_nonneg _) (by linarith) hden
      _ = _ := by ring
  have hri : ‖z' i‖/‖y i‖≤2*(‖z i‖/‖y i‖) := by
    simpa only [mul_div_assoc] using div_le_div_of_nonneg_right hni (norm_nonneg (y i))
  have hrj : ‖z' j‖/‖y j‖≤2*(‖z j‖/‖y j‖) := by
    simpa only [mul_div_assoc] using div_le_div_of_nonneg_right hnj (norm_nonneg (y j))
  refine ⟨hne,?_⟩
  rw [preferred_gaugeKernel_norm_sq,preferred_gaugeKernel_norm_sq]
  have hs := sq_le_sq₀ (by positivity : 0≤‖y i-y j‖/‖1-z' i*z' j‖)
    (by positivity : 0≤2*(‖y i-y j‖/‖1-z i*z j‖)) |>.mpr hratio
  have hh := mul_le_mul (mul_le_mul hri hrj (by positivity) (by positivity)) hs (sq_nonneg _)
    (by positivity : 0≤(2*(‖z i‖/‖y i‖))*(2*(‖z j‖/‖y j‖)))
  exact hh.trans_eq (by ring)

theorem preferred_determinant_of_row_squares {N : ℕ} (hN : 0<N)
    (A : Matrix (Fin N) (Fin N) ℂ) {C : ℝ} (hC : 0≤C)
    (hrow : ∀ i,∑ j,‖A i j‖^2≤C^2*(N:ℝ)) :
    ‖A.det‖≤(C*Real.sqrt N)^N := by
  let H := Aᴴ*A
  have hH : H.PosSemidef := Matrix.posSemidef_conjTranspose_mul_self A
  let a : Fin N → ℝ := hH.isHermitian.eigenvalues
  have ha : ∀ i,0≤a i := hH.eigenvalues_nonneg
  have hd : ‖A.det‖^2=∏ i,a i := by
    have he := hH.isHermitian.det_eq_prod_eigenvalues
    rw [show H.det=(‖A.det‖^2:ℝ) from gram_det_eq_norm_det_sq A] at he
    rw [←RCLike.ofReal_prod] at he
    exact RCLike.ofReal_injective he
  have ht : ∑ i,a i=H.trace.re := by
    have he := congrArg (RCLike.re : ℂ → ℝ) hH.isHermitian.trace_eq_sum_eigenvalues
    simpa only [map_sum,RCLike.ofReal_re,RCLike.re_eq_complex_re] using he.symm
  have htrace : H.trace.re≤(N:ℝ)*(C^2*(N:ℝ)) := by
    rw [gram_trace_re,Finset.sum_comm]
    exact (Finset.sum_le_sum (fun i _ => hrow i)).trans_eq (by simp)
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  have hmean : (∑ i,a i)/(N:ℝ)≤C^2*(N:ℝ) := by
    apply (div_le_iff₀ hNr).mpr
    rw [ht]
    nlinarith
  have hsq : ‖A.det‖^2≤(C^2*(N:ℝ))^N := by
    rw [hd]
    exact (nonnegative_product_le_mean_pow hN a ha).trans
      (pow_le_pow_left₀ (div_nonneg (Finset.sum_nonneg (fun i _ => ha i)) hNr.le) hmean N)
  have hp : ((C*Real.sqrt N)^N)^2=(C^2*(N:ℝ))^N := by
    rw [←pow_mul,mul_comm N 2,pow_mul,mul_pow,Real.sq_sqrt (by positivity)]
  nlinarith [norm_nonneg A.det,pow_nonneg (mul_nonneg hC (Real.sqrt_nonneg (N:ℝ))) N]

end
end IsingBulk.Preferred22
