import IsingBulk.HT22.Transport.SourceField

/-! # Stability of the genuine mixed complex covariance

These are pointwise finite-dimensional estimates, not assumptions on a
transported scalar or on an old LT22 residual. The parameter `H` represents
`sqrt T`, and is kept separate from the diameter `d` throughout.
-/
namespace IsingBulk.HT22
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Two independent pair factors are perturbed; no Hermitian replacement. -/
theorem mixedCovariance_perturbation {N : ℕ}
    (u v u' v' : Fin N → ℂ) (A B a b : ℝ)
    (hA : 0≤A) (hB : 0≤B) (ha : 0≤a) ( _hb : 0≤b)
    (hu : ∀ i j, ‖u i-u j‖≤A) (hv : ∀ i j, ‖v i-v j‖≤B)
    (hdu : ∀ i j, ‖(u' i-u' j)-(u i-u j)‖≤a)
    (hdv : ∀ i j, ‖(v' i-v' j)-(v i-v j)‖≤b) :
    ‖mixedCovariance u' v'-mixedCovariance u v‖ ≤
      (N:ℝ)^2*(A*b+B*a+a*b)/2 := by
  have hp (i j : Fin N) :
      ‖(u' i-u' j)*(v' i-v' j)-(u i-u j)*(v i-v j)‖≤A*b+B*a+a*b := by
    have he : (u' i-u' j)*(v' i-v' j)-(u i-u j)*(v i-v j) =
        (u i-u j)*((v' i-v' j)-(v i-v j))+
        (v i-v j)*((u' i-u' j)-(u i-u j))+
        ((u' i-u' j)-(u i-u j))*((v' i-v' j)-(v i-v j)) := by ring
    rw [he]
    apply (norm_add_le _ _).trans
    apply (add_le_add (norm_add_le _ _) le_rfl).trans
    simp only [norm_mul]
    exact add_le_add (add_le_add (mul_le_mul (hu i j) (hdv i j) (norm_nonneg _) hA)
      (mul_le_mul (hv i j) (hdu i j) (norm_nonneg _) hB))
      (mul_le_mul (hdu i j) (hdv i j) (norm_nonneg _) ha)
  have hs : ‖∑ i, ∑ j, ((u' i-u' j)*(v' i-v' j)-(u i-u j)*(v i-v j))‖ ≤
      (N:ℝ)^2*(A*b+B*a+a*b) := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _i : Fin N, ∑ _j : Fin N, (A*b+B*a+a*b) :=
        Finset.sum_le_sum (fun i _ => (norm_sum_le _ _).trans
          (Finset.sum_le_sum (fun j _ => hp i j)))
      _ = _ := by simp; ring
  have he : mixedCovariance u' v'-mixedCovariance u v =
      (∑ i, ∑ j, ((u' i-u' j)*(v' i-v' j)-(u i-u j)*(v i-v j)))/2 := by
    simp only [mixedCovariance, Finset.sum_sub_distrib]
    ring
  rw [he, norm_div, Complex.norm_two]
  exact div_le_div_of_nonneg_right hs (by norm_num)

/-- One `d/N²` perturbation retains the actual mixed-covariance margin. -/
theorem mixedCovariance_scaled_margin {N : ℕ} (hN : 0<N)
    (u v u' v' : Fin N → ℂ) (C H d c η : ℝ)
    (hC : 0<C) (hH : 0<H) (hd : 0<d) (hc : 0<c)
    (hη : 0<η) (hη1 : η≤1) (hηc : η≤c/(4*C^2))
    (hu : ∀ i j, ‖u i-u j‖≤C*H*d)
    (hv : ∀ i j, ‖v i-v j‖≤C*d)
    (hdu : ∀ i j, ‖(u' i-u' j)-(u i-u j)‖≤C*H*η*d/(N:ℝ)^2)
    (hdv : ∀ i j, ‖(v' i-v' j)-(v i-v j)‖≤C*η*d/(N:ℝ)^2)
    (hR : c*H*d^2≤‖mixedCovariance u v‖) :
    c*H*d^2/2≤‖mixedCovariance u' v'‖ := by
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have hn1 : (1:ℝ)≤N := by exact_mod_cast hN
  have hn2 : (1:ℝ)≤(N:ℝ)^2 := one_le_pow₀ hn1
  have he1 : C*H*η*d/(N:ℝ)^2≤C*H*d := by
    calc
      _ ≤ C*H*η*d := div_le_self (by positivity) hn2
      _ = (C*H*d)*η := by ring
      _ ≤ _ := mul_le_of_le_one_right (by positivity) hη1
  have hp := mixedCovariance_perturbation u v u' v'
    (C*H*d) (C*d) (C*H*η*d/(N:ℝ)^2) (C*η*d/(N:ℝ)^2)
    (by positivity) (by positivity) (by positivity) (by positivity) hu hv hdu hdv
  have herr : ‖mixedCovariance u' v'-mixedCovariance u v‖≤c*H*d^2/2 := by
    calc
      _ ≤ (N:ℝ)^2*((C*H*d)*(C*η*d/(N:ℝ)^2)+
          (C*d)*(C*H*η*d/(N:ℝ)^2)+(C*H*d)*(C*η*d/(N:ℝ)^2))/2 := by
        exact hp.trans (by gcongr)
      _ = (3/2:ℝ)*C^2*H*η*d^2 := by field_simp; ring
      _ ≤ c*H*d^2/2 := by
        have hh := (le_div_iff₀ (by positivity : 0<4*C^2)).mp hηc
        have hcoef : (3/2:ℝ)*C^2*η≤c/2 := by nlinarith [show 0≤C^2*η by positivity]
        convert mul_le_mul_of_nonneg_right hcoef (by positivity : 0≤H*d^2) using 1 <;> ring
  have htri := norm_sub_le (mixedCovariance u' v')
    (mixedCovariance u' v'-mixedCovariance u v)
  rw [sub_sub_cancel] at htri
  linarith

/-- Actual numerator and covariance bounds give a residual bound. -/
theorem mixedCollectiveField_norm_bound {N : ℕ}
    (u v uDot : Fin N → ℂ) (A D r : ℝ)
    (hA : 0≤A) (hD : 0≤D) (hr : 0<r)
    (hu : ∀ i j, ‖u i-u j‖≤D) (hdot : ∀ i, ‖uDot i‖≤A)
    (hR : r≤‖mixedCovariance u v‖) :
    ‖mixedCollectiveField u v uDot‖≤(N:ℝ)^2*A*D/r := by
  have hsum : ‖∑ i, uDot i‖≤(N:ℝ)*A :=
    (norm_sum_le _ _).trans (by simpa using Finset.sum_le_sum (s := Finset.univ) (fun i _ => hdot i))
  have hg (i : Fin N) : ‖centeredAngleSum u i‖≤(N:ℝ)*D :=
    (norm_sum_le _ _).trans (by simpa using Finset.sum_le_sum (s := Finset.univ) (fun j _ => hu i j))
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  simp only [mixedCollectiveField, norm_mul, norm_div, norm_neg]
  calc
    _ ≤ ((N:ℝ)*A/r)*((N:ℝ)*D) :=
      mul_le_mul (div_le_div₀ (by positivity) hsum hr hR) (hg i) (norm_nonneg _) (by positivity)
    _ = _ := by ring

end
end IsingBulk.HT22
