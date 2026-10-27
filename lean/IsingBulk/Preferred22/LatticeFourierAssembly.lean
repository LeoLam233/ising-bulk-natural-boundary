import IsingBulk.Preferred22.HorizontalFourier
import IsingBulk.Preferred22.LatticeAssembly

/-! The exact full-lattice angular identity follows from the actual site
summability, the proved torus Fourier identity, and the proved two-sided
vertical sum. Only joint particle/site absolute summability remains open in
this part of the physical identification. -/
namespace IsingBulk.Preferred22
noncomputable section
open scoped BigOperators

theorem site_lattice_tsum_eq_coefficient {N : ℕ} (hN : 0 < N) {s : ℂ}
    (hs : 1 < ‖s‖)
    (hq : Summable (fun ab : ℤ × ℤ => siteCoefficient N ab.1 ab.2 s)) :
    (∑' ab : ℤ × ℤ,siteCoefficient N ab.1 ab.2 s)=coefficient N s := by
  cases N with
  | zero => omega
  | succ n =>
    have hrow (b : ℤ) : (∑' a : ℤ,siteCoefficient (n+1) a b s)=
        constrainedVerticalCoefficient n b s :=
      horizontal_site_tsum n hs b (hq.prod_symm.prod_factor b)
    calc
      (∑' ab : ℤ × ℤ,siteCoefficient (n+1) ab.1 ab.2 s) =
          ∑' a : ℤ,∑' b : ℤ,siteCoefficient (n+1) a b s := hq.tsum_prod
      _ = ∑' b : ℤ,∑' a : ℤ,siteCoefficient (n+1) a b s :=
        (Summable.tsum_comm (f := fun a b : ℤ => siteCoefficient (n+1) a b s) hq).symm
      _ = ∑' b : ℤ,constrainedVerticalCoefficient n b s := tsum_congr hrow
      _ = coefficient (n+1) s :=
        (constrainedVerticalCoefficient_summable_eq_coefficient n hs).2

/-- Exact remaining physical series interchange obligation; no published
input is enlarged to contain this statement. -/
def PreferredJointSiteSummability : Prop :=
  ∀ x : ℝ, 1 < x → Summable (fun q : ℕ × (ℤ × ℤ) =>
    ‖siteCoefficient (2*(q.1+1)) q.2.1 q.2.2 (x:ℂ)‖)

theorem latticeFubini_of_joint (hjoint : PreferredJointSiteSummability) :
    PreferredLatticeFubiniStatement := by
  intro x hx
  refine ⟨hjoint x hx,?_⟩
  intro n
  have hs : 1 < ‖(x:ℂ)‖ := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by linarith)]
    exact hx
  exact site_lattice_tsum_eq_coefficient (by omega) hs
    ((hjoint x hx).prod_factor n).of_norm

/-- CONDITIONAL full-scope assembly with the physical residual reduced to
the exact joint absolute summability statement. The selected first/finite/tail
obligations are still explicit and unproved premises. -/
theorem preferredFullTarget_of_joint_obligations
    (hjoint : PreferredJointSiteSummability)
    (hselected : PreferredSelectedAnalyticObligations) : PreferredFullTarget :=
  preferredFullTarget_of_obligations (latticeFubini_of_joint hjoint) hselected

end
end IsingBulk.Preferred22
