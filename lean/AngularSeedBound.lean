import AngularSeedHairbrush

/-! Concrete finite hairbrush seed estimate with its finite-depth losses
explicit. Angular gain is absorbed against actual group overlap; the
original grid union is the set on the right-hand side. -/
namespace KakeyaFormal.AngularSeedBound
open AngularSeedPieces AngularSeedRealization AngularSeedSummation AngularSeedHairbrush
open WidthNormalization HairbrushScales
noncomputable section

/-- Exact common-volume normalization and angular-overlap cancellation. -/
theorem cancel_overlap_and_width {C rate lam δ tau W M D V L beta s : ℝ}
    (hC : 0 ≤ C) (hrate : 0 ≤ rate) (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hδ : 0 < δ) (htau : 0 < tau) (htau1 : tau ≤ 1) (hW : 0 < W) (hL : 0 < L)
    (hbeta : beta ≤ s)
    (hbound : C*(lam/W)^2*((3*rate/8)*M)*D*(δ/tau)^s/L ≤ 2*tau^(-beta)*(V/W)) :
    (C*(3*rate/16)/W)*lam^2*M*D*δ^s/L ≤ V := by
  let base := (C*(3*rate/16)/W)*lam^2*M*D/L
  let scale := tau^beta*W/2
  have hb : 0 ≤ base := by dsimp [base]; positivity
  have hs : 0 ≤ scale := by dsimp [scale]; positivity
  have htpow : tau^beta ≠ 0 := (Real.rpow_pos_of_pos htau beta).ne'
  calc
    _ = base*δ^s := by dsimp [base]; ring
    _ ≤ base*(tau^beta*(δ/tau)^s) :=
      mul_le_mul_of_nonneg_left (angular_gain_absorbs_overlap hδ htau htau1 hbeta) hb
    _ = scale*(C*(lam/W)^2*((3*rate/8)*M)*D*(δ/tau)^s/L) := by
      dsimp [base,scale]
      field_simp
      ring
    _ ≤ scale*(2*tau^(-beta)*(V/W)) := mul_le_mul_of_nonneg_left hbound hs
    _ = V := by
      dsimp [scale]
      rw [Real.rpow_neg htau.le]
      field_simp

/-- An actual finite two-ends/cap/separated shading obeys the seed power bound,
with the precise finite-depth constant and hairbrush logarithm still visible.
This is a theorem about the original grid union, not a supplied analytic seed. -/
theorem finite_seed_at_depth {k M : ℕ} (F : TubeFamily (k+2) M)
    {δ beta lam width alpha B m A : ℝ} (P : Pieces F δ beta)
    (hδ : 0 < δ) (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hbetaS : beta ≤ (m-1)/2)
    (hB : 1 ≤ B) (hm : 1 ≤ m) (hA : 1 ≤ A)
    (hadm : F.Admissible width δ) (hcomp : F.Comparable δ lam)
    (hsep : F.Separated δ) (hcap : F.CapBound δ m A)
    (hends : ∀ i, ∀ x : Space (k+2), ∀ r : ℝ, δ ≤ r → r ≤ 1 →
      (((F.shade i).filter (fun z => dist (cellCenter δ z) x ≤ r)).card:ℝ) ≤
        B*r^alpha*((F.shade i).card:ℝ)) :
    (seedConstant k P.J width alpha beta B m A*(3*retentionRate (k+1) P.J/16)/
      (widthFactor (k+2) width)^(k+2))*lam^2*(M:ℝ)*δ^(k+1)*δ^((m-1)/2)/
      (hairbrushLog k (δ/P.tau))^((5:ℝ)/2) ≤ δ^(k+2)*(F.unionCells.card:ℝ) := by
  have htau : 0 < P.tau := hδ.trans_le P.lower_scale
  have hδtau : 0 < δ/P.tau := div_pos hδ htau
  have hδtau1 : δ/P.tau ≤ 1 := (div_le_one htau).mpr P.lower_scale
  have hlog := hairbrushLog_pos (k := k) hδtau hδtau1
  exact cancel_overlap_and_width (seedConstant_pos k P.J width halpha hbeta hB hA).le
    (retentionRate_pos _ _).le (Nat.cast_nonneg M) (pow_pos hδ _).le
    hδ htau P.upper_scale (pow_pos (widthFactor_pos _ _) _) (Real.rpow_pos_of_pos hlog _)
    hbetaS (summed_hairbrush F P hδ hlam hlam1 halpha hbeta hB hm hA hadm hcomp hsep hcap hends)

end
end KakeyaFormal.AngularSeedBound
