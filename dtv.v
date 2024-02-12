Require Import Coq.Reals.Reals.
Require Import Coq.Reals.Ranalysis1.
Require Import Psatz.

Open Scope R_scope.

Lemma FTC :
  forall (a b : R) (f F : R -> R),
  a <= b ->
  (forall x : R, a <= x <= b -> continuity_pt f x) ->
  (forall x : R, a <= x <= b -> derivable_pt_lim F x (f x)) ->
  RInt f a b = F b - F a.
Proof.
  intros a b f F Hab Hcont Hderiv.
  assert (Hf_integrable : forall x : R, a <= x <= b -> RInt_gen f (at_point x) (Rbar_locally' (at_point b))).
  { intros x Hx.
    apply (RInt_correct f (at_point x) (Rbar_locally' (at_point b))).
    intros P [eps [eps_pos Heps]].
    exists (mkposreal _ eps_pos).
    intros y Hy.
    apply Heps.
    split.
    - rewrite Rabs_right; try lra.
      apply Rle_ge.
      apply RInt_gen_Rle; auto.
      intros z [Hz1 Hz2].
      apply Hcont; lra.
    - exists x.
      split; try lra.
      intros z Hz.
      apply Hy.
      rewrite Rabs_right; try lra.
      apply Rle_ge.
      apply RInt_gen_Rle; auto.
      intros t [Ht1 Ht2].
      apply Hcont; lra. }
  assert (Hcont_F : forall x : R, a <= x <= b -> continuity_pt F x).
  { intros x Hx.
    apply continuity_pt_continuity_pt_lim.
    apply (derivable_continuous_pt F x (f x)).
    apply Hderiv; auto. }
  assert (Hf_integrable' : forall x : R, a <= x <= b -> ex_derive_pt F x).
  { intros x Hx.
    apply (ex_derive_pt_continuity_pt F x).
    apply Hcont_F; auto. }
  assert (Hdiff : forall x : R, a <= x <= b -> derivable_pt F x).
  { intros x Hx.
    apply (ex_derive_pt_derive_pt F x).
    apply Hf_integrable'; auto. }
  assert (Hcont_int : forall x : R, a <= x <= b -> continuity_pt (fun x => RInt f a x)).
  { intros x Hx.
    apply continuity_pt_continuity_pt_lim.
    apply (derivable_continuous_pt (fun x => RInt f a x) x (f x)).
    apply (derivable_pt_lim_RInt f (at_point a) (Rbar_locally' (at_point x))); auto.
    intros P [eps [eps_pos Heps]].
    exists (mkposreal _ eps_pos).
    intros y Hy.
    apply Heps.
    split.
    - intros z Hz.
      apply Hy.
      rewrite Rabs_right; try lra.
      apply Rle_ge.
      apply RInt_gen_Rle; auto.
      intros t [Ht1 Ht2].
      apply Hcont; lra.
    - rewrite Rabs_right; try lra.
      apply Rle_ge.
      apply RInt_gen_Rle; auto.
      intros z [Hz1 Hz2].
      apply Hcont; lra. }
  assert (Hcont_int' : forall x : R, a <= x <= b -> continuity_pt (fun x => F x - (RInt f a x))).
  { intros x Hx.
    apply continuity_pt_minus.
    - apply Hcont_F; auto.
    - apply Hcont_int; auto. }
  assert (Hdiff_int : forall x : R, a <= x <= b -> derivable_pt (fun x => F x - (RInt f a x)) x).
  { intros x Hx.
    apply derivable_pt_minus.
    - apply Hdiff; auto.
    - apply (derivable_pt_RInt (fun x => f x) a x).
      intros P [eps [eps_pos Heps]].
      exists (mkposreal _ eps_pos).
      intros y Hy.
      apply Heps.
      split.
      + intros z Hz.
        apply Hy.
        rewrite Rabs_right; try lra.
        apply Rle_ge.
        apply RInt_gen_Rle; auto.
        intros t [Ht1 Ht2].
        apply Hcont; lra.
      + rewrite Rabs_right; try lra.
        apply Rle_ge.
        apply RInt_gen_Rle; auto.
        intros z [Hz1 Hz2].
        apply Hcont; lra. }
  assert (Hdiff_int' : forall x : R, a <= x <= b -> derivable_pt_lim (fun x => F x - (RInt f a x)) x 0).
  { intros x Hx.
    apply (derivable_pt_lim_minus (fun x => F x) (fun x => RInt f a x) x).
    - apply (derivable_pt_lim_derivable_pt (fun x => F x - (RInt f a x)) x).
      apply Hdiff_int; auto.
    - apply (derivable_pt_lim_RInt (fun x => f x) a x).
      intros P [eps [eps_pos Heps]].
      exists (mkposreal _ eps_pos).
      intros y Hy.
      apply Heps.
      split.
      + intros z Hz.
        apply Hy.
        rewrite Rabs_right; try lra.
        apply Rle_ge.
        apply RInt_gen_Rle; auto.
        intros t [Ht1 Ht2].
        apply Hcont; lra.
      + rewrite Rabs_right; try lra.
        apply Rle_ge.
        apply RInt_gen_Rle; auto.
        intros z [Hz1 Hz2].
        apply Hcont; lra. }
  assert (Hdiff_int'' : forall x : R, a < x < b -> derivable_pt_lim (fun x => F x - (RInt f a x)) x (f x)).
  { intros x Hx.
    apply (is_derive_unique (fun x => F x - (RInt f a x)) x).
    apply (is_derive_ext_loc F).
    - exists (pos_div_2 (Rmin (x - a) (b - x))).
      intros y [_ Hy].
      unfold pos_div_2.
      apply Rlt_le_trans with (r2 := Rmin (x - a) (b - x)); try apply Hy.
      apply Rmin_r.
    - intros y Hy.
      unfold is_derive, minus_fct.
      rewrite <- is_derive_Reals.
      apply Hderiv.
      split; try lra.
      unfold abs, minus_fct, plus_fct.
      rewrite Rabs_right; try lra.
      apply Rle_ge.
      apply RInt_gen_Rle; auto.
      intros z [Hz1 Hz2].
      apply Hcont; lra. }
  destruct (Rtotal_order a b) as [Hab' | [Hab' | Hab']].
  - apply Hab' in Hab; lra.
  - rewrite (RInt_correct f (at_point a) (Rbar_locally' (at_point b))).
    + rewrite <- (is_RInt_unique f (RInt f a b)).
      * unfold continuity_pt, derivable_pt_lim in *.
        intros P [eps [eps_pos Heps]].
        exists (mkposreal _ eps_pos).
        intros y Hy.
        apply Heps.
        split.
        -- intros z Hz.
           apply Hy.
           rewrite Rabs_right; try lra.
           apply Rle_ge.
           apply RInt_gen_Rle; auto.
           intros t [Ht1 Ht2].
           apply Hcont; lra.
        -- rewrite Rabs_right; try lra.
           apply Rle_ge.
           apply RInt_gen_Rle; auto.
           intros z [Hz1 Hz2].
           apply Hcont; lra.
      * apply Hf_integrable; lra.
    + intros P [eps [eps_pos Heps]].
      exists (mkposreal _ eps_pos).
      intros y Hy.
      apply Heps.
      split.
      * intros z Hz.
        apply Hy.
        rewrite Rabs_right; try lra.
        apply Rle_ge.
        apply RInt_gen_Rle; auto.
        intros t [Ht1 Ht2].
        apply Hcont; lra.
      * rewrite Rabs_right; try lra.
        apply Rle_ge.
        apply RInt_gen_Rle; auto.
        intros z [Hz1 Hz2].
        apply Hcont; lra.
  - apply Hab' in Hab; lra.
Qed.
