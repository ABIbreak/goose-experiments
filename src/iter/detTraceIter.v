From sys_verif.program_proof Require Import prelude empty_ffi.
From New.proof Require Import std.
From New.generatedproof.sys_verif_code Require Import iterator.

Section proof.
Context `{hG: !heapGS Σ} `{!globalsGS Σ} {go_ctx: GoContext}.

#[global] Instance : IsPkgInit iterator := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf iterator := build_get_is_pkg_init_wf.


Definition is_detTraceIter V `{!IntoVal V} (detTraceIter : func.t) (trace : list V) (P : list V → iPropI Σ) Φ : iPropI Σ :=
  ∀ (yield : func.t), (
    "HP" :: P([]) ∗
    "#Hyield" :: □(
      ∀ (v : V) (vs : list V) (i : nat),
        (⌜ vs ++ [v] = firstn (S i) trace ⌝ (* -* vs <> trace also! *) ∗ P(vs)) -∗
        WP #yield #v {{ 
          ok,
          if (decide (ok = #true)) then
            P((vs ++ [v])%list)
          else if (decide (ok = #false)) then
            Φ
          else
            False
        }}
    ) ∗
    "Htrace" :: (P(trace) -∗ Φ) 
  )%I -∗
  WP #detTraceIter #yield {{
    _, Φ
  }}.

(* TODO: suprised that this isn't in the Rocq stdlib but the converse is? maybe should upstream? *)
Lemma firstn_n_length :
  ∀ (A : Type) (i : nat) (l : list A), take i l = l -> i >= length l.
Proof.
  induction i.
  - intros l Htake.
    rewrite firstn_0 in Htake.
    subst.
    simpl.
    lia.
  - induction l.
    + simpl.
      intros ?.
      lia.
    + rewrite firstn_cons.
      intros ?.
      assert (take i l = l) by congruence.
      simpl.
      apply IHi in H0.
      lia.
Qed.

(* TODO: why isn't this also in the Rocq stdlib?? *)
Lemma In_take_imp_In_list :
  ∀(A : Type) (x : A) (xs : list A) (n : nat), In x (firstn n xs) → In x xs.
Proof.
  intros A x xs n HIn.
  apply list_elem_of_In in HIn.
  apply list_elem_of_In.
  apply elem_of_take in HIn.
  destruct HIn as [i [? ?]].
  apply (list_elem_of_lookup_2 xs i x).
  trivial.
Qed.

Lemma wp_sliceIter slice vs P Φ' :
  {{{ 
    is_pkg_init iterator ∗ 
    "#Hslice" :: own_slice slice DfracDiscarded vs
  }}}
    @! iterator.sliceIter #uint8T #slice
  {{{
    (f : func.t), RET #f;
    is_detTraceIter w8 f vs P Φ'
  }}}.
Proof.
  wp_start.
  iNamed "Hpre".
  wp_auto.
  iApply "HΦ".
  unfold is_detTraceIter.
  iIntros (yield) "Hpre".
  iNamed "Hpre".
  iDestruct (own_slice_len with "Hslice") as "[%Hlength %Hslice_len]".
  wp_auto.
  iAssert (
    ∃(i : w64) (v : w8),
    "i" :: i_ptr ↦ i ∗
    "v" :: v_ptr ↦ v ∗ (* v = (vs !!! (sint.nat i)) *)
    "HP" :: P(firstn (sint.nat i) vs) ∗
    "%Hi" :: ⌜ 0 ≤ sint.Z i ≤ length vs ⌝
  )%I with "[HP i v]" as "Hinv".
  {
    iFrame.
    replace (sint.Z (W64 0)) with 0 by word.
    iSplitL ; word.
  }
  wp_for "Hinv".
  wp_if_destruct.
  {
    wp_bind (slice.elem_ref (# uint8T) (# slice) (# i)).
    wp_pure ; first word.
    wp_auto.

    assert (sint.nat i < length vs)%nat as Hi3 by word.
    apply list_lookup_lookup_total_lt in Hi3.

    wp_apply (wp_load_slice_elem slice i vs DfracDiscarded _) ; first lia.
    {
      iSplitL.
      - iApply "Hslice".
      - done.
    }
    iIntros "_".
    wp_auto.
    wp_bind (#yield (#_)).
    iApply (wp_wand with "[HP]").
    {
      iApply ("Hyield" $! (vs !!! sint.nat i) (firstn (sint.nat i) vs) (sint.nat i)).
      iFrame.
      iPureIntro.
      pose proof (take_S_r vs (sint.nat i) (vs !!! (sint.nat i))).
      apply H in Hi3.
      done.
    }
    iIntros (?) "Hpost".
    destruct (decide _).
    {
      subst.
      wp_auto.
      wp_for_post.
      iFrame.
      iSplitL.
      - replace (sint.nat (word.add i (W64 1))) with (S (sint.nat i))%nat by word.
        simpl.
        pose proof (take_S_r vs (sint.nat i) (vs !!! sint.nat i)) as Htake.
        rewrite Htake ; first done.
        done.
      - word.
    }
    destruct (decide _).
    {
      subst.
      wp_auto.
      wp_for_post.
      iFrame.
    }
    done.
  }
  iApply "Htrace".
  replace (sint.nat i) with (length vs) by word.
  replace (take (length vs) vs) with vs by (symmetry ; apply firstn_all).
  done.
Qed.

Definition isAscii (vs : list w8) : Prop :=
  Forall (λ c, (uint.Z c ≠ 0) ∧ (uint.Z c < 0x80)) vs.

Lemma wp_isAscii slice vs :
  {{{
    is_pkg_init iterator ∗
    "#Hslice" :: own_slice slice DfracDiscarded vs
  }}}
    @! iterator.isAscii #slice
  {{{
    (b : bool), RET #b; ⌜ b = bool_decide (isAscii vs) ⌝
  }}}.
Proof.
  wp_start.
  iNamed "Hpre".
  wp_auto.
  iPersist "str".
  wp_apply (
    wp_sliceIter
    slice 
    vs
    (
      λ l,
      "%HisAscii" :: ⌜ isAscii l ⌝ ∗ 
      "ret_val" :: ret_val_ptr ↦ bool_decide (isAscii l)
    )%I
    (ret_val_ptr ↦ bool_decide (isAscii vs))%I
  ) ; first done.
  iIntros (?) "HdetTraceIter".
  wp_auto.
  unfold is_detTraceIter.
  wp_bind (#f (#_)).
  iApply (wp_wand with "[ret_val HdetTraceIter]").
  {
    iApply "HdetTraceIter".
    iFrame.
    iSplitR.
    {
      iPureIntro.
      unfold isAscii.
      done.
    }
    iSplitL.
    2: {
      iIntros "Hpost".
      iNamed "Hpost".
      iFrame.
    }
    iModIntro.
    iIntros (v vs' i) "[%Hvs asdf]".
    iNamed "asdf".
    wp_auto.
    wp_if_destruct.
    {
      rewrite bool_decide_eq_false_2.
      {
        unfold isAscii.
        apply Exists_not_Forall.
        apply Exists_exists.
        exists v.
        split.
        - apply (In_take_imp_In_list _ v vs (S i)).
          rewrite <- Hvs.
          apply in_or_app.
          right.
          apply list_elem_of_In.
          set_solver.
        - simpl. word.
      }
      done.
    }
    wp_if_destruct.
    {
      rewrite bool_decide_eq_false_2.
      {
        unfold isAscii.
        apply Exists_not_Forall.
        apply Exists_exists.
        exists (W8 0).
        split.
        - apply (In_take_imp_In_list _ (W8 0) vs (S i)).
          rewrite <- Hvs.
          apply in_or_app.
          right.
          apply list_elem_of_In.
          set_solver.
        - simpl. word.
      }
      done.
    }
    assert (isAscii (vs' ++ [v])).
    {
      unfold isAscii.
      apply Forall_app_2.
      - unfold isAscii in HisAscii.
        done.
      - apply Forall_singleton.
        word.
    }
    iSplitR ; first done.
    rewrite bool_decide_eq_true_2 ; first done.
    iFrame.
  }
  iIntros (?) "ret_val".
  wp_auto.
  iApply "HΦ".
  done.
Qed.
