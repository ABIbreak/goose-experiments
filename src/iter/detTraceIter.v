From sys_verif.program_proof Require Import prelude empty_ffi.
From New.proof Require Import std.
From New.generatedproof.sys_verif_code Require Import iterator.

Section proof.
Context `{hG: !heapGS Σ} `{!globalsGS Σ} {go_ctx: GoContext}.

#[global] Instance : IsPkgInit iterator := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf iterator := build_get_is_pkg_init_wf.

Definition is_detTraceIter V `{!IntoVal V} (detTraceIter yield : func.t) (trace : list V) (P : list V → iPropI Σ) Φ : iPropI Σ :=
  (
    "HP" :: P([]) ∗
    "#Hyield" :: □(
      ∀ (v : V) (vs : list V),
        (⌜ vs ≠ trace ⌝ ∗ P(vs)) -∗
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
    "Hlimit" :: (P(trace) -∗ Φ) 
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

Lemma wp_sliceIter yield slice vs P Φ' :
  {{{ 
    is_pkg_init iterator ∗ 
    "#Hslice" :: own_slice slice DfracDiscarded vs
  }}}
    @! iterator.sliceIter #uint8T #slice
  {{{
    (f : func.t), RET #f;
    is_detTraceIter w8 f yield vs P Φ'
  }}}.
Proof.
  wp_start.
  iNamed "Hpre".
  wp_auto.
  iApply "HΦ".
  unfold is_detTraceIter.
  iIntros "Hpre".
  iNamed "Hpre".
  iDestruct (own_slice_len slice DfracDiscarded vs with "Hslice") as "[%Hlength %Hslice_len]".
  wp_auto.
  iAssert (
    ∃(i : w64) (v : w8),
    "i" :: i_ptr ↦ i ∗
    "v" :: v_ptr ↦ v ∗
    "HP" :: P(firstn (sint.nat i) vs) ∗
    "%Hi" :: ⌜ 0 ≤ sint.Z i ≤ length vs ⌝
  )%I with "[HP i v]" as "Hinv".
  {
    iFrame.
    replace (sint.Z (W64 0)) with 0 by word.
    word.
  }
  wp_for "Hinv".
  wp_if_destruct.
  {
    wp_bind (slice.elem_ref (# uint8T) (# slice) (# i)).
    wp_pure ; first word.
    wp_auto.

    (* TODO: cleanup *)
    assert (sint.nat i < length vs)%nat as Hi2 by word.
    pose proof (lookup_lt_is_Some_2 vs (sint.nat i)).
    apply H in Hi2.
    unfold is_Some in Hi2.
    destruct Hi2.

    wp_apply (wp_load_slice_elem slice i vs DfracDiscarded x) ; first lia.
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
      iApply "Hyield".
      iFrame.
      iPureIntro.
      intuition.
      assert (sint.nat i >= length vs).
      {
        apply firstn_n_length.
        done.
      }
      lia.
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
        Search "take".
        assert (take (S (sint.nat i)) vs = take (sint.nat i) vs ++ [x]).
        {
          apply take_S_r.
          done.
        }
        rewrite H1.
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
  iApply "Hlimit".
  replace (sint.nat i) with (length vs) by word.
  - assert (take (length vs) vs = vs) by apply firstn_all.
    replace (take (length vs) vs) with vs.
    done.
Qed.
