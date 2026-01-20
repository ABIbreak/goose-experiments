From sys_verif.program_proof Require Import prelude empty_ffi.
From New.proof Require Import std.
From New.generatedproof.sys_verif_code Require Import iterator.
From New.proof.github_com.goose_lang.goose.model.channel
  Require Import chan_au_base.
From New.proof.github_com.goose_lang.goose.model.channel.protocol
     Require Import base simple future spsc done dsp (* dsp_proofmode *) mpmc join handshake.
From New.golang.theory Require Import chan.

Section proof.
Context `{hG: !heapGS Σ} `{!globalsGS Σ} {go_ctx: GoContext}.

Context `{!IntoVal V} `{!IntoValTyped V vt}.
Context `{!chanG Σ V}.

#[global] Instance : IsPkgInit iterator := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf iterator := build_get_is_pkg_init_wf.

Definition is_chanIter (chanIter : func.t) : iPropI Σ :=
  ∀ (Inv : iPropI Σ) (P : V → iPropI Σ) (Φ : iPropI Σ) (yield : func.t), (
    "Hinv" :: Inv ∗
    "#Hyield" :: □(
      ∀ (v : V),
      Inv ∗ P(v) -∗
      WP #yield #v {{
        ok,
        if (decide (ok = #true)) then
          Inv
        else if (decide (ok = #false)) then
          Φ
        else
          False
      }}
    )∗
    "Htrace" (* TODO: misleading name *) :: (Inv -∗ Φ)
  )%I -∗
  WP #chanIter #yield {{ _, Φ }}.

Lemma wp_chanIter (ch : loc) (γ : chan_names) :
  {{{
    is_pkg_init iterator ∗
    "His_channel" :: is_channel ch γ ∗
    "Hown_channel" :: own_channel ch chan_rep.Idle γ
  }}}
    @! iterator.chanIter #vt #ch
  {{{ (f : func.t), RET #f; is_chanIter f }}}.
Proof.
  wp_start. iNamed "Hpre".
  wp_auto.
  iApply "HΦ".
  clear Φ.
  unfold is_chanIter.
  iIntros (? ? ? ?) "Hpre".
  iNamed "Hpre".
  wp_auto.
  unfold chan.for_range.
  wp_auto.
  (* TODO: clean this up :( )*)
  iPoseProof (start_simple ch γ P) as "Hsimple".
  iApply "Hsimple" in "His_channel".
  iApply "His_channel" in "Hown_channel".
  iMod "Hown_channel" as (γsimple) "[%Heq #His_simple]".
  iAssert (
    ∃(v : V),
    "Hinv" :: Inv ∗
    "v" :: v_ptr ↦ v
  )%I with "[Hinv v]" as "Hinv2" ; first iFrame.
  wp_for "Hinv2".
  wp_apply (wp_simple_receive with "[His_simple]") ; first done.
  iIntros (?) "HP".
  wp_auto.
  wp_bind (#yield _).
  iApply (wp_wand with "[Hinv HP]").
  {
    iApply "Hyield".
    iFrame.
  }
  iIntros (ok) "Hok".
  destruct (decide _).
  {
    subst.
    wp_auto.
    wp_for_post.
    iFrame.
  }
  destruct (decide _).
  {
    subst.
    wp_auto.
    wp_for_post.
    done.
  }
  done.
Qed.

Lemma wp_collectChannel (ch : loc) (γ : chan_names) (P : V → iPropI Σ) :
  {{{
    is_pkg_init iterator ∗
    "His_channel" :: is_channel ch γ ∗
    "Hown_channel" :: own_channel ch chan_rep.Idle γ
  }}}
    @! iterator.collectChannel #vt #ch
  {{{ 
    (s : slice.t), RET #s; 
    ∃ (trace : list V), own_slice s 1 trace ∗
    ([∗ list] k ↦ x ∈ trace, P x)
  }}}.
Proof.
  wp_start. iNamed "Hpre".
  wp_auto.
  wp_apply wp_slice_make2 ; first word.
  iIntros (?) "[Hsl Hsl_cap]".
  replace (sint.nat (W64 0)) with 0%nat by word.
  rewrite replicate_0.
  set (l := []).
  wp_auto.
  wp_apply (wp_chanIter with "[His_channel Hown_channel]") ; first iFrame.
  iIntros (?) "His_chanIter".
  wp_auto.
  unfold is_chanIter.
  wp_bind (#f _).
  iApply (wp_wand with "[s Hsl Hsl_cap His_chanIter]").
  {
    set Inv := (
      ∃ l trace, 
      "Htrace" :: ([∗ list] k ↦ x ∈ trace, P x) ∗ 
      "s" :: s_ptr ↦ l ∗
      "Hsl" :: l ↦* trace ∗
      "Hsl_cap" :: own_slice_cap V l (DfracOwn 1)
    )%I.
    wp_apply (
      "His_chanIter" $!
      Inv
      P
      Inv
    ).
    iSplitL "s Hsl Hsl_cap".
    {
      iExists sl.
      iExists [].
      subst l.
      iFrame.
      rewrite big_sepL_nil.
      done.
    }
    iSplitR.
    {
      iModIntro.
      iIntros (v) "[Hinv HP]".
      iNamed "Hinv".
      wp_auto.
      wp_apply wp_slice_literal.
      iIntros (lv) "Hlv".
      wp_auto.
      wp_apply (wp_slice_append with "[Hsl Hsl_cap Hlv]"); first iFrame.
      iIntros (?) "[Hs' [Hs'_cap Hlv]]".
      wp_auto.
      destruct (decide _).
      2: {
        iExFalso.
        iPureIntro.
        apply n.
        done.
      }
      iExists s'.
      iExists (trace0 ++ [v]).
      iFrame.
      rewrite big_sepL_nil.
      done.
    }
    iIntros "Hinv".
    iNamed "Hinv".
    iExists l0.
    iExists trace0.
    iFrame.
  }
  iIntros (v) "Hinv".
  iNamed "Hinv".
  wp_auto.
  iApply "HΦ".
  iExists trace0.
  iFrame.
Qed.

End proof.