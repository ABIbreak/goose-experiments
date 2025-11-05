From sys_verif.program_proof Require Import prelude empty_ffi.
From New.proof Require Import std.
From New.generatedproof.sys_verif_code Require Import iterator.

Section proof.
Context `{hG: !heapGS Σ} `{!globalsGS Σ} {go_ctx: GoContext}.

#[global] Instance : IsPkgInit iterator := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf iterator := build_get_is_pkg_init_wf.

Definition is_intIter (intIter yield : func.t) (limit : w64) (P : w64 → iPropI Σ) Φ : iPropI Σ :=
  (
    if (decide (limit = (W64 0))) then
      Φ
    else
      "HP" :: P(W64 0) ∗
      "#Hyield" :: □(
        ∀ (i : w64),
          (⌜ 0 ≤ uint.nat i < uint.nat limit ⌝ ∗ P(i)) -∗
          WP #yield #i {{
            ok,
            if (decide (ok = #true)) then
              P(word.add i (W64 1))
            else if (decide (ok = #false)) then
              Φ
            else
              False
          }}
      ) ∗
      "Hlimit" :: (P(limit) -∗ Φ)
  )%I -∗
  WP #intIter #yield {{
    _, Φ
  }}.

Lemma wp_intIter yield limit P Φ' :
  {{{ is_pkg_init iterator ∗ ⌜ 0 ≤ sint.Z limit ⌝ }}}
    @! iterator.intIter #limit
  {{{
    (f : func.t), RET #f; is_intIter f yield limit P Φ'
  }}}.
Proof.
  wp_start as "%Hlimit".
  rewrite -wp_fupd.
  wp_auto.
  iPersist "limit".
  iModIntro.
  iApply "HΦ".
  unfold is_intIter.
  destruct (decide _).
  {
    iIntros "HΦ'".
    wp_auto.
    wp_for.
    rewrite bool_decide_eq_false_2; [word|].
    wp_auto.
    done.
  }
  iIntros "[HP [#Hyield Himp]]".
  wp_auto.
  iPersist "yield".
  iAssert (
    ∃ (i : w64),
    "%Hi" :: ⌜ 0 ≤ uint.nat i ≤ uint.nat limit ⌝ ∗
    "Hi" :: i_ptr ↦ i ∗
    "HP" :: P(i)
  )%I with "[i HP]" as "Hinv".
  {
    iExists (W64 0).
    iFrame.
    word.
  }
  wp_for "Hinv".
  destruct (decide (i = limit)).
  {
    rewrite bool_decide_eq_false_2 ; [word|].
    wp_auto.
    subst.
    iApply "Himp".
    done.
  }
  rewrite bool_decide_eq_true_2 ; [word|].
  wp_auto.
  wp_bind (#yield (#i)).
  iApply (wp_wand with "[HP]").
  {
    iApply "Hyield".
    iSplitR ; [word|done].
  }
  iIntros (ok) "Hpost".
  destruct (decide _).
  {
    subst.
    wp_auto.
    wp_for_post.
    iFrame.
    word.
  }
  destruct (decide _).
  {
    subst.
    wp_auto.
    wp_for_post.
    iFrame.
  }
  done.
Qed.

Lemma fact_monotonic (n m: nat) :
  (n ≤ m)%nat →
  (fact n ≤ fact m)%nat.
Proof.
  (* this is already in the standard library *)
  apply Coq.Arith.Factorial.fact_le.
Qed.

Lemma fact_S (n: nat) :
  fact (S n) = ((S n) * fact n)%nat.
Proof.
  (* this follows from the definition itself *)
  reflexivity.
Qed.

Lemma wp_factorial (n : w64) :
  {{{ is_pkg_init iterator ∗ 
      "%Hfact" :: ⌜ fact (uint.nat n) < 2 ^ 64 ⌝ ∗
      "%Hn" :: ⌜ 0 ≤ sint.Z n ⌝    
  }}}
      @! iterator.factorial #n
  {{{ 
      (factorial : w64), RET #factorial; 
      ⌜ uint.nat factorial = fact (uint.nat n) ⌝ 
  }}}.
Proof.
  wp_start.
  iNamed "Hpre".
  wp_auto.
  set (loop_body := func.mk _ _ _).
  wp_apply (
    wp_intIter
    loop_body
    n
    (
      λ i,
      "factorial" :: factorial_ptr ↦ W64 (fact (uint.nat i))
    )%I
    (factorial_ptr ↦ W64 (fact (uint.nat n)))    
  ); [word|].
  iIntros (intIter_f) "HintIter".
  wp_auto.
  unfold is_intIter.
  wp_bind (#intIter_f (#loop_body)).
  iApply (wp_wand with "[factorial HintIter]").
  {
    iApply "HintIter".
    destruct (decide _).
    {
      subst.
      replace (uint.nat (W64 0)) with 0%nat by word.
      simpl.
      done.
    }
    iSplitL.
    {
      replace (uint.nat (W64 0)) with 0%nat by word.
      simpl.
      done.
    }
    iSplitL.
    {
      iModIntro.
      iIntros (i) "[%Hi Hinv]".
      iNamed "Hinv".
      wp_auto.
      destruct (decide _).
      {
        replace (uint.nat (word.add i (W64 1))) with (S (uint.nat i))%nat by word.
        replace (word.add i (W64 1)) with (W64 (S (uint.nat i))) by word.
        rewrite fact_S.
        pose proof fact_monotonic (S (uint.nat i)) (uint.nat n) as Hfact_monotonic.
        assert (S (uint.nat i) ≤ uint.nat n)%nat as Hmono by word.
        apply Hfact_monotonic in Hmono.
        assert (
          word.mul (W64 (fact (uint.nat i))) (W64 (S (uint.nat i))) = 
          W64 (S (uint.nat i) * fact (uint.nat i))%nat
        ) by word.
        rewrite H.
        done.
      }
      done.
    }
    iIntros "?".
    done.
  }
  iIntros (?) "?".
  wp_auto.
  iApply "HΦ".
  word.
Qed.

End proof.