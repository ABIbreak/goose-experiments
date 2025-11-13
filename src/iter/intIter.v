From sys_verif.program_proof Require Import prelude empty_ffi.
From New.proof Require Import std.
From New.generatedproof.sys_verif_code Require Import iterator.

Section proof.
Context `{hG: !heapGS Σ} `{!globalsGS Σ} {go_ctx: GoContext}.

#[global] Instance : IsPkgInit iterator := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf iterator := build_get_is_pkg_init_wf.

Definition is_intIter (intIter : func.t) (limit : w64) (P : w64 → iPropI Σ) Φ : iPropI Σ :=
  ∀ (yield : func.t), (
    "HP" :: P(W64 0) ∗
    "#Hyield" :: □(
      ∀ (i : w64),
      (⌜ 0 ≤ sint.Z i < sint.Z limit ⌝ ∗ P(i)) -∗
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

Lemma wp_intIter limit P Φ' :
  {{{ is_pkg_init iterator ∗ ⌜ 0 ≤ sint.Z limit ⌝ }}}
    @! iterator.intIter #limit
  {{{
    (f : func.t), RET #f; is_intIter f limit P Φ'
  }}}.
Proof.
  wp_start as "%Hlimit".
  rewrite -wp_fupd.
  wp_auto.
  iPersist "limit".
  iModIntro.
  iApply "HΦ".
  unfold is_intIter.
  iIntros (yield) "Hpre".
  iNamed "Hpre".
  wp_auto.
  iPersist "yield".
  iAssert (
    ∃ (i : w64),
    "%Hi" :: ⌜ 0 ≤ sint.Z i ≤ sint.Z limit ⌝ ∗
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
    iApply "Hlimit".
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
      "%Hfact" :: ⌜ fact (sint.nat n) < 2 ^ 32 ⌝ ∗
      "%Hn" :: ⌜ 0 ≤ sint.Z n ⌝    
  }}}
      @! iterator.factorial #n
  {{{ 
      (factorial : w64), RET #factorial; 
      ⌜ sint.Z factorial = fact (sint.nat n) ⌝ 
  }}}.
Proof.
  wp_start.
  iNamed "Hpre".
  wp_auto.
  wp_apply (
    wp_intIter
    n
    (
      λ i,
      "factorial" :: factorial_ptr ↦ W64 (fact (sint.nat i))
    )%I
    (factorial_ptr ↦ W64 (fact (sint.nat n)))
  ); [word|].
  iIntros (intIter_f) "HintIter".
  wp_auto.
  unfold is_intIter.
  wp_bind (#intIter_f (#_)).
  iApply (wp_wand with "[factorial HintIter]").
  {
    iApply "HintIter".
    iSplitL.
    {
      replace (sint.nat (W64 0)) with 0%nat by word.
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
        replace (sint.nat (word.add i (W64 1))) with (S (sint.nat i))%nat by word.
        replace (word.add i (W64 1)) with (W64 (S (sint.nat i))) by word.
        rewrite fact_S.
        pose proof fact_monotonic (S (sint.nat i)) (sint.nat n) as Hfact_monotonic.
        assert (S (sint.nat i) ≤ sint.nat n)%nat as Hmono by word.
        apply Hfact_monotonic in Hmono.
        assert (
          word.mul (W64 (fact (sint.nat i))) (W64 (S (sint.nat i))) = 
          W64 (S (sint.nat i) * fact (sint.nat i))%nat
        ) as Heq by word.
        rewrite Heq.
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