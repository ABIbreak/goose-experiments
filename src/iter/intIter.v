From sys_verif.program_proof Require Import prelude empty_ffi.
From New.proof Require Import std.
From New.generatedproof.sys_verif_code Require Import iterator.

(* TODO: what does the boilerplate below do? *)
Section proof.
Context `{hG: !heapGS Σ} `{!globalsGS Σ} {go_ctx: GoContext}.

#[global] Instance : IsPkgInit iterator := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf iterator := build_get_is_pkg_init_wf.

(* First draft at proving iterators, or higher order functions in general *)

(* Syntactically correct example
Lemma wp_test (s: loc) (x: w32) :
  {{{ is_pkg_init sync ∗ s ↦ x }}}
    semacquire #s
  {{{ (f: func.t), RET #f; {{{ True }}} #f #() {{{ RET #(); True }}} }}}.
*)

Lemma wp_intIter_0 (limit : w64) :
  {{{ is_pkg_init iterator }}}
    (* @! wraps the name, as seen in perennial/new/golang/theory/pkg.v *)
    @! iterator.intIter #limit
  {{{ (f : func.t), RET #f; True }}}.
Proof.
  wp_start.
  wp_alloc limit_l as "limit".
  wp_pures.
  iApply "HΦ".
  wp_pures.
  done.
Qed.

(* Second attempt at proving iterators, covering only safety *)

Lemma wp_intIter_1 (*P Q*) (limit : w64) (yield : func.t) :
  {{{
    is_pkg_init iterator ∗ 
    (* ⌜ int_lt #(W64 0) #limit = #true ⌝ ∗ *)
    ⌜ 0 <= uint.nat limit <= 2 ^ 64 - 1 ⌝ ∗
    ∀ i : w64, {{{ (*P*) True }}} #yield #i {{{ (b : bool), RET #b; (*Q*) True }}}
  }}}
    @! iterator.intIter #limit
  {{{ (f : func.t), RET #f; 
    {{{ True }}} #f #yield {{{ RET #(); True }}}
  }}}.
Proof.
  wp_start as "[%limit_bounds #Hyield]".
  wp_alloc limit_l as "limit".
  iPersist "limit".
  wp_pures.
  iApply "HΦ".
  wp_start.
  wp_pures.
  wp_alloc yield_l as "yield".
  wp_pures.
  wp_alloc i_l as "i".
  wp_auto.
  iAssert (
    ∃i : w64,
    i_l ↦ i ∗
    ⌜uint.nat i <= uint.nat limit ⌝
    )%I with "[i]" as "Hinv".
  { iFrame. word. }
  wp_for "Hinv".
  iDestruct "Hinv" as "[Hi %Hi_le]".
  wp_auto.
  wp_if_destruct.
  + wp_apply ("Hyield").
    iIntros.
    destruct b.
    - wp_pures.
      iApply wp_for_post_do.
      wp_auto.
      iFrame.
      word.
    - wp_pures.
      iApply wp_for_post_return.
      wp_pures.
      iApply "HΦ".
      done.
  + iApply "HΦ".
    done.
Qed.

Lemma wp_intIter_2 P Q (limit : w64) (yield : func.t) :
  {{{
    is_pkg_init iterator ∗
    "limit_bounds" :: ⌜ 0 <= uint.nat limit <= 2 ^ 64 - 1 ⌝ ∗
    ∀ i : w64, {{{ P }}} #yield #i {{{ (b : bool), RET #b; if b then P else Q }}}
  }}}
    @! iterator.intIter #limit
  {{{ (f : func.t), RET #f; 
    {{{ P }}} #f #yield {{{ RET #(); P ∨ Q }}}
  }}}.
Proof.
  wp_start as "[%limit_bounds #Hyield]".
  rewrite -wp_fupd.
  wp_auto.
  (* wp_auto. *)
  (* TODO: the limit hypothesis created by wp_auto cannot be persisted? "No matching clauses for match." *)
  (*wp_alloc limit_ptr as "limit".
  *)
  iPersist "limit".
  wp_pures.
  iApply "HΦ".
  iModIntro.
  wp_start.
  wp_auto.
  iAssert (
    ∃i : w64,
    i_ptr ↦ i ∗
    P ∗
    ⌜uint.nat i <= uint.nat limit ⌝
    )%I with "[Hpre i]" as "Hinv".
  { 
    iFrame.
    word. 
  }
  wp_for "Hinv".
  iDestruct "Hinv" as "[Hi [HP %Hi_le]]".
  wp_auto.
  wp_if_destruct.
  + wp_apply ("Hyield" with "HP").
    iIntros (b) "HP_or_Q".
    destruct b.
    - wp_auto.
      iApply wp_for_post_do.
      wp_auto.
      iFrame.
      word.
    - wp_auto.
      iApply wp_for_post_return.
      wp_auto.
      iApply "HΦ".
      iFrame.
  + iApply "HΦ".
    iFrame.
Qed.

(* NOTE: remember that =?, >=? are for booleans! *)

Fixpoint isAscii (vs : list w8) : bool :=
  match vs with
  | v :: vs' => ((uint.Z v) =? 0) && (uint.Z v >=? 0x80) && isAscii vs'
  | nil => true
  end.

Lemma wp_isAscii_0 (s : slice.t) (vs : list w8) :
  {{{
    is_pkg_init iterator ∗
    own_slice s DfracDiscarded vs
  }}}
    @! iterator.isAscii #s
  {{{
    (b : bool), RET #b; True (* ⌜ b = isAscii vs ⌝ *)
  }}}.
Proof.
  wp_start.
  wp_auto.
  wp_bind (# (func_callv iterator.intIter) (# (slice.len_f s))).
  wp_apply wp_intIter_1.
Admitted.

Definition what_is_a_hoare_triple P e Q Φ : iPropI Σ :=
  P -∗ (Q -∗ Φ) -∗ WP e {{ v, Φ }}.

Definition is_intIter (f : func.t) limit yield (P : w64 -> iPropI Σ) Φ : iPropI Σ :=
  P(W64(0)) -∗ 
  □(∀i, P(i) -∗ 
    WP @! yield #i {{ ok, if decide (ok = #true) then P(word.add i 1) else Φ}}) -∗
  (P(limit) -∗ Φ) -∗
  WP #f @! yield {{ v, Φ }}.

Lemma wp_intIter_3 limit yield P Φ':
  {{{ is_pkg_init iterator ∗ ⌜ 0 ≤ sint.Z limit ⌝ }}}
    @! iterator.intIter #limit
  {{{
    (f : func.t), RET #f; is_intIter f limit yield P Φ'
  }}}.
Proof.
  wp_start as "%Hlimit".
  rewrite -wp_fupd.
  wp_auto.
  iPersist "limit".
  iApply "HΦ".
  iModIntro.
  unfold is_intIter.
  iIntros "HP #Hyield HΦ".
  wp_auto.
  iAssert (
    ∃i : w64,
    i_ptr ↦ i ∗
    P(i) ∗
    ⌜sint.Z i <= sint.Z limit ⌝
    )%I with "[HP i]" as "Hinv".
  { 
    iFrame.
    word.
  }
  wp_for "Hinv".
  iDestruct "Hinv" as "[i [HP %Hi]]".
  wp_auto.
  wp_if_destruct.
  - wp_bind (# (func_callv yield) (# i)).
    iApply ("Hyield" with "HP").
    
    admit.
  - iApply "HΦ".
    assert (limit = i) by word.
    rewrite H.
    done.
Admitted.
  

(*  P(0) ∗ □(∀i : w64, P(#i) -∗ WP(#yield(#i), λ: ok, if ok then P(i + 1) else Φ)).*)
