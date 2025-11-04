(*| # Assignment 3: verify factorial function

The code in
[go/functional/functional.go](https://github.com/tchajed/sys-verif-fa25-proofs/blob/main/go/functional/functional.go)
implements `func Factorial(n uint6) uint64`.

Here, you'll prove this function correct, proving that the imperative, loop-based
implementation Go is equivalent to a recursive, functional implementation in
Gallina.

Before starting, **you should read the [fibonacci
demo](/notes/program-proofs/demos/fibonacci_proof.md)**, which has a very similar
structure to this proof.

|*)
From sys_verif.program_proof Require Import prelude empty_ffi.
From sys_verif.program_proof Require Import functional_init.

Section proof.
Context `{hG: !heapGS Σ}.
Context `{!globalsGS Σ} {go_ctx: GoContext}.

(*| A functional implementation of the factorial function is already provided as
`fact` by the Coq standard library, which is what we'll use. It looks as you'd expect:

```rocq
Fixpoint fact (n: nat): nat :=
  match n with
  | 0%nat => 1%nat
  | S n' => (S n' * fact n')%nat
  end.
```

|*)

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

Lemma asdf (i : w64) :
  uint.Z i = uint.nat i.
Proof.
  assert (0 <= uint.nat i < 2 ^ 64) by admit.
  word.


(* You will need to use `rewrite word.unsigned_mul_nowrap` yourself in this
proof, which the `word` tactic will not (currently) do automatically. *)

Lemma wp_Factorial (n: w64) :
  {{{ is_pkg_init functional ∗ ⌜Z.of_nat (fact (uint.nat n)) < 2^64⌝ }}}
    @! functional.Factorial #n
  {{{ (c: w64), RET #c; ⌜uint.nat c = fact (uint.nat n)⌝ }}}.
Proof.
  wp_start as "%Hpre".
  wp_auto.
  iPersist "n".
  wp_if_destruct.
  - iApply "HΦ".
    replace (uint.nat (W64 0)) with 0%nat by word.
    simpl.
    word.
  - iAssert(
      ∃ (i fact_var : w64),
      "i" :: i_ptr ↦ i ∗
      "fact" :: fact_ptr ↦ fact_var ∗
      "%Hfact" :: ⌜ uint.Z fact_var = fact(uint.nat i) ⌝ ∗
      "%Hi_bound" :: ⌜ 0 <= uint.Z i <= uint.Z n ⌝
    )%I with "[i fact]" as "Hinv".
    {
      iExists (W64 0).
      iFrame.
      iPureIntro.
      split ; [|word].
      replace (uint.nat (W64 0)) with 0%nat by word.
      simpl.
      word.
    }
    wp_for "Hinv".
    wp_if_destruct.
    + iApply wp_for_post_do.
      wp_auto.
      iFrame.
      iSplitL; [|word].
      iPureIntro.

      rewrite word.unsigned_mul_nowrap.
      {
        rewrite Hfact.
        pose proof (fact_monotonic (S (uint.nat i)) (uint.nat n)) as Hi_n.
        rewrite fact_S in Hi_n.
        replace (uint.Z (word.add i (W64 1))) with (uint.Z i + 1) by word.
        word.
      }
      replace (uint.nat (word.add i (W64 1))) with (uint.nat i + 1)%nat by word.
      replace (uint.Z (word.add i (W64 1))) with (uint.Z i + 1) by word.
      rewrite Hfact.
      replace (uint.Z i + 1) with (uint.nat i + 1)%Z by word.
      replace (uint.nat i + 1)%Z with (1 + uint.nat i)%Z by word.
      symmetry.
      Check (uint.nat i + 1).
      replace (uint.nat i + 1)%nat with (S (uint.nat i)) by word.
      simpl.
      word.
    + iApply "HΦ".
      assert (i = n) by word.
      subst.
      iPureIntro.
      word.
Qed.

Lemma wp_Factorial_1 (n: w64) :
  {{{ is_pkg_init functional ∗ ⌜Z.of_nat (fact (uint.nat n)) < 2^64⌝ }}}
    @! functional.Factorial #n
  {{{ (c: w64), RET #c; ⌜uint.nat c = fact (uint.nat n)⌝ }}}.
Proof.
  wp_start as "%Hpre".
  wp_auto.
  iPersist "n".
  wp_if_destruct.
  - iApply "HΦ".
    replace (uint.nat (W64 0)) with 0%nat by word.
    simpl.
    word.
  - iAssert(
      ∃ (i fact_var : w64),
      "i" :: i_ptr ↦ i ∗
      "fact" :: fact_ptr ↦ fact_var ∗
      "%Hfact" :: ⌜ uint.nat fact_var = fact(uint.nat i) ⌝ ∗
      "%Hi_le_n" :: ⌜ uint.Z i <= uint.Z n ⌝
    )%I with "[i fact]" as "Hinv".
    {
      iExists (W64 0).
      iFrame.
      iPureIntro.
      split ; [|word].
      replace (uint.nat (W64 0)) with 0%nat by word.
      simpl.
      word.
    }
    wp_for "Hinv".
    wp_if_destruct.
    + iApply wp_for_post_do.
      wp_auto.
      iFrame.
      iSplitL; [|word].
      iPureIntro.
      Show Proof.
      replace (uint.nat (word.add i (W64 1))) with (S (uint.nat i)) by word.
      rewrite fact_S.
      rewrite <- Hfact.
      assert (uint.Z fact_var * S (uint.nat i) < 2 ^ 64).
      {
        pose proof (fact_monotonic (S (uint.nat i)) (uint.nat n)) as Hi_n.
        rewrite fact_S in Hi_n.
        word.
      }
      destruct (decide (uint.nat i > 0)).
      * word.
      * assert (i = 0) by word.
        word.
    + iApply "HΦ".
      assert (i = n) by word.
      subst.
      iPureIntro.
      word.
Qed.

End proof.
