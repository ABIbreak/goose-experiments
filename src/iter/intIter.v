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
  (* the limit hypothesis created by wp_auto cannot be persisted? "No matching clauses for match." *)
  (* solve ^ by doing a "rewrite -wp_fupd." beforehand *)
  (*wp_alloc limit_ptr as "limit".*)
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
Definition isAscii (vs : list w8) : bool :=
  bool_decide (Forall (λ c, (uint.Z c = 0) ∧ (uint.Z c >= 0x80)) vs).

Fixpoint isAscii_1 (vs : list w8) : bool :=
  match vs with
  | v :: vs' => ((uint.Z v) =? 0) && (uint.Z v >=? 0x80) && isAscii_1 vs'
  | nil => true
  end.

Lemma asdf (vs : list w8) :
  isAscii vs = isAscii_1 vs.
Proof.
  induction vs as [|v vs' iHvs].
  - done.
  - simpl.
    unfold isAscii.
    (*
    apply (Forall_cons_2 (λ c : w8_word_instance, uint.Z c = 0 ∧ uint.Z c >= 128) v vs').
    Search "Forall".
    Check Forall_inv.
    *)
    admit.
Admitted.

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
Admitted.

Definition what_is_a_hoare_triple P e Q Φ : iPropI Σ :=
  P -∗ (Q -∗ Φ) -∗ WP e {{ v, Φ }}.

Definition is_intIter_0 (f yield : func.t) limit (P : w64 → iPropI Σ) Φ : iPropI Σ :=
  (if (decide ((W64 0) = limit)) then Φ else 
  (P(W64(0)) ∗ 
  □(∀i, P(i) -∗ 
    WP #yield #i {{ ok, if (decide (ok = #true ∧ sint.Z i + 1 < sint.Z limit)) then 
                          P(word.add i 1) 
                        (* TODO: >= works but ≥ errors due to expecting a nat? *)
                        else if (decide (ok = #true ∧ sint.Z i + 1 >= sint.Z limit)) then
                          Φ
                        else if (decide (ok = #false)) then 
                          Φ
                        else
                          False
                    }}) ∗
  (P(limit) -∗ Φ))%I) -∗
  WP #f #yield {{ (* TODO: remove v, its kind of misleading? *) v, Φ }}.

Lemma wp_intIter_3 yield limit P Φ':
  {{{ is_pkg_init iterator ∗ ⌜ 0 ≤ sint.Z limit ⌝ }}}
    @! iterator.intIter #limit
  {{{
    (f : func.t), RET #f; is_intIter_0 f yield limit P Φ'
  }}}.
Proof.
  wp_start as "%Hlimit".
  rewrite -wp_fupd.
  wp_auto.
  iPersist "limit".
  iApply "HΦ".
  iModIntro.
  unfold is_intIter_0.
  destruct (decide _).
  - iIntros "?".
    wp_auto.
    wp_for.
    subst.
    wp_if_destruct.
    + discriminate.
    + done.
  - iIntros "[HP [#Hyield HΦ]]".
    wp_auto.
    iAssert (
      ∃i : w64,
      i_ptr ↦ i ∗
      P(i) ∗
      ⌜sint.Z i <= sint.Z limit ⌝
      )%I with "[HP i]" as "Hinv".
    { iFrame. word. }
    wp_for "Hinv".
    iDestruct "Hinv" as "[i [HP %Hi]]".
    wp_auto.
    wp_if_destruct.
    + wp_bind (#yield (# i)).
      iApply (wp_wand with "[HP]").
      { iApply ("Hyield" with "HP"). }
      simpl.
      iIntros (ok) "Hpost".
      destruct (decide _).
  (*      * destruct a as [c d]. (* TODO: rename this with better names*)
        subst.
        wp_auto.
        iApply wp_for_post_do.
        wp_auto.
        iFrame.
        word.
      * destruct (decide _).
        -- destruct a as [c d].
          subst.
          wp_auto.
          iApply wp_for_post_do.
          wp_auto.
          iSplitL "HΦ".
          ++ done.
          ++ 
          iApply "HΦ".
          iFrame.
          word.
      
      + intuition.



  - wp_bind ( #yield (# i)).
    (* If (wp_wand with "HP") doesn't work, try (wp_wand with "[HP]")*)
    iApply (wp_wand with "[HP]").
    { iApply ("Hyield" with "HP"). }
    simpl.
    iIntros (v) "Hpost".
    destruct (decide _).
    + subst.
      wp_auto.
      iApply wp_for_post_do.
      wp_auto.
      iFrame.
      word.
    + destruct (decide _).
      * subst.
        wp_auto.
        iApply wp_for_post_return.
        wp_auto.
        iFrame.
      * by iExFalso.
  - iApply "HΦ".
    assert (limit = i) by word.
    rewrite H.
    done.
  Qed.
  *)
Admitted.

Lemma wp_isAscii_1 (s : slice.t) (vs : list w8) :
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
  iPersist "Hpre" as "Hs".
  wp_auto.
  iPersist "str".

  (* TODO: is this an idiomatic way of "naming" anonymous functions? *)
  (* TODO: please tell me there's another way of going about this other than yeeting the entire function in here :sob: *)
  iAssert (
    ∃yield : func.t,
    loop_body_ptr ↦ yield ∗
    ⌜ yield = {|
      func.f := <>;
      func.x := "i";
      func.e :=
      exception_do
      (let: "i" := alloc "i" in
      (if: if: ![# byteT] (slice.elem_ref (# byteT)
      ![# sliceT] (# str_ptr) ![# intT] "i")
      ≥ # (W8 128) then # true
      else ![# byteT] (slice.elem_ref (# byteT)
      ![# sliceT] (# str_ptr) ![# intT] "i") =
      # (W8 0)
      then let: "$r0" := # false in
      (do: # ret_val_ptr <-[# boolT] "$r0") ;;;
      return: # false else do: # ()) ;;;
      let: "$r0" := # true in
      (do: # ret_val_ptr <-[# boolT] "$r0") ;;;
      return: # true)%E
    |} ⌝
    (* Yet another instance of "put the hypothesis, in the list" *)
  )%I with "[loop_body]" as (yield) "[loop_body %Hyield]".
  {
    iFrame.
    iPureIntro.
    (* TODO: resolve, reflexivity doesn't work *)
    admit.
  }

  iPoseProof (own_slice_len with "Hs") as "[%Hs_eq_vs %Hs_len]".
  wp_apply (wp_intIter_3
    yield
    (slice.len_f s) 
    (λ i, (
      ret_val_ptr ↦ isAscii (firstn (sint.nat i) vs) ∗
      ⌜ 0 ≤ sint.Z i < sint.Z (slice.len_f s) ⌝
    )%I)
    (ret_val_ptr ↦ isAscii vs)%I
  ).
  { word. }
  iIntros (f) "HintIter".
  wp_auto.
  iUnfold is_intIter_0 in "HintIter".
  wp_bind (# f (# yield)).
  iApply (wp_wand with "[HintIter loop_body ret_val]").
  (*{
    iApply ("HintIter" with "[ret_val][][]").
    - replace (sint.nat (W64 0)) with 0%nat by word.
      rewrite firstn_0.
      iFrame.
      admit. (*
      iPureIntro.
      replace (sint.Z (W64 0)) with 0 by word.
      lia.*)
    - iModIntro.
      iIntros (i) "[Hpre %Hi]".
      rewrite Hyield.
      wp_auto.
      wp_apply (wp_load_slice_elem).
      wp_pure.
      { word. }

      wp_apply (wp_load_slice_elem).

      Search "slice".
      

      iPoseProof (own_slice_elem_acc (slice.len_f s) _ _ with "Hs") as "[as ad]".
      { done. }
      { 
        rewrite <- Hs_eq_vs.
        admit.
      }
       
      Search slice.elem_ref.
      Search "slice".
      Search "elem_ref".
    - rewrite <- Hs_eq_vs.
      rewrite firstn_all.
      iIntros "?".
      done.
  }
  iIntros (v) "_".
  wp_auto.
  iApply "HΦ".*)

Admitted.

Definition is_intIter_1 (f yield : func.t) limit (P : w64 → iPropI Σ) Φ : iPropI Σ :=
  (if (decide ((W64 0) = limit)) then Φ else 
  (P(W64(0)) ∗ 
  □(∀i, P(i) -∗ 
    WP #yield #i {{ ok, if (decide (ok = #true ∧ sint.Z i + 1 < sint.Z limit)) then 
                          P(word.add i 1) 
                        (* TODO: >= works but ≥ errors due to expecting a nat? *)
                        else if (decide (ok = #true ∧ sint.Z i + 1 >= sint.Z limit)) then
                          Φ
                        else if (decide (ok = #false)) then 
                          Φ
                        else
                          False
                    }}))%I) -∗
  WP #f #yield {{ (* TODO: remove v, its kind of misleading? *) v, Φ }}.

Lemma wp_intIter_4 yield limit P Φ':
  {{{ is_pkg_init iterator ∗ ⌜ 0 ≤ sint.Z limit ⌝ }}}
    @! iterator.intIter #limit
  {{{
    (f : func.t), RET #f; is_intIter_1 f yield limit P Φ'
  }}}.
Proof.
  wp_start as "%Hlimit".
  wp_auto.
  iApply "HΦ".
  unfold is_intIter_1.
  destruct (decide _).
  - iIntros "HΦ".
    wp_auto.
    wp_for.
    subst.
    rewrite bool_decide_eq_false_2.
    { word. }
    wp_auto.
    done.
  - iIntros "[HP #Hyield]".
    wp_auto.
    iAssert (
      ∃ i,
      ⌜ sint.Z i ≤ sint.Z limit ⌝ ∗
      i_ptr ↦ i ∗
      if decide (i = limit) then Φ' else P(i)
    )%I with "[HP i]" as "Hinv".
    {
      iExists (W64 0).
      replace (sint.Z (W64 0)) with 0%Z by word.
      destruct (decide _) ; [word | iFrame; word].
    }
    wp_for "Hinv".
    iDestruct "Hinv" as "[%i_le_limit [i HP]]".
    wp_auto.
    wp_if_destruct.
    + wp_bind (#yield (#i)).
      iApply (wp_wand with "[HP]").
      {
        assert (i ≠ limit) by word.
        destruct (decide _) ; [word |].
        iApply ("Hyield" with "HP").
      }
      iIntros (ok) "Hpost".
      destruct (decide _).
      * destruct a as [? ?].
        subst.
        wp_auto.
        iApply wp_for_post_do.
        wp_auto.
        iFrame.
        iSplitR ; [word|].
        destruct (decide _) ; [word|done].
      * destruct (decide _).
        -- destruct a as [? ?].
          subst.
          wp_auto.
          iApply wp_for_post_do.
          wp_auto.
          iFrame.
          assert (sint.Z i + 1 = sint.Z limit) by word.
          iSplitR.
          ++ word.
          ++ destruct (decide _) ; [done|word].
        -- destruct (decide _).
          ++ subst.
            wp_auto.
            iApply wp_for_post_return.
            wp_auto.
            done.
          ++ done.
    + assert (i = limit) by word.
      destruct (decide _).
      * done.
      * done.
Qed.

Lemma wp_isAscii_2 (s : slice.t) (vs : list w8) :
  {{{
    is_pkg_init iterator ∗
    own_slice s DfracDiscarded vs
  }}}
    @! iterator.isAscii #s
  {{{
    (b : bool), RET #b; ⌜ b = isAscii vs ⌝
  }}}.
Proof.
  wp_start.
  iPersist "Hpre" as "#Hs".
  wp_auto.
  set (loop_body:=func.mk _ _ _).
  wp_apply (
    wp_intIter_4 
    loop_body 
    (slice.len_f s) 
    (λ i, (
      ∃ head tail, 
      ⌜ vs = head ++ (nth (sint.nat i) vs _) :: tail ⌝ ∗
      ⌜ nth_ok (sint.nat i) vs _ = true ⌝ ∗
      ⌜ isAscii head = true ⌝ ∗ 
      ret_val_ptr ↦ true ∗
      ⌜ 0 ≤ sint.Z i < sint.Z (slice.len_f s) ⌝
    )%I)
    (ret_val_ptr ↦ isAscii vs)%I
  ).
  {
    iPoseProof (own_slice_len with "Hs") as "[_ ?]".
    done.
  }
  iIntros (iter) "HintIter".
  wp_auto.
  iPersist "str".
  unfold is_intIter_1.
  wp_bind (# iter (# loop_body)).
  iApply (wp_wand with "[ret_val HintIter]").
  {
    iApply "HintIter".
    iPoseProof (own_slice_len with "Hs") as "[%Hlen %Hlen_ge_0]".
    destruct (decide _).
    - replace (sint.nat (slice.len_f s)) with 0%nat in Hlen by word.
      assert (vs = []).
      { rewrite <- length_zero_iff_nil. done. }
      subst.
      iFrame.
    - iSplitL "ret_val".
      + iExists [].
        iExists (tl vs).
        iSplitR.
        {
          iPureIntro.
          replace (sint.nat (W64 0)) with 0%nat by word.
          simpl.
          assert (∀ default, (hd default vs) = (nth 0 vs default)).
          {
            intros default.
            destruct vs; trivial.
          }
          admit.
          (*
          apply list_lookup_total_middle.
          rewrite <-(list_lookup_total_middle _ _ 0%nat).
          simpl.
          
          Search (_ !!! _)"lookup".
          replace (vs !!! (0%nat)) with (hd vs).
          Search (_ !!! _ = _) "list".
          
          admit.
          *)
        }
        simpl.
        iFrame.
        admit.
        (* word. *)
      + iModIntro.
        admit.
        (*
        iIntros (i) "[%HisAscii [Hret_val %Hi]]".
        wp_auto.
        wp_apply (wp_load_slice_elem s i vs DfracDiscarded (vs !!! (sint.nat i))).
        { word. }
        { 
          iSplitR.
          - done.
          - iPureIntro.
            Search (_ !! _ = Some (_ !!! _)).
            assert (sint.nat i < length vs) by word.
            rewrite list_lookup_lookup_total_lt.
            { word. }
            reflexivity.
        }
        iIntros "_".
        wp_auto.
        wp_if_destruct.
        -- destruct (decide _).
          ++ destruct a as [? ?].
            apply (inj to_val) in H.
            discriminate.
          ++ destruct (decide _).
            ** destruct a as [? ?].
              apply (inj to_val) in H.
              discriminate.
            ** assert (isAscii vs = false) as Hnot_isAscii.
              {
                (* TODO: reword isAscii to be amenable to this kind of reasoning? *)
                admit.
              }
              rewrite Hnot_isAscii.
              iFrame.
        -- wp_apply (wp_load_slice_elem s i vs DfracDiscarded (vs !!! (sint.nat i))).
          { word. }
          { 
            iSplitR.
            - done.
            - iPureIntro.
              assert (sint.nat i < length vs) by word.
              rewrite list_lookup_lookup_total_lt.
              { word. }
              reflexivity.
          }
          iIntros.
          wp_auto.
          wp_if_destruct.
          ++ destruct (decide _).
            ** destruct a as [? ?].
              apply (inj to_val) in H.
              discriminate.
            ** destruct (decide _).
              --- destruct a as [? ?].
                apply (inj to_val) in H.
                discriminate.
              --- admit. (* TODO: another case of bad *)
          ++ destruct (decide _).
            ** destruct a as [? ?].
              iFrame.
              iSplitL ; [|word].
              iPureIntro.
              replace (sint.nat (word.add i (W64 1))) with (S (sint.nat i))%nat by word.
              Search "firstn".
              assert (∃v vs', vs = v::vs').
              {
                exists 
              }
              rewrite firstn_cons.
            ** destruct (decide _).
              --- admit.
              --- admit.   
              *)
  }
  iIntros (?) "asdf".
  wp_auto.
  iApply "HΦ".
  done.
Admitted.

Lemma wp_isAscii_3 (s : slice.t) (vs : list w8) :
  {{{
    is_pkg_init iterator ∗
    own_slice s DfracDiscarded vs
  }}}
    @! iterator.isAscii #s
  {{{
    (b : bool), RET #b; ⌜ b = isAscii vs ⌝
  }}}.
Proof.
  wp_start.
  iPersist "Hpre" as "#Hs".
  wp_auto.
  iAssert (
    ∃loop_body : func.t,
    loop_body_ptr ↦ loop_body ∗
    ⌜loop_body = 
      {|
      func.f := <>;
      func.x := "i";
      func.e :=
      exception_do
      (let: "i" := alloc "i" in
      (if: if: ![# byteT] (slice.elem_ref (# byteT)
      ![# sliceT] (# str_ptr) ![# intT] "i")
      ≥ # (W8 128) then # true
      else ![# byteT] (slice.elem_ref (# byteT)
      ![# sliceT] (# str_ptr) ![# intT] "i") =
      # (W8 0)
      then let: "$r0" := # false in
      (do: # ret_val_ptr <-[# boolT] "$r0") ;;;
      return: # false else do: # ()) ;;;
      let: "$r0" := # true in
      (do: # ret_val_ptr <-[# boolT] "$r0") ;;;
      return: # true)%E
    |}⌝
  )%I with "[loop_body]" as (loop_body) "[loop_body %Hloop_body]".
  { 
    iExists ({|
      func.f := <>;
      func.x := "i";
      func.e :=
      exception_do
      (let: "i" := alloc "i" in
      (if: if: ![# byteT] (slice.elem_ref (# byteT)
      ![# sliceT] (# str_ptr) ![# intT] "i")
      ≥ # (W8 128) then # true
      else ![# byteT] (slice.elem_ref (# byteT)
      ![# sliceT] (# str_ptr) ![# intT] "i") =
      # (W8 0)
      then let: "$r0" := # false in
      (do: # ret_val_ptr <-[# boolT] "$r0") ;;;
      return: # false else do: # ()) ;;;
      let: "$r0" := # true in
      (do: # ret_val_ptr <-[# boolT] "$r0") ;;;
      return: # true)%E
    |}).
    iFrame.
    iPureIntro.
    admit.
  }
  iPoseProof (own_slice_len with "Hs") as "[%Hlen %Hlen_ge_0]".
  wp_apply (
    wp_intIter_4 
    loop_body 
    (slice.len_f s) 
    (λ i, (
      ⌜ isAscii (firstn (sint.nat i) vs) ⌝ ∗
      ret_val_ptr ↦ true ∗
      ⌜ 0 ≤ sint.Z i < sint.Z (slice.len_f s) ⌝
    )%I)
    (ret_val_ptr ↦ isAscii vs)%I
  ); [iPureIntro; done |].
  iIntros (iter) "HintIter".
  wp_auto.
  iPersist "str".
  unfold is_intIter_1.
  wp_bind (# iter (# loop_body)).
  iApply (wp_wand with "[ret_val HintIter]").
  {
    iApply "HintIter".
    
    destruct (decide _).
    - replace (sint.nat (slice.len_f s)) with 0%nat in Hlen by word.
      assert (vs = []).
      { rewrite <- length_zero_iff_nil. done. }
      subst.
      iFrame.
    - iSplitL "ret_val".
      + rewrite firstn_0.
        simpl.
        iFrame.
        iPureIntro.
        word.
      + admit.
        (*
        iSplitL.
        * iModIntro.
          iIntros (i) "[%HisAscii [Hret_val %Hi]]".
          rewrite Hloop_body.
          wp_auto.
          wp_apply (wp_load_slice_elem s i vs DfracDiscarded (vs !!! (sint.nat i))).
          { word. }
          { 
            iSplitR.
            - done.
            - iPureIntro.
              Search (_ !! _ = Some (_ !!! _)).
              assert (sint.nat i < length vs) by word.
              rewrite list_lookup_lookup_total_lt; [word |].
              reflexivity.
          }
          iIntros "_".
          wp_auto.
          wp_if_destruct.
          -- destruct (decide _).
            ++ destruct a as [? ?].
              apply (inj to_val) in H.
              discriminate.
            ++ destruct (decide _).
              ** destruct a as [? ?].
                apply (inj to_val) in H.
                discriminate.
              ** assert (isAscii vs = false) as Hnot_isAscii.
                {
                  (* TODO: reword isAscii to be amenable to this kind of reasoning? *)
                  admit.
                }
                rewrite Hnot_isAscii.
                iFrame.
          -- wp_apply (wp_load_slice_elem s i vs DfracDiscarded (vs !!! (sint.nat i))).
            { word. }
            { 
              iSplitR.
              - done.
              - iPureIntro.
                assert (sint.nat i < length vs) by word.
                rewrite list_lookup_lookup_total_lt.
                { word. }
                reflexivity.
            }
            iIntros.
            wp_auto.
            wp_if_destruct.
            ++ destruct (decide _).
              ** destruct a as [? ?].
                apply (inj to_val) in H.
                discriminate.
              ** destruct (decide _).
                --- destruct a as [? ?].
                  apply (inj to_val) in H.
                  discriminate.
                --- admit. (* TODO: another case of bad *)
            ++ destruct (decide _).
              ** iFrame. 
                iSplitL; iPureIntro; [| word].
                admit.
              ** destruct (decide _).
                --- assert (isAscii vs = true).
                  {
                    assert (word.add i 1 = slice.len_f s) by word.
                    rewrite <- H in Hlen.
                    admit.
                    (*replace (sint.nat (word.add i (W64 1))) with ((sint.nat i) + 1) in Hlen by word.
                  *)
                  }
                  rewrite H.
                  done.
                --- iPureIntro.
                    exfalso.
                    assert ((False /\ False) -> False).
                    {
                      intros [? ?]. done.
                    }
                    apply H.
                    unfold not in n2.
                    unfold not in n3.
                    split.
                    +++ admit.
                    +++ admit.
        * rewrite <- Hlen.
          rewrite firstn_all.
          iIntros "[? [? %_]]".
          done.
        *)
  }
  (*
  iIntros (?) "asdf".
  wp_auto.
  iApply "HΦ".
  done.
  *)
Admitted.

Definition is_intIter_2 (intIter yield : func.t) (limit : w64) (P : w64 → iPropI Σ) Φ : iPropI Σ :=
  (
    if (decide (limit = (W64 0))) then 
      Φ 
    else
      (
        P(W64 0) ∗
        □(
          ∀ (i : w64), P(i) -∗ 
          WP #yield #i {{ 
            ok, 
            if decide (ok = #true ∧ uint.nat i + 1 < uint.nat limit) then
              P(uint.nat i + 1)
            else if decide (ok = #true ∧ uint.nat i + 1 = uint.nat limit) then
              Φ
            else if decide (ok = #false) then
              Φ
            else
              False
          }}
        )
      )%I
  ) -∗
  WP #intIter #yield {{
    _, Φ
  }}.

Lemma wp_intIter_5 yield limit P Φ':
  {{{ is_pkg_init iterator ∗ ⌜ 0 ≤ sint.Z limit ⌝ }}}
    @! iterator.intIter #limit
  {{{
    (f : func.t), RET #f; is_intIter_2 f yield limit P Φ'
  }}}.
Proof.
  wp_start as "%Hlimit".
  wp_auto.
  iApply "HΦ".
  unfold is_intIter_2.
  destruct (decide _).
  {
    iIntros "HΦ'".
    wp_auto.
    wp_for.
    subst.
    wp_if_destruct; [discriminate|done].
  }
  iIntros "[HP #Hyield]".
  wp_auto.
  iAssert (
    ∃ i,
    "%Hi" :: ⌜ sint.Z i ≤ sint.Z limit ⌝ ∗
    "i" :: i_ptr ↦ i ∗
    "Hpost" :: if decide (i = limit) then Φ' else P(i)
  )%I with "[HP i]" as "Hinv".
  {
    iExists (W64 0).
    replace (sint.Z (W64 0)) with 0%Z by word.
    destruct (decide _) ; [word | iFrame; word].
  }
  wp_for "Hinv".
  wp_if_destruct.
  - destruct (decide _).
    {
      assert (i ≠ limit) by word.
      done.
    }
    wp_bind (#yield (#i)).
    iApply (wp_wand with "[Hpost]").
    {
      iApply "Hyield".
      done.
    }
    iIntros (ok) "Hpost".
    destruct (decide _) as [[Hok Hi_inc] | ?].
    {
      subst.
      wp_auto.
      iApply wp_for_post_do.
      wp_auto.
      iFrame.
      iSplitR ; [word|].
      destruct (decide _) ; [word|].
      replace (W64 (uint.nat i + 1)) with (word.add i (W64 1)) by word.
      done.
    }
    destruct (decide _) as [[Hok Hi_inc] | ?].
    {
      subst.
      wp_auto.
      iApply wp_for_post_do.
      wp_auto.
      iFrame.
      iSplitR ; [word|].
      destruct (decide _) ; [done|].
      assert (i = limit) by word.
      word.
    }
    destruct (decide _) as [Hok | ?].
    {
      subst.
      wp_auto.
      iApply wp_for_post_return.
      wp_auto.
      done.
    }
    done.
  - assert (i = limit) by word.
    destruct (decide _) ; done.
Qed.

Lemma asdf0 (vs head tail : list w8) (elem : w8) :
  vs = head ++ elem :: tail -> 
  isAscii vs = isAscii head && isAscii [elem] && isAscii tail.
Proof.
  intros.
  induction head.
  - rewrite H.
    simpl.
    admit.
  - simpl.
Admitted.

Lemma wp_isAscii_4 (s : slice.t) (vs : list w8) :
  {{{
    is_pkg_init iterator ∗
    own_slice s DfracDiscarded vs
  }}}
    @! iterator.isAscii #s
  {{{
    (b : bool), RET #b; ⌜ b = isAscii vs ⌝
  }}}.
Proof.
  wp_start as "#s".
  wp_auto.
  iPersist "str".
  set (loop_body := func.mk _ _ _).
  iPoseProof (own_slice_len with "s") as "[%Hlen_eq %Hlen_ge_0]".
  wp_apply (
    wp_intIter_5
    loop_body 
    (slice.len_f s) 
    (λ i, (
      ∃ head tail, 
      "%Hvs" :: ⌜ vs = head ++ (nth (sint.nat i) vs (W8 23)) :: tail ⌝ ∗
      "%Hnth_ok" :: ⌜ nth_ok (sint.nat i) vs (W8 23) = true ⌝ ∗
      "%HisAscii" :: ⌜ isAscii head = true ⌝ ∗ 
      "ret_val" :: ret_val_ptr ↦ true ∗
      "%Hi" :: ⌜ 0 ≤ sint.Z i < sint.Z (slice.len_f s) ⌝
    )%I)
    (ret_val_ptr ↦ isAscii vs)%I
  ) ; [done|].
  iIntros (intIter) "HintIter".
  wp_auto.
  unfold is_intIter_2.
  destruct (decide _) as [Hlen | Hlen].
  {
    wp_bind (#intIter (#loop_body)).
    iApply (wp_wand with "[ret_val HintIter]").
    {
      iApply "HintIter".
      rewrite Hlen in Hlen_eq.
      replace (sint.nat (W64 0)) with 0%nat in Hlen_eq by word.
      rewrite length_zero_iff_nil in Hlen_eq.
      subst.
      done.
    }
    iIntros (?) "ret_val".
    wp_auto.
    iApply "HΦ".
    done.
  }
  assert (sint.nat (slice.len_f s) ≠ 0%nat) as Hslice_neq_nil by word.
  rewrite <- Hlen_eq in Hslice_neq_nil.
  case vs as [?|v vs'].
  {
    simpl in Hslice_neq_nil.
    done.
  }
  wp_bind (#intIter (#loop_body)).
  iApply (wp_wand with "[ret_val HintIter]").
  {
    iApply "HintIter".
    iSplitL.
    {
      iExists ([]).
      iExists (vs').
      iFrame.
      iPureIntro.
      repeat split ; word.
    }
    iModIntro.
    iIntros (i) "Hinv".
    iNamed "Hinv".
    wp_auto.
    wp_apply (
      wp_load_slice_elem s i (v :: vs') DfracDiscarded ((v :: vs') !!! (sint.nat i))
    ) ; [word| | ].
    {
      iSplitL ; [done|iPureIntro].
      apply list_lookup_lookup_total_lt.
      assert (sint.Z (slice.len_f s) = sint.nat (slice.len_f s)) as asdf by word.
      rewrite asdf in Hi.
      rewrite <- Hlen_eq in Hi.
      word.
    }
    (*TODO load once pleaseeeee*)
    iIntros "_".
    wp_auto.
    wp_if_destruct.
    - destruct (decide _) as [[? ?]|?].
      {
        apply (inj to_val) in H.
        discriminate.
      }
      destruct (decide _) as [[? ?]|?].
      {
        apply (inj to_val) in H.
        discriminate.
      }
      rewrite Hvs.
      Search "Forall".
      simpl.
      admit.
    - admit.
  }
  iIntros (?) "ret_val".
  wp_auto.
  iApply "HΦ".
  done.
Admitted.
