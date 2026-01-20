From sys_verif.program_proof Require Import prelude empty_ffi.
From New.proof Require Import std.
From New.generatedproof.sys_verif_code Require Import iterator.

Section proof.
Context `{hG: !heapGS Σ} `{!globalsGS Σ} {go_ctx: GoContext}.

(* TODO: is it advisable to add the typeclasses for K and V into the context? *)
Context `{!Inhabited K} `{Countable K} `{!IntoVal K} `{!IntoValTyped K kt}.
Context `{!Inhabited V} `{!IntoVal V} `{!IntoValTyped V vt}.

Context `{Inhabited K} `{Inhabited V}.

#[global] Instance : IsPkgInit iterator := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf iterator := build_get_is_pkg_init_wf.

Lemma wp_inSlice slice (vs : list w64) (v : w64):
  {{{
    is_pkg_init iterator ∗
    "#Hslice" :: own_slice slice DfracDiscarded vs
  }}}
    @! iterator.inSlice #slice #v
  {{{
    (b : bool), RET #b; ⌜ b = bool_decide (v ∈ vs) ⌝
  }}}.
Proof.
  wp_start.
  iNamed "Hpre".
  wp_auto.
  iDestruct (own_slice_len with "Hslice") as "[%Hlength %Hslice_len]".
  iAssert (
    ∃ (i : w64) (j : w64) (v' : w64),
    "i" :: i_ptr ↦ i ∗
    "j" :: j_ptr ↦ j ∗
    "v" :: v_ptr ↦ v' ∗
    "%Hi" :: ⌜ 0 <= sint.Z i <= length vs ⌝ ∗
    "%Hv_not_In" :: ⌜ v ∉ firstn (sint.nat i) vs ⌝
  )%I with "[i j v]" as "Hinv".
  {
    iExists (W64 0).
    iFrame ; iPureIntro ; split ; simpl.
    - word.
    - rewrite firstn_0.
      apply not_elem_of_nil.
  }
  wp_for "Hinv".
  wp_if_destruct.
  2: {
    iApply "HΦ".
    iPureIntro.
    rewrite bool_decide_eq_false_2 ; last reflexivity.
    replace (take _ _) with vs in Hv_not_In.
    {
      exact Hv_not_In.
    }
    symmetry.
    apply firstn_all2.
    word.
  }
  wp_pure ; first word.
  wp_apply (wp_load_slice_elem slice i vs DfracDiscarded (vs !!! sint.nat i)) ; first word.
  {
    iSplitL.
    - done.
    - iPureIntro. 
      apply list_lookup_lookup_total_lt.
      word.
  }
  iIntros "_".
  wp_auto.
  wp_if_destruct.
  {
    wp_for_post.
    iApply "HΦ".
    rewrite bool_decide_eq_true_2 ; last done.
    apply list_elem_of_lookup_total_2.
    word.
  }
  wp_for_post.
  iFrame.
  iSplitL ; iPureIntro.
  - word.
  - replace (take _ _) with ((take (sint.nat i) vs) ++ [(vs !!! (sint.nat i))]).
    2: {
      replace (sint.nat (word.add _ _)) with (S (sint.nat i)) by word.
      symmetry.
      apply take_S_r.
      apply list_lookup_lookup_total_lt.
      word.
    }
    apply not_elem_of_app.
    split.
    + exact Hv_not_In.
    + unfold not.
      intros Hv_vs.
      unfold not in n.
      apply n.
      symmetry.
      apply list_elem_of_singleton.
      exact Hv_vs.
Qed.

Definition is_mapIter (mapIter : func.t) (m : gmap K V) : iPropI Σ :=
  ∀ (P : gmap K V → iPropI Σ) (Φ : iProp Σ) (yield : func.t), (
    "HP" :: P(∅) ∗
    "#Hyield" :: □(
      ∀ (k : K) (v : V) (sm : gmap K V),
        (⌜ k ∉ dom sm ∧ (<[ k := v ]> sm) ⊆ m ⌝ ∗ P(sm)) -∗
        WP #yield #k #v {{
          ok,
          if (decide (ok = #true)) then
            P(<[ k := v ]> sm)
          else if (decide (ok = #false)) then
            Φ
          else
            False
        }}
    ) ∗
    "Htrace" :: (P(m) -∗ Φ)
  )%I -∗
  WP #mapIter #yield {{ _, Φ }}.

Axiom wp_map_for_range :
  ∀ mref (m : gmap K V) (body : func.t) dq (Φ: val → iProp Σ),
  own_map mref dq m ∗
  (∀ keys_sl keys,
     ⌜ list_to_set keys = dom m ∧ length keys = size m ∧ NoDup keys ⌝ ∗
     own_slice keys_sl DfracDiscarded keys -∗
      WP slice.for_range (#kt) (#keys_sl) (
          λ: <> "k"%string,
          let: "kv"%string := (map.get (#mref) "k"%string) in
          let: "v"%string := Fst "kv"%string in 
          #body "k"%string ("v"%string)
      )%E {{ v, own_map mref dq m ∗ Φ v ∗
        if (decide (v = execute_val)) then
          True
        else if (decide (v = return_val #())) then
          True
        else
          False 
      }} (* TODO: doesn't account for early termination *)
  ) -∗ 
  WP map.for_range #mref #body {{ 
    v, 
    Φ v ∗
    if (decide (v = execute_val)) then
      True
    else if (decide (v = return_val #())) then
      True
    else
      False
  }}.

(* TODO: what amount of ownership should be given to the iterator? (mirroring concerns about slice iterator) *)
Lemma wp_mapIter mref (m : gmap K V):
  {{{
    is_pkg_init iterator ∗
    "#Hmap" :: own_map mref DfracDiscarded m
  }}}
    @! iterator.mapIter #kt #vt #mref
  {{{ (f : func.t), RET #f; is_mapIter f m }}}.
Proof using Inhabited0 Inhabited1 H0 H1. (* TODO: why are these necessary? *)
  wp_start.
  iNamed "Hpre".
  wp_auto.
  iApply "HΦ".
  clear Φ.
  unfold is_mapIter.
  iIntros (P Φ yield) "Hpre".
  iNamed "Hpre".
  wp_auto.
  iPersist "m".
  wp_bind (map.for_range _ _).
  iApply (wp_wand with "[HP Htrace yield k v]").
  {
    iApply (wp_map_for_range mref m _ DfracDiscarded 
    (λ v, 
      if (decide (v = execute_val)) then
        Φ
      else if (decide (v = return_val #())) then
        Φ
      else
        ⌜ False ⌝%I
    )).
    iSplitR ; first done.
    iIntros (keys_sl keys) "[%Hpure #Hkeys]".
    iDestruct (own_slice_len with "Hkeys") as "[%Hlength %Hslice_len]".
    destruct Hpure as [Hkeys_m [Hkeys_m_card Hno_dup]].
    wp_auto.
    iAssert (
      ∃(k : K)(v : V)(i : w64)(sm : gmap K V),
      "k" :: k_ptr ↦ k ∗
      "v" :: v_ptr ↦ v ∗
      "i" :: i_ptr ↦ i ∗
      "HP" :: P(sm) ∗
      "%Hsm" :: ⌜ ∅ ⊆ sm ⊆ m ⌝ ∗
      "%Hsm_card" :: ⌜ sint.nat i = size sm ⌝ ∗
      "%Hsm_dom" :: ⌜ list_to_set (firstn (sint.nat i) keys) = dom sm ⌝ ∗
      "%Hi" :: ⌜ 0 ≤ sint.Z i ≤ size m ⌝
    )%I with "[k v i HP]" as "Hinv".
    {
      iExists (default_val K), (default_val V), (W64 0), ∅.
      iFrame.
      repeat iSplitL ; iPureIntro.
      - set_solver.
      - apply map_empty_subseteq.
      - set_solver.
      - set_solver.
      - word.
      - word.
    }
    wp_for "Hinv".
    wp_if_destruct.
    2: {
      iSplitR ; first done.
      iSplitL.
      2: {
        destruct (decide _) ; done.
      }
      destruct (decide _).
      2 : {
        destruct (decide _) ; done.
      }
      iApply "Htrace".
      enough (sm = m).
      {
        subst.
        iFrame.
      }
      apply map_subseteq_size_eq ; [set_solver | lia].
    }
    wp_pure ; first word.
    wp_apply (wp_load_slice_elem _ _ _ _ (keys !!! sint.nat i)) ; first word.
    {
      iSplitL ; first done.
      iPureIntro.
      rewrite list_lookup_lookup_total_lt ; first word.
      done.
    }
    iIntros "_".
    wp_auto.
    wp_apply wp_map_get ; first done.
    iIntros "_".
    wp_auto.
    wp_bind (#yield _ _).
    assert (m !! (keys !!! sint.nat i) = Some (m !!! (keys !!! sint.nat i))) as Hm_lookup_Some.
    {
      rewrite lookup_lookup_total_dom ; last done.
      rewrite <- Hkeys_m.
      rewrite elem_of_list_to_set.
      apply list_elem_of_lookup_total_2.
      word.
    }
    rewrite Hm_lookup_Some.
    simpl.
    assert (take (S (sint.nat i)) keys = take (sint.nat i) keys ++ [keys !!! (sint.nat i)]) as Htake_S.
    {
      apply take_S_r.
      apply list_lookup_lookup_total_lt.
      word.
    }
    (* This should be generalized into its own lemma after replace dom sm, but my attempts were unsuccessful *)
    assert (keys !!! sint.nat i ∉ dom sm) as Hkeys_not_elem_of.
    {
      rewrite <- Hsm_dom.
      apply not_elem_of_list_to_set.

      assert (NoDup (firstn (S (sint.nat i)) keys)) as Hfirstn_keys_NoDup.
      {
        pose proof (sublist_take keys (S (sint.nat i))).
        apply (sublist_NoDup _ keys) ; done.
      }
      rewrite Htake_S in Hfirstn_keys_NoDup.
      apply NoDup_ListNoDup in Hfirstn_keys_NoDup.
      apply NoDup_remove in Hfirstn_keys_NoDup as [_ Hnot_In].

      unfold not.
      intros Hkeys_dom.
      apply Hnot_In.
      rewrite app_nil_r.
      apply list_elem_of_In.
      done.
    }
    iApply (wp_wand with "[HP]").
    {
      wp_apply ("Hyield" $! _ _ sm).
      iFrame.
      iPureIntro.
      split; first done.
      apply insert_subseteq_l ; last set_solver.
      apply lookup_lookup_total_dom.
      rewrite <- Hkeys_m.
      apply elem_of_list_to_set.
      apply list_elem_of_lookup_total_2.
      word.
    }
    iIntros (?).
    destruct (decide _).
    {
      iIntros "HP".
      subst.
      wp_auto.
      wp_for_post.
      iFrame.
      repeat iSplitL; iPureIntro.
      - apply map_empty_subseteq.
      - apply insert_subseteq_l ; last set_solver.
        exact Hm_lookup_Some.
      - rewrite map_size_insert.
        assert (sm !! (keys !!! sint.nat i) = None) as Hsm_lookup_none.
        {
          apply not_elem_of_dom.
          done.
        }
        rewrite Hsm_lookup_none.
        word.
      - rewrite dom_insert_L.
        replace (sint.nat (word.add _ _)) with (S (sint.nat i)) by word.
        rewrite Htake_S.
        set_solver.
      - word.
      - word.
    }
    destruct (decide _).
    {
      iIntros "HΦ".
      subst.
      wp_auto.
      wp_for_post.
      iFrame "#∗".
      destruct (decide _) ; iFrame.
      destruct (decide _) ; iFrame.
      done.
    }
    iIntros "?".
    done.
  }
  iIntros (v0) "[HΦ ?]".
  destruct (decide _).
  {
    subst.
    wp_auto.
    done.
  }
  destruct (decide _) ; last done.
  subst.
  wp_auto.
  done.
Qed.

(* TODO: tried to give this a proof in Perennial, countered by lack of map.for_range spec *)
Axiom wp_map_len : ∀ l (m : gmap K V) dq,
  {{{ l ↦${dq} m }}}
    map.len #l
  {{{ (s : w64), RET #s; ⌜ sint.Z s = size m ⌝ ∗ l ↦${dq} m }}}.

(* TODO: is this axiom sane? *)
Axiom wp_interface_eq : ∀ (v1 v2 : V),
  True -∗
  WP interface.eq #v1 #v2 {{ b, ⌜ b = #(bool_decide (v1 = v2)) ⌝ }}.

Lemma wp_MapDeepEqual mref1 (m1 : gmap K V) mref2 (m2 : gmap K V) :
  {{{
    is_pkg_init iterator ∗
    "#Hmap1" :: own_map mref1 DfracDiscarded m1 ∗
    "#Hmap2" :: own_map mref2 DfracDiscarded m2
  }}}
    @! iterator.mapDeepEqual #kt #vt #mref1 #mref2
  {{{
    (b : bool), RET #b; ⌜ b = bool_decide (m1 = m2) ⌝
  }}}.
Proof using Inhabited0 Inhabited1 H0 H1.
  wp_start.
  iNamed "Hpre".
  wp_auto.
  iPersist "m1 m2".
  wp_apply (wp_map_len _ m1) ; first done.
  iIntros (s1) "[%Hs1 _]".
  wp_auto.
  wp_apply (wp_map_len _ m2) ; first done.
  iIntros (s2) "[%Hs2 _]".
  wp_auto.
  wp_if_destruct.
  2 : {
    iApply "HΦ".
    iPureIntro.
    rewrite bool_decide_eq_false_2.
    {
      unfold not.
      intros Heq.
      apply n.
      rewrite Heq in Hs1.
      rewrite <- Hs1 in Hs2.
      word.
    }
    done.
  }
  wp_apply (wp_mapIter mref1 m1) ; first done.
  iIntros (f) "HmapIter".
  wp_auto.
  unfold is_mapIter.
  wp_bind (#f _).
  iApply (wp_wand with "[ret_val HmapIter]").
  {
    iApply (
      "HmapIter" $!
      (λ m, ret_val_ptr ↦ bool_decide (m ⊆ m2))%I
      (ret_val_ptr ↦ bool_decide (m1 = m2))%I
    ).
    iSplitL.
    {
      rewrite bool_decide_eq_true_2 ; [apply map_empty_subseteq | done].
    }
    iSplitR.
    {
      iModIntro.
      iIntros (k v sm) "[%Hpure ret_val]".
      destruct Hpure as [Hk_not_elem_of_sm Hsm_insert_le_m1].
      wp_auto.
      wp_apply wp_map_get ; first done.
      iIntros "_".
      wp_auto.
      wp_if_destruct.
      {
        wp_if_destruct.
        - replace (m2 !! k) with (Some v).
          2 : {
            symmetry.
            apply (lookup_weaken (<[ k := v]> sm)) ; last done.
            apply lookup_insert_eq.
          }
          simpl.
          wp_bind (interface.eq _ _).
          iApply wp_wand.
          {
            iApply wp_interface_eq.
            done.
          }
          iIntros (b) "%Hb".
          subst.
          rewrite bool_decide_eq_true_2.
          {
            apply map_subseteq_spec.
            intros ? ? Hlookup.
            apply (lookup_weaken (<[ k := v]> sm)) ; last done.
            apply lookup_insert_Some.
            right.
            split ; last done.
            unfold not.
            intros Heq.
            apply Hk_not_elem_of_sm.
            rewrite <- Heq in Hlookup.
            apply (elem_of_dom_2 _ _ x).
            done.
          }
          rewrite bool_decide_eq_true_2 ; first done.
          wp_auto.
          destruct (decide _) ; first done.
          destruct (decide _).
          {
            apply (inj to_val) in e.
            discriminate.
          }
          iPureIntro.
          apply n.
          reflexivity.
        - unfold is_Some in i.
          destruct i as [v' Hm2_lookup_k].
          rewrite Hm2_lookup_k.
          simpl.
          wp_bind (interface.eq _ _).
          iApply wp_wand.
          {
            iApply wp_interface_eq.
            done.
          }
          iIntros (b) "%Hb".
          case_bool_decide.
          + subst.
            wp_auto.
            destruct (decide _).
            {
              rewrite bool_decide_eq_false_2 ; last done.
              unfold not.
              intros Hsubset_eq.
              apply n.
              apply insert_subseteq_l ; done.
            }
            destruct (decide _).
            {
              apply (inj to_val) in e.
              discriminate.
            }
            iPureIntro.
            apply n0.
            done.
          + subst.
            wp_auto.
            destruct (decide _).
            {
              apply (inj to_val) in e.
              discriminate.
            }
            destruct (decide _).
            {
              rewrite bool_decide_eq_false_2 ; last done.
              unfold not.
              intros Heq.
              apply n.
              rewrite <- Heq.
              done.
            }
            iPureIntro.
            apply n1.
            reflexivity.
      }
      rewrite bool_decide_eq_false_2 ; last done.
      unfold not.
      intros Heq.
      apply n.
      rewrite <- Heq.
      apply (lookup_weaken_is_Some (<[ k := v]> sm)) ; last done.
      apply lookup_insert_is_Some.
      left.
      done.
    }
    iIntros "ret_val".
    rewrite Hs2 in Hs1.
    case_bool_decide.
    - assert (m1 = m2).
      {
        apply map_subseteq_size_eq ; [done | lia].
      }
      rewrite bool_decide_eq_true_2 ; done.
    - rewrite bool_decide_eq_false_2 ; [set_solver | done].
  }
  iIntros (?) "ret_val".
  wp_auto.
  iApply "HΦ".
  done.
Qed.

End proof.
