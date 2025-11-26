From sys_verif.program_proof Require Import prelude empty_ffi.
From New.proof Require Import std.
From New.generatedproof.sys_verif_code Require Import iterator.

Section proof.
Context `{hG: !heapGS Σ} `{!globalsGS Σ} {go_ctx: GoContext}.

#[global] Instance : IsPkgInit iterator := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf iterator := build_get_is_pkg_init_wf.

Definition is_mapIter `{Countable K} `{!IntoVal K} `{!IntoVal V} (mapIter : func.t)
    (m : gmap K V) (P : gmap K V → iPropI Σ) Φ : iPropI Σ :=
  ∀ (yield : func.t), (
    "HP" :: P(∅) ∗
    "#Hyield" :: □(
      ∀ (k : K) (v : V) (sm : gmap K V),
        (⌜ (<[ k := v ]> sm) ⊆ m ⌝ ∗ P(sm)) -∗
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

Lemma wp_mapIter `{Countable K} `{!IntoVal K} `{!IntoValTyped K kt} `{!IntoVal V} `{!IntoValTyped V vt} 
    mref (m : gmap K V) P Φ' :
  {{{
    is_pkg_init iterator ∗
    "#Hmap" :: own_map mref DfracDiscarded m
  }}}
    @! iterator.mapIter #kt #vt #mref
  {{{ (f : func.t), RET #f; is_mapIter f m P Φ' }}}.
Proof.
Admitted.
